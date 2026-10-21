#!/usr/bin/env python3
"""Serial, bounded measurements of unchanged GAP research functions (Linux).

Uses only Python's standard library. Captures outputs, wait4 resource usage,
and sampled process-group CPU/RSS; optional strace and GAP/KBMAG diagnostics
are labeled separately from uninstrumented baseline runs.
"""
import argparse
import ctypes
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
HISTORICAL = ["GL2Z", "SL2Z", "SL2F2", "SL2F3", "SL2F5", "SL2Zi",
              "SL2w", "SL2Zneg5", "PSL2Z"]
CASES = HISTORICAL + ["G3", "G5", "G7", "G11"]
SMALL = ["SL2F2", "SL2F3", "SL2F5"]


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def process_trace(path):
    """Elapsed exec-to-exit intervals, not CPU profiles of the C routines."""
    processes = {}
    if not path.exists():
        return []
    for line in path.read_text().splitlines():
        event = re.match(r"(\d+)\s+(\d+\.\d+)\s+(.*)", line)
        if not event:
            continue
        pid, timestamp, text = int(event[1]), float(event[2]), event[3]
        executable = re.search(r'execve\("([^"]+)"', text)
        if executable and "= 0" in text:
            processes[pid] = {"pid":pid, "executable":Path(executable[1]).name,
                              "exec_timestamp":timestamp, "completed":False}
        if pid in processes and ("exit_group(" in text or "+++ killed by" in text):
            processes[pid].update(elapsed_seconds=round(timestamp-processes[pid]["exec_timestamp"],6),
                                  completed="exit_group(" in text, exit_event=text)
    return list(processes.values())


def sample_group(group, observations):
    """Approximate observations: short-lived processes can escape sampling."""
    rss_total = 0
    for path in Path("/proc").glob("[0-9]*/stat"):
        try:
            fields = path.read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) != group:
                continue
            pid = int(path.parent.name)
            key = (pid, fields[19])  # start time disambiguates reused PIDs
            executable = Path(os.readlink(path.parent / "exe")).name
            cpu = (int(fields[11]) + int(fields[12])) / os.sysconf("SC_CLK_TCK")
            rss = int(fields[21]) * os.sysconf("SC_PAGE_SIZE") // 1024
            old = observations.setdefault(key, {"pid": pid, "executable": executable,
                                                "cpu_seconds": 0, "peak_rss_kib": 0})
            old["executable"] = executable
            old["cpu_seconds"] = max(old["cpu_seconds"], cpu)
            old["peak_rss_kib"] = max(old["peak_rss_kib"], rss)
            rss_total += rss
        except (OSError, ValueError, IndexError):
            continue  # A process can finish between reading stat and exe.
    return rss_total


def execute(command, output, limit):
    # Adopt and reap orphaned grandchildren after a timeout, rather than leaving
    # KBMAG zombies with the container's PID 1. This affects this process only.
    if ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "Linux PR_SET_CHILD_SUBREAPER failed")
    observations = {}
    peak_rss = 0
    start = time.monotonic()
    timed_out = False
    interrupted = False
    extra_usage = []
    with output.open("w") as log:
        child = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                 start_new_session=True)
        try:
            while True:
                peak_rss = max(peak_rss, sample_group(child.pid, observations))
                pid, status, usage = os.wait4(child.pid, os.WNOHANG)
                if pid:
                    break
                if time.monotonic() - start >= limit:
                    timed_out = True
                    os.killpg(child.pid, signal.SIGTERM)
                    grace = time.monotonic() + 5
                    while True:
                        pid, status, usage = os.wait4(child.pid, os.WNOHANG)
                        if pid:
                            break
                        if time.monotonic() >= grace:
                            os.killpg(child.pid, signal.SIGKILL)
                            _, status, usage = os.wait4(child.pid, 0)
                            break
                        time.sleep(.05)
                    # Clean any group members left after the parent exited.
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    break
                time.sleep(.05)
        except KeyboardInterrupt:
            interrupted = True
            os.killpg(child.pid, signal.SIGKILL)
            _, status, usage = os.wait4(child.pid, 0)
            pid = child.pid
        finally:
            if child.returncode is None:
                # wait4 above owns reaping; tell Popen not to wait a second time.
                child.returncode = os.waitstatus_to_exitcode(status) if 'status' in locals() and pid else None
                if child.returncode is None:
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    child.wait()
            # Reap adopted descendants in this process group only. After the
            # parent has exited they must not survive the benchmark invocation.
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            while True:
                try:
                    adopted, _, adopted_usage = os.wait4(-child.pid, 0)
                    extra_usage.append(adopted_usage)
                except ChildProcessError:
                    break
    wall = time.monotonic() - start
    return {"status": "interrupted" if interrupted else "timeout" if timed_out else ("completed" if child.returncode == 0 else "error"),
            "exit_status": 130 if interrupted else 124 if timed_out else (child.returncode if child.returncode >= 0 else 128-child.returncode),
            "raw_returncode": child.returncode, "wall_seconds": round(wall, 6),
            "waited_user_seconds": round(sum(u.ru_utime for u in [usage,*extra_usage]), 6),
            "waited_system_seconds": round(sum(u.ru_stime for u in [usage,*extra_usage]), 6),
            "waited_max_rss_kib": max(u.ru_maxrss for u in [usage,*extra_usage]),
            "sampled_peak_group_rss_kib": peak_rss,
            "sampled_processes": list(observations.values())}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    selector = p.add_mutually_exclusive_group(required=True)
    selector.add_argument("--case", choices=CASES)
    selector.add_argument("--suite", choices=["small", "extra-primes", "arithmetic-components"])
    p.add_argument("--prime", type=int)
    p.add_argument("--timeout", type=float, default=5)
    p.add_argument("--repeat", type=int, default=1)
    p.add_argument("--mode", choices=["standard", "large"], default="standard")
    p.add_argument("--task", choices=["h2", "abelian", "construction"], default="h2")
    p.add_argument("--diagnostics", action="store_true", help="GAP function profiling and InfoRWS=1")
    p.add_argument("--trace", action="store_true", help="strace process events (adds overhead)")
    p.add_argument("--gap", default=os.environ.get("GAP_BIN", "gap"))
    p.add_argument("--output", type=Path, required=True, help="new output directory; never overwrites")
    a = p.parse_args()
    if a.timeout <= 0 or a.repeat < 1 or (a.case and (a.prime is None or a.prime < 2)):
        p.error("positive timeout/repeat and --prime >=2 with --case are required")
    if a.suite and a.prime is not None:
        p.error("--prime applies only to --case")
    gap = shutil.which(a.gap)
    if gap is None:
        p.error("GAP executable not found; pass --gap")
    if a.trace and shutil.which("strace") is None:
        p.error("--trace requires strace")
    if a.task != "h2" and a.diagnostics:
        p.error("--diagnostics applies only to --task h2")
    if a.timeout > 30:
        p.error("this quick-baseline harness caps each invocation at 30 seconds")
    if a.task == "h2" and (a.case and a.case not in SMALL or a.suite == "arithmetic-components"):
        p.error("full H2 runs are restricted to the small finite-group whitelist; use --task abelian or construction for expensive presentations")
    jobs = ([(a.case, a.prime)] if a.case else
            [(c, q) for c in SMALL for q in [2, 3, 5, 7]] if a.suite == "small" else
            [("G3", 3), ("G5", 5), ("G7", 7), ("G11", 11)] if a.suite == "arithmetic-components" else
            [(c, q) for c in ["SL2F2", "SL2F3", "SL2F5"] for q in [11, 13]])
    a.output.mkdir(parents=True, exist_ok=False)
    source_files = ["tests/reproduce-h2.g", "tests/cases.g", "benchmarks/abelian.g", "benchmarks/construction.g", "benchmarks/run.py"]
    for filename in source_files:
        snapshot = a.output/"source"/filename
        snapshot.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT/filename, snapshot)
    metadata = {"created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                "git_commit": git("rev-parse", "HEAD"), "git_status": git("status", "--short"),
                "original_sha256": {f: digest(ROOT/f) for f in ["Algorithms.g", "Library-of-groups.g"]},
                "driver_sha256": {f: digest(ROOT/f) for f in source_files},
                "platform": {"uname": list(os.uname()), "cpu_count": os.cpu_count(),
                             "cpu_max":Path('/sys/fs/cgroup/cpu.max').read_text().strip(),
                             "memory_max":Path('/sys/fs/cgroup/memory.max').read_text().strip()},
                "arguments": {k: str(v) if isinstance(v, Path) else v for k, v in vars(a).items()},
                "measurement_notes": "Linux wait4 CPU includes waited-for children plus adopted descendants reaped by the subreaper. RSS is the maximum, not sum of concurrent RSS. /proc samples at ~50ms can miss short processes; RSS sums include shared pages. Traced/profiled runs add overhead. Timings include GAP startup."}
    (a.output/"metadata.json").write_text(json.dumps(metadata, indent=2)+"\n")
    results = []
    errors = False
    for case, prime in jobs:
        for repeat in range(1, a.repeat+1):
            target = a.output/f"{case}-q{prime}-r{repeat}"
            target.mkdir()
            setup = (f'ResearchCase := "{case}";; ResearchPrime := {prime};; '
                     f'ResearchLarge := {str(a.mode == "large").lower()};; '
                     f'ResearchDiagnostics := {str(a.diagnostics).lower()};;')
            command = [gap, "-q", "-b", "--quitonbreak", "-c", setup,
                       "tests/reproduce-h2.g" if a.task == "h2" else f"benchmarks/{a.task}.g"]
            if a.trace:
                command = ["strace", "-f", "-qq", "-ttt", "-T", "-e", "trace=process", "-o", str((target/"process.trace").resolve()), *command]
            result = execute(command, target/"output.log", a.timeout)
            text = (target/"output.log").read_text(errors="replace").replace("\\\n", "")
            bound = re.search(r"upper_bound=(-?\d+)", text)
            version = re.search(r"GAP ([^;\n]+); KBMAG ([^\n]+)", text)
            if result["status"] == "completed" and "COMPLETED" not in text:
                result["status"] = "error"
                result["error"] = "zero exit without completion marker"
            result.update(case=case, coefficient_prime=prime, repeat=repeat,
                          upper_bound=int(bound[1]) if bound and result["status"] == "completed" else None,
                          versions={"gap":version[1],"kbmag":version[2]} if version else None,
                          diagnostics_enabled=a.diagnostics,
                          confluent_systems=text.count("System computed is confluent.") if a.diagnostics else None,
                          nonconfluent_systems=text.count("System computed is NOT confluent.") if a.diagnostics else None,
                          knuth_bendix_starts=text.count("Calling external Knuth-Bendix program.") if a.diagnostics else None,
                          gap_profile_rows=[json.loads(m[1]) for m in re.finditer(r'PROFILE_ROW=(\[[^\n]*\])',text)],
                          scalar_stages=[{"name":m[1],"value":int(m[2]),"gap_cpu_ms":int(m[3])} for m in re.finditer(r'SCALAR (\w+)=(-?\d+) cpu_ms=(\d+)',text)],
                          construction_stages=[{"name":m[1],"gap_cpu_ms":int(m[2])} for m in re.finditer(r'COMPONENT (\w+) cpu_ms=(\d+)',text)],
                          traced_processes=process_trace(target/"process.trace"))
            (target/"result.json").write_text(json.dumps(result, indent=2)+"\n")
            results.append({"artifact_directory": target.name, **result})
            (a.output/"results.json").write_text(json.dumps(results, indent=2)+"\n")
            print(json.dumps({k: result[k] for k in ["case", "coefficient_prime", "repeat", "status", "upper_bound", "wall_seconds"]}), flush=True)
            if result["status"] == "interrupted":
                return 130
            errors |= result["status"] == "error"
    return 1 if errors else (124 if any(r["status"] == "timeout" for r in results) else 0)


if __name__ == "__main__":
    sys.exit(main())

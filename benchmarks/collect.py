#!/usr/bin/env python3
"""Archive existing quick-run artifacts; never launch GAP or alter algorithms.

Usage: python benchmarks/collect.py RAW_ROOT NEW_OUTPUT_DIRECTORY
RAW_ROOT contains small, abelian, construction, diagnostics, extra-primes,
and validation directories produced by the documented baseline workflow.
"""
import datetime
import json
from pathlib import Path
import sys

from run import digest, process_trace


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    source, output = map(Path,sys.argv[1:])
    suites = ["small","abelian","construction","diagnostics","extra-primes"]
    metadata = {name:json.loads((source/name/"metadata.json").read_text()) for name in suites}
    output.mkdir(parents=True, exist_ok=False)
    rows = []
    raw = []
    for suite in suites:
        for result in json.loads((source/suite/"results.json").read_text()):
            result = dict(result)
            directory = source/suite/result["artifact_directory"]
            result["traced_processes"] = process_trace(directory/"process.trace")
            result["suite"] = suite
            rows.append(result)
            trace = directory/"process.trace"
            raw.append({"suite":suite,"case":result["case"],
                        "coefficient_prime":result["coefficient_prime"],"repeat":result["repeat"],
                        "stdout":(directory/"output.log").read_text(),
                        "process_trace":trace.read_text() if trace.exists() else None})
    for filename, items in [("runs.jsonl",rows),("raw.jsonl",raw)]:
        (output/filename).write_text(''.join(json.dumps(row,separators=(',',':'))+'\n' for row in items))
    provenance = {"collected_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  "suite_metadata":metadata,"trace_parser_sha256":digest(Path(__file__).with_name('run.py')),
                  "postprocessing_note":"Trace intervals reparsed from raw strace, including split execve/resumed events. Numerical GAP outputs and original timing samples are unchanged."}
    (output/"metadata.json").write_text(json.dumps(provenance,indent=2)+'\n')
    (output/"validation.json").write_text((source/"validation/results.json").read_text())
    log = ''
    for path in sorted((source/"validation").glob('*.log')):
        log += f'=== {path.name} ===\n'+path.read_text()+'\n'
    (output/"validation.log").write_text(log.rstrip('\n')+'\n')
    print(f'Archived {len(rows)} measured runs and their raw outputs at {output}')


if __name__ == '__main__':
    main()

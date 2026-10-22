"""Regression tests for benchmark failure propagation and process cleanup."""
import importlib.util
import json
from pathlib import Path
import subprocess
import signal
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("benchmark", ROOT/"benchmarks/run.py")
benchmark = importlib.util.module_from_spec(spec)
spec.loader.exec_module(benchmark)


class BenchmarkTests(unittest.TestCase):
    def run_command(self, code, timeout=2):
        with tempfile.TemporaryDirectory() as d:
            output = Path(d)/"output.log"
            result = benchmark.execute([sys.executable,"-c",code], output, timeout)
            return result, output.read_text()

    def test_success_and_output(self):
        result, output = self.run_command("print('known output')")
        self.assertEqual(result["status"], "completed")
        self.assertEqual(output.strip(), "known output")
        self.assertGreater(result["wall_seconds"], 0)

    def test_failure_is_not_success(self):
        result, _ = self.run_command("raise SystemExit(7)")
        self.assertEqual((result["status"],result["exit_status"]), ("error",7))

    def test_timeout_reaps_descendants(self):
        code = "import subprocess,sys,time; p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)']); print(p.pid,flush=True); time.sleep(60)"
        result, output = self.run_command(code, .3)
        self.assertEqual((result["status"],result["exit_status"]), ("timeout",124))
        self.assertFalse((Path('/proc')/output.strip()).exists(), "descendant was not reaped")

    def test_expensive_h2_rejected_before_execution(self):
        with tempfile.TemporaryDirectory() as d:
            output = Path(d)/"unused"
            r = subprocess.run([sys.executable,str(ROOT/'benchmarks/run.py'),
                '--case','G7','--prime','7','--gap',sys.executable,'--output',str(output)],
                capture_output=True,text=True)
            self.assertEqual(r.returncode,2)
            self.assertIn('restricted',r.stderr)
            self.assertFalse(output.exists())

    def test_interrupt_is_recorded(self):
        with tempfile.TemporaryDirectory() as d:
            output = Path(d)/'output.log'
            helper = ("import importlib.util,json,sys; from pathlib import Path; "
                f"s=importlib.util.spec_from_file_location('b',{str(ROOT/'benchmarks/run.py')!r}); "
                "b=importlib.util.module_from_spec(s); s.loader.exec_module(b); "
                f"r=b.execute([sys.executable,'-c',\"import time; print('ready',flush=True); time.sleep(60)\"],Path({str(output)!r}),2); "
                "print(json.dumps(r))")
            child = subprocess.Popen([sys.executable,'-c',helper],stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE,text=True)
            try:
                deadline = time.monotonic()+2
                while time.monotonic()<deadline:
                    if output.exists() and 'ready' in output.read_text():
                        break
                    time.sleep(.01)
                else:
                    self.fail('interrupt fixture did not start')
                child.send_signal(signal.SIGINT)
                stdout, stderr = child.communicate(timeout=3)
                self.assertEqual(child.returncode,0,stderr)
                self.assertEqual(json.loads(stdout)['status'],'interrupted')
                self.assertEqual(json.loads(stdout)['exit_status'],130)
            finally:
                if child.poll() is None:
                    child.kill()
                    child.communicate()

    def test_trace_intervals_and_unfinished_process(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d)/'process.trace'
            path.write_text('10 100.100 execve("/bin/kbprog", [], 0x0) = 0 <0.001>\n'
                            '10 100.350 exit_group(0) = ?\n'
                            '11 100.400 execve("/bin/kbprog", [], 0x0) = 0 <0.001>\n'
                            '12 100.500 execve("/bin/kbprog", [], 0x0 <unfinished ...>\n'
                            '12 100.510 <... execve resumed>) = 0 <0.01>\n'
                            '12 100.600 exit_group(0) = ?\n')
            rows = benchmark.process_trace(path)
            self.assertEqual(rows[0]['elapsed_seconds'],.25)
            self.assertTrue(rows[0]['completed'])
            self.assertFalse(rows[1]['completed'])
            self.assertNotIn('elapsed_seconds',rows[1])
            self.assertEqual(rows[2]['elapsed_seconds'],.1)
            self.assertTrue(rows[2]['completed'])


if __name__ == '__main__':
    unittest.main()

#!/usr/bin/env python3
"""Mandatory fail-closed safety gate. Every probe must pass before a pilot."""
import argparse
import hashlib
import json
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]


def gone(record):
    path=Path(f"/proc/{record['pid']}/stat")
    try:
        actual=int(path.read_text().rsplit(')',1)[1].split()[19])
    except FileNotFoundError:
        return True
    return actual != record['start']  # Protect against PID reuse.


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    summary={'all_passed':False,'tests':[]}
    try:
        for mode in ['limits','memory','cpu','wall','output','normal_child','crash_child','interrupt']:
            memory=512 if mode=='limits' else 64
            cpu=1 if mode=='cpu' else 6
            wall=.5 if mode=='wall' else 4
            size=4096 if mode=='output' else 8*1024*1024
            pidfile=(a.output/(mode+'.pids.json')).resolve()
            cmd=[sys.executable,str(ROOT/'experiments/resource_guard.py'),'--output',str((a.output/mode).resolve()),
                 '--memory-mib',str(memory),'--cpu-seconds',str(cpu),'--wall-seconds',str(wall),
                 '--output-bytes',str(size),'--',sys.executable,'-u',str(ROOT/'tests/resource_probes.py'),'wall' if mode=='interrupt' else mode,str(pidfile)]
            if mode=='interrupt':
                proc=subprocess.Popen(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
                deadline=time.monotonic()+2
                while not pidfile.exists() and time.monotonic()<deadline:
                    time.sleep(.01)
                assert pidfile.exists(),'interrupt probe did not initialize'
                proc.send_signal(signal.SIGTERM)
                out,err=proc.communicate(timeout=5)
                run=subprocess.CompletedProcess(cmd,proc.returncode,out,err)
            else:
                run=subprocess.run(cmd,cwd=ROOT,text=True,capture_output=True,timeout=9)
            (a.output/(mode+'.supervisor.txt')).write_text(run.stdout+run.stderr)
            assert run.returncode==0,(mode,run.stdout,run.stderr)
            record=json.loads((a.output/mode/'resources.json').read_text())
            assert record['cleanup_verified']
            if mode=='limits':
                limits=json.loads((a.output/mode/'stdout.txt').read_text())
                assert limits=={'RLIMIT_AS':[512*1024*1024]*2,'RLIMIT_CPU':[6]*2,'RLIMIT_FSIZE':[8*1024*1024]*2}
                assert record['termination']=='completed'
            else:
                ids=json.loads(pidfile.read_text())
                assert all(gone(v) for v in ids.values()),(mode,ids)
                assert any(c['pid']==ids['child']['pid'] for c in record['adopted_children'])
                if mode=='memory':
                    assert record['returncode']==73 and 'EXPECTED_MEMORY_ERROR' in (a.output/mode/'stderr.txt').read_text()
                elif mode=='cpu':
                    assert record['termination']=='cpu_limit' and record['worker']['user_seconds']+record['worker']['system_seconds']>=.8
                elif mode=='wall':
                    assert record['termination']=='wall_limit'
                elif mode=='output':
                    assert record['termination']=='output_limit' and record['stdout_bytes']==size
                elif mode=='normal_child':
                    assert record['returncode']==0
                elif mode=='crash_child':
                    assert record['returncode']==17
                elif mode=='interrupt':
                    assert record['termination']=='supervisor_signal' and record['supervisor_signal']==signal.SIGTERM
            summary['tests'].append({'mode':mode,'passed':True,'resources':record})
            print('PASS',mode,record['termination'],flush=True)
        summary['all_passed']=True
    except BaseException as error:
        summary['failure']=repr(error)
        raise
    finally:
        files=['experiments/resource_guard.py','tests/resource_probes.py','scripts/test-resource-guard.py']
        summary['source_sha256']={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files}
        (a.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('PASS: all eight safety probes; expected limits and escaped-session child cleanup verified.')


if __name__=='__main__':
    main()

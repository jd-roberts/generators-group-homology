#!/usr/bin/env python3
"""Consume exactly ONE authorized R7 checkpoint continuation after all gates."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,required=True);a=p.parse_args();base=a.base.resolve()
    marker=base/'attempt.json'
    if marker.exists():p.error('authorization already consumed; no retry is allowed')
    gates=[base/'loader-gate.json',base/'stage1/safety/summary.json',base/'stage1/verification-summary.json',base/'prior-replay-gate.json']
    for path in gates:
        data=json.loads(path.read_text());assert data['all_passed'],path
        for name,digest in data['source_sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    guard=json.loads((base/'loader-final.guard/resources.json').read_text());assert guard['cleanup_verified'] and guard['returncode']==0
    frozen=json.loads((base/'preparation/checkpoint.json').read_text());assert len(frozen['rules'])==241
    loaded=json.loads((base/'loaded-state.json').read_text());assert loaded['rules']==frozen['rules']
    validation=subprocess.run([sys.executable,'scripts/check-a4-continuation.py','--base',str(base),'--inputs-only'],cwd=ROOT,capture_output=True,text=True,timeout=10)
    (base/'input-verification.stdout.txt').write_text(validation.stdout);(base/'input-verification.stderr.txt').write_text(validation.stderr)
    assert validation.returncode==0,validation.stderr
    sources=['experiments/checkpoint_completion.py','experiments/a4_continuation_worker.py','experiments/counted_completion.py',
             'experiments/certified_completion.py','experiments/resource_guard.py','scripts/prepare-a4-continuation.py',
             'scripts/test-a4-checkpoint.py','scripts/check-a4-continuation.py','scripts/run-a4-continuation.py',
             'scripts/check-power-certificate.py','scripts/check-relation-span-certificate.py','docs/PRIME7-A4-CONTINUATION-PLAN.md']
    files=['checkpoint.json','schedule.json','prior-trace.jsonl','input.json.gz']
    attempt=dict(attempt=1,no_retry=True,only_target=7,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 base_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                 source_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in sources},
                 preparation_sha256={name:hashlib.sha256((base/'preparation'/name).read_bytes()).hexdigest() for name in files},
                 gate_sha256={str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in gates})
    with marker.open('x') as stream:json.dump(attempt,stream,indent=2);stream.write('\n')
    for name in sources:
        dest=base/'source'/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((ROOT/name).read_bytes())
    command=[sys.executable,'experiments/resource_guard.py','--output',str(base/'worker'),'--memory-mib','512',
             '--cpu-seconds','6','--wall-seconds','10','--output-bytes','8388608','--',sys.executable,'-u',
             'experiments/a4_continuation_worker.py','--base',str(base)]
    run=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=14)
    (base/'supervisor.stdout.txt').write_text(run.stdout);(base/'supervisor.stderr.txt').write_text(run.stderr)
    assert run.returncode==0,('supervisor failure; no retry',run.stderr)
    replay=subprocess.run([sys.executable,'scripts/check-a4-continuation.py','--base',str(base),'--write-results'],cwd=ROOT,capture_output=True,text=True,timeout=15)
    (base/'independent-check.stdout.txt').write_text(replay.stdout);(base/'independent-check.stderr.txt').write_text(replay.stderr)
    assert replay.returncode==0,('independent checker failure; no retry',replay.stderr)
    result=json.loads((base/'result.json').read_text());print(json.dumps(dict(r7_certified=result['r7_certified'],verified_new_rules=result['verified_new_rules'],
        all_certified_originals=result['all_certified_originals'],summary=result['summary']),indent=2))


if __name__=='__main__':main()

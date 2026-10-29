#!/usr/bin/env python3
"""Consume ONE authorized known-identity control, after fail-closed safety gates."""
import argparse
import datetime
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,required=True);p.add_argument('--small-results',type=Path,required=True);a=p.parse_args()
    base=a.base.resolve();base.mkdir(parents=True,exist_ok=True)
    marker=base/'control-attempt.json'
    if marker.exists():p.error('control already consumed; no retry is authorized')
    safety=json.loads((base/'stage1/safety/summary.json').read_text())
    old=json.loads((base/'stage1/verification-summary.json').read_text())
    small=json.loads((a.small_results/'summary.json').read_text())
    assert safety['all_passed'] and old['all_passed'] and small['all_passed'],'gate failed; abort control'
    for record in [safety,old,small]:
        for path,digest in record['source_sha256'].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,('gate source changed',path)
    assert len(small['results'])==61
    driver=json.loads((a.small_results.parent/'suite-run.guard/resources.json').read_text())
    assert driver['returncode']==0 and driver['cleanup_verified'],'small suite supervisor gate failed'
    # Pin the exact full quotient and copy it unchanged; static checks, no search.
    raw=(ROOT/'docs/evidence/prime7-spanning-preparation/fixed-quotient-blueprint.json.gz').read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='d33076b1c1b20c9950349645e77c0dbcebe9c8e326ba77dd041b6b696b134a60'
    blueprint=json.loads(gzip.decompress(raw));full=blueprint['quotient_relators'];indices=[225,140,204]
    source=dict(rank=6,original_indices=indices,base_relators=[full[i-1] for i in indices],target=blueprint['problem']['relators'][11])
    assert source['target']==[1]*7 and source['base_relators']==[[1,5,1,-5],[-5]+[-1]*7+[5]+[1]*7,[1]*49]
    paths=['experiments/certified_power.py','experiments/certified_completion.py','experiments/restricted_identity.py',
           'experiments/power_control_worker.py','experiments/relation_span.py','experiments/resource_guard.py',
           'scripts/run-prime7-power-control.py','scripts/check-power-control.py','scripts/check-power-certificate.py','scripts/check-relation-span-certificate.py']
    attempt=dict(authorized_control=1,no_retry=True,target=12,indices=indices,
                 created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 base_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                 source_sha256={path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in paths},
                 gate_sha256={str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in [base/'stage1/safety/summary.json',base/'stage1/verification-summary.json',a.small_results/'summary.json']})
    with marker.open('x') as f:json.dump(attempt,f,indent=2);f.write('\n')
    # Reservation consumes this control even if launch or subsequent checking fails.
    (base/'full-input.json.gz').write_bytes(raw)
    (base/'control-input.json').write_text(json.dumps(source,indent=2)+'\n')
    for path in paths:
        dest=base/'source'/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((ROOT/path).read_bytes())
    command=[sys.executable,'experiments/resource_guard.py','--output',str(base/'worker'),'--memory-mib','512',
             '--cpu-seconds','3','--wall-seconds','5','--output-bytes','8388608','--',sys.executable,'-u',
             'experiments/power_control_worker.py','--input',str(base/'control-input.json')]
    run=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=9)
    (base/'supervisor.stdout.txt').write_text(run.stdout);(base/'supervisor.stderr.txt').write_text(run.stderr)
    assert run.returncode==0,('supervisor failure; no retry',run.stderr)
    # Separate verifier, not the producer, accepts every local and full-Q product.
    verify=subprocess.run([sys.executable,'scripts/check-power-control.py','--base',str(base)],cwd=ROOT,capture_output=True,text=True,timeout=10)
    (base/'independent-check.stdout.txt').write_text(verify.stdout);(base/'independent-check.stderr.txt').write_text(verify.stderr)
    assert verify.returncode==0,('independent replay failed; no retry',verify.stderr)
    result=json.loads(verify.stdout);(base/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(methods={k:v['answer']['status'] for k,v in result['methods'].items()},
                         combined_verified_rules=result['combined_verified_rules'],new_arithmetic_targets=0,spanning=False),indent=2))


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Exactly one authorized R7 experiment, gated and resource bounded. No retries."""
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
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,required=True);a=p.parse_args();base=a.base.resolve()
    marker=base/'attempt.json'
    if marker.exists():p.error('R7 attempt already consumed; no retries or another directory are authorized')
    paths_to_gates=[base/'stage1/safety/summary.json',base/'stage1/verification-summary.json',base/'final-infrastructure/summary.json',base/'prior-replay-gate.json']
    for gate_path in paths_to_gates:
        gate=json.loads(gate_path.read_text());assert gate['all_passed'],('gate failed',gate_path)
        for path,digest in gate['source_sha256'].items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    infra=json.loads((base/'final-infrastructure.guard/resources.json').read_text());assert infra['cleanup_verified'] and infra['returncode']==0
    plan_path=base/'preparation/plan.json';plan=json.loads(plan_path.read_text())
    assert plan['target']==7 and plan['limits']['shared_search_seconds']==5 and plan['limits']['completion_rules']==256
    raw=(ROOT/'docs/evidence/prime7-spanning-preparation/fixed-quotient-blueprint.json.gz').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==plan['input_sha256']=='d33076b1c1b20c9950349645e77c0dbcebe9c8e326ba77dd041b6b696b134a60'
    # This is fixed formula replay, not a word-problem search. Fail before
    # reserving the attempt if a centrality certificate is invalid.
    sys.path.insert(0,str(ROOT))
    from experiments.a4_structure import commuting_equations
    sp=importlib.util.spec_from_file_location('independent',ROOT/'scripts/check-relation-span-certificate.py')
    cp=importlib.util.module_from_spec(sp);sp.loader.exec_module(cp)
    blueprint=json.loads(gzip.decompress(raw));lemmas=json.loads(json.dumps(commuting_equations()))
    for lemma in lemmas:
        cp.check_product(lemma['lhs']+cp.inv(lemma['rhs']),blueprint['quotient_relators'],lemma['factors'],6)
    (base/'preflight-centrality.json').write_text(json.dumps(dict(equations=lemmas,verified_original_Q=True),separators=(',',':'))+'\n')
    sources=['experiments/a4_structure.py','experiments/counted_completion.py','experiments/a4_worker.py','experiments/certified_power.py',
             'experiments/certified_completion.py','experiments/restricted_identity.py','experiments/resource_guard.py',
             'experiments/relation_span.py','scripts/run-a4-experiment.py','scripts/check-a4-experiment.py','scripts/prepare-a4-experiment.py',
             'scripts/test-a4-infrastructure.py','scripts/check-power-certificate.py','scripts/check-relation-span-certificate.py',
             'docs/PRIME7-A4-EXPERIMENT-PLAN.md']
    attempt=dict(attempt=1,no_retry=True,only_search_target=7,input_sha256=plan['input_sha256'],
                 plan_sha256=hashlib.sha256(plan_path.read_bytes()).hexdigest(),
                 created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 base_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                 source_sha256={path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sources},
                 gate_sha256={str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths_to_gates})
    with marker.open('x') as stream:json.dump(attempt,stream,indent=2);stream.write('\n')
    (base/'input.json.gz').write_bytes(raw)
    for path in sources:
        dest=base/'source'/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((ROOT/path).read_bytes())
    command=[sys.executable,'experiments/resource_guard.py','--output',str(base/'worker'),'--memory-mib','512','--cpu-seconds','6',
             '--wall-seconds','10','--output-bytes','8388608','--',sys.executable,'-u','experiments/a4_worker.py',
             '--input',str(base/'input.json.gz'),'--plan',str(plan_path)]
    run=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=14)
    (base/'supervisor.stdout.txt').write_text(run.stdout);(base/'supervisor.stderr.txt').write_text(run.stderr)
    assert run.returncode==0,('supervisor error; do not retry',run.stderr)
    check=subprocess.run([sys.executable,'scripts/check-a4-experiment.py','--base',str(base),'--write-results'],cwd=ROOT,capture_output=True,text=True,timeout=15)
    (base/'independent-check.stdout.txt').write_text(check.stdout);(base/'independent-check.stderr.txt').write_text(check.stderr)
    assert check.returncode==0,('independent checking failed; no retry',check.stderr)
    result=json.loads((base/'result.json').read_text())
    print(json.dumps(dict(r7_certified=result['r7_certified'],new_literal_certificates=result['new_literal_certificates'],
                         all_certified_originals=result['all_certified_originals'],summary=result['summary']),indent=2))


if __name__=='__main__':main()

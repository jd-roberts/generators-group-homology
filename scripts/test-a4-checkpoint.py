#!/usr/bin/env python3
"""Small completion test and actual checkpoint LOAD-ONLY validation; no R7 search."""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from experiments.checkpoint_completion import CheckpointCompletion


def load(name,path):
    sp=importlib.util.spec_from_file_location(name,ROOT/path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,required=True);a=p.parse_args();b=a.base
    checker=load('independent','scripts/check-a4-continuation.py');products=load('products','scripts/check-relation-span-certificate.py')
    verified,_,rules,plan=checker.inputs(b)
    engine=CheckpointCompletion(rules,plan['jobs'])  # NO prove/overlaps/complete call.
    state=dict(rules=engine.rules,jobs=[list(item[2]) for item in sorted(engine.pending)],queued_jobs=len(engine.queued))
    state=json.loads(json.dumps(state));assert state['rules']==rules and state['jobs']==plan['jobs'] and state['queued_jobs']==4000
    (b/'loaded-state.json').write_text(json.dumps(state,separators=(',',':'))+'\n')
    checks=['actual 241-rule loader roundtrip and exact frozen job order verified',
            '241 forward and 236 reverse products independently checked']
    toy=[dict(id=0,lhs=[1,1],rhs=[],factors=[[[],1,1]],origin='toy_x2'),
         dict(id=1,lhs=[1,1,1],rhs=[],factors=[[[],2,1]],origin='toy_x3')]
    events=[];small=CheckpointCompletion(toy,[[0,1]],seconds=1,emit=events.append);small.complete([(1,)])
    answer=small.goal_answers[0] if small.goal_answers else small.prove((1,))
    assert answer['status']=='certified'
    products.check_product([1],[[1,1],[1,1,1]],json.loads(json.dumps(answer['factors'])),1)
    assert small.pairs==small.jobs_completed==1 and len(small.queued)==1 and small.compatible_overlap_placements==4
    assert len(small.rules)==3 and any(e['kind']=='new_rule' for e in events)
    checks.append('small x2/x3 overlap derives x with independent product; fixed one-job queue stays fixed')
    bad=copy.deepcopy(toy);bad[0]['lhs']=[]
    try:CheckpointCompletion(bad,[[0,1]])
    except ValueError:checks.append('invalid checkpoint orientation rejected')
    else:raise AssertionError('bad orientation accepted')
    bad=copy.deepcopy(toy);bad[0]['factors'][0][2]=-1
    try:products.check_product(bad[0]['lhs'],[[1,1],[1,1,1]],bad[0]['factors'],1)
    except ValueError:checks.append('changed checkpoint product sign rejected independently')
    else:raise AssertionError('bad product accepted')
    try:products.check_product([1,1],[[1,1],[1,1,1]],[],1)
    except ValueError:checks.append('missing reverse quotient-coverage product rejected')
    else:raise AssertionError('missing coverage accepted')
    try:CheckpointCompletion(toy,[[0,1],[0,1]])
    except ValueError:checks.append('repeated frozen job rejected')
    else:raise AssertionError('repeated job accepted')
    (b/'small-test.json').write_text(json.dumps(dict(events=events,answer=answer,accounting=small.accounting()),separators=(',',':'))+'\n')
    sources=['experiments/checkpoint_completion.py','scripts/prepare-a4-continuation.py','scripts/check-a4-continuation.py','scripts/test-a4-checkpoint.py',
             'experiments/counted_completion.py','experiments/certified_completion.py','experiments/resource_guard.py']
    (b/'loader-gate.json').write_text(json.dumps(dict(all_passed=True,checks=checks,input_verification=verified,
        source_sha256={path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sources}),indent=2)+'\n')
    print('PASS: load-only full-Q equivalence, exact schedule, small positive completion, and four adversarial checks.')


if __name__=='__main__':main()

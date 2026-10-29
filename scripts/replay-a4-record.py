#!/usr/bin/env python3
"""Certificate and static-witness replay only; no arithmetic search is invoked."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def load(name,path):
    s=importlib.util.spec_from_file_location(name,ROOT/path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,required=True);a=p.parse_args();b=a.base
    check=load('independent_a4','scripts/check-a4-experiment.py');result,combined=check.verify(b)
    assert result==json.loads((b/'result.json').read_text())
    assert combined==json.loads((b/'verified-products.json').read_text())
    attempt=json.loads((b/'attempt.json').read_text())
    for path,digest in attempt['gate_sha256'].items():assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest,path
    for gate in ['stage1/safety/summary.json','stage1/verification-summary.json','final-infrastructure/summary.json','prior-replay-gate.json']:
        record=json.loads((b/gate).read_text());assert record['all_passed']
        for path,digest in record['source_sha256'].items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    analysis=json.loads((b/'preparation/analysis.json').read_text());inventory=json.loads((ROOT/'docs/evidence/prime7-spanning-preparation/inventory.json').read_text())
    M,Z=inventory['candidate_occurrence_matrix'],inventory['existing_zero_identity_matrix']
    dual=analysis['dual_functional_not_a_nonmembership_obstruction']
    assert dual[6]==1 and all(sum(x*y for x,y in zip(r,dual))%7==0 for r in M+Z)
    coefficients=analysis['necessary_exponent_witness'];E=analysis['candidate_exponents']
    assert [sum(c*r[j] for c,r in zip(coefficients,E))%7 for j in range(6)]==[0,0,0,0,4,0]
    product=load('independent_products','scripts/check-relation-span-certificate.py')
    full=product.make_quotient(combined['problem']);rows=analysis['quotient_inventory'];assert len(rows)==236
    for i,row in enumerate(rows):
        assert row['index']==i+1 and row['word']==full[i]
        root,e,q=row['canonical_cyclic_root'],row['power_exponent'],row['normalizing_conjugator']
        w=root*e if e>=0 else product.inv(root)*(-e)
        assert product.cancel(q+w+product.inv(q))==full[i]
    pure=[]
    for line in (b/'worker/stdout.txt').read_text().splitlines():
        event=json.loads(line)
        if event['kind']!='rule':continue
        rule=event['rule'];w=product.cancel(rule['lhs']+product.inv(rule['rhs']));q=[]
        while len(w)>1 and w[0]==-w[-1]:q.append(w[0]);w=w[1:-1]
        if w and all(abs(x)==5 for x in w):
            pure.append(dict(rule=rule['id'],origin=rule['origin'],exponent=sum(1 if x>0 else -1 for x in w),conjugator=q))
    assert pure==[dict(rule=51,origin='original_Q_199',exponent=28,conjugator=[])]
    print(json.dumps(dict(one_authorized_attempt=True,r7_certified=result['r7_certified'],
                          verified_completion_rules=result['verified_completion_rules'],verified_power_rules=result['verified_power_rules'],
                          verified_centrality_equations=result['verified_preflight_centrality_equations'],
                          certified_originals=result['all_certified_originals'],full_spanning=result['full_spanning_established'],
                          all_static_witnesses_and_gates_verified=True,search_executed_by_this_replay=False,pure_a_powers_in_rule_trace=pure),indent=2))


if __name__=='__main__':main()

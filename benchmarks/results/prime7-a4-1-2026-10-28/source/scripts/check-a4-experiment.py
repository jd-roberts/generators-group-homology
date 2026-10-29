#!/usr/bin/env python3
"""Independent certificate/counter/linear replay. No discovery code imported."""
import argparse
import copy
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def representation(rows,target):
    basis={}
    for i,row in enumerate(rows):
        v=[x%7 for x in row];c=[int(i==j) for j in range(len(rows))]
        for pivot,(b,d) in sorted(basis.items()):
            t=v[pivot];v=[(a-t*x)%7 for a,x in zip(v,b)];c=[(a-t*x)%7 for a,x in zip(c,d)]
        pivot=next((j for j,x in enumerate(v) if x),None)
        if pivot is not None:
            k=pow(v[pivot],-1,7);basis[pivot]=([x*k%7 for x in v],[x*k%7 for x in c])
    v=target[:];c=[0]*len(rows)
    for pivot,(b,d) in sorted(basis.items()):
        t=v[pivot];v=[(a-t*x)%7 for a,x in zip(v,b)];c=[(a+t*x)%7 for a,x in zip(c,d)]
    return None if any(v) else c,len(basis)


def verify(directory):
    product=module('independent_products','scripts/check-relation-span-certificate.py')
    rules_checker=module('independent_rules','scripts/check-power-certificate.py')
    frozen=(directory/'input.json.gz').read_bytes();blueprint=json.loads(gzip.decompress(frozen))
    plan=json.loads((directory/'preparation/plan.json').read_text());attempt=json.loads((directory/'attempt.json').read_text())
    assert hashlib.sha256(frozen).hexdigest()==plan['input_sha256']==attempt['input_sha256']
    assert plan['target']==7 and blueprint['problem']['relators'][6]==[5]*4 and len(blueprint['quotient_relators'])==236
    assert plan['completion_inputs_include_target_as_relation'] is False
    assert attempt['attempt']==1 and attempt['no_retry']
    assert hashlib.sha256((directory/'preparation/plan.json').read_bytes()).hexdigest()==attempt['plan_sha256']
    for path,digest in attempt['source_sha256'].items():
        assert hashlib.sha256((directory/'source'/path).read_bytes()).hexdigest()==digest,path
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    assert product.verify(blueprint)['certified_targets']==[3,5,9,12,15]
    base=product.make_quotient(blueprint['problem']);assert base==blueprint['quotient_relators']
    usage=json.loads((directory/'worker/resources.json').read_text())
    assert usage['limits']=={'memory_bytes':536870912,'cpu_seconds':6,'wall_seconds':10.0,'output_bytes':8388608} and usage['cleanup_verified']
    preflight=json.loads((directory/'preflight-centrality.json').read_text())
    assert len(preflight['equations'])==20
    for lemma in preflight['equations']:
        product.check_product(lemma['lhs']+product.inv(lemma['rhs']),base,lemma['factors'],6)
    events=[];discarded=[]
    for n,line in enumerate((directory/'worker/stdout.txt').read_bytes().splitlines(keepends=True),1):
        try:
            if not line.endswith(b'\n'):raise ValueError('incomplete record')
            events.append(json.loads(line))
        except (ValueError,UnicodeDecodeError):discarded.append(n)
    combined=copy.deepcopy(blueprint);accepted_rules=[];auxiliary=[];power_count=0;new_literal=set()
    def accept_equation(equation):
        word=product.cancel(equation['lhs']+product.inv(equation['rhs']))
        product.check_product(word,base,equation['factors'],6)
        # No word search: classify literal free equalities already in the trace.
        for i,target in enumerate(blueprint['problem']['relators'],1):
            if word==target:proof=equation['factors']
            elif product.inv(word)==target:proof=[[q,j,-s] for q,j,s in reversed(equation['factors'])]
            else:continue
            product.check_product(target,base,proof,6)
            if combined['targets'][i-1]['status']!='certified':new_literal.add(i)
            combined['targets'][i-1]=dict(status='certified',factors=proof)
    for event in events:
        kind=event['kind']
        if kind=='header':
            assert event['target']==7 and event['target_word']==[5]*4 and event['input_sha256']==attempt['input_sha256']
            assert event['plan_sha256']==attempt['plan_sha256']
            assert event['effective_os_limits']=={'RLIMIT_AS':[536870912]*2,'RLIMIT_CPU':[6]*2,'RLIMIT_FSIZE':[8388608]*2}
        elif kind=='power_result':
            local,mapped=event['local'],event['mapped'];indices=plan['power_indices']
            assert len(local['rules'])==len(mapped['rules'])<=128
            def remap(proof):
                assert all(type(j) is int and 1<=j<=len(indices) for q,j,s in proof)
                return [[q,indices[j-1],s] for q,j,s in proof]
            for a,b in zip(local['rules'],mapped['rules']):
                assert b==dict(a,factors=remap(a['factors']))
                assert len(b['factors'])<=2000
                accept_equation(b)
            for a,b in zip(local['targets'],mapped['targets']):
                assert b==(dict(a,factors=remap(a['factors'])) if a['status']=='certified' else a)
            power_count=len(mapped['rules'])
            if mapped['targets'][0]['status']=='certified':
                proof=mapped['targets'][0]['factors'];product.check_product([5]*4,base,proof,6)
                combined['targets'][6]=mapped['targets'][0];new_literal.add(7)
        elif kind=='auxiliary_equation':
            equation=event['equation'];accept_equation(equation);auxiliary.append(equation)
        elif kind=='rule':
            r=event['rule'];assert r['id']==len(accepted_rules)
            assert max(len(r['lhs']),len(r['rhs']))<=512 and len(r['factors'])<=2000
            accepted_rules.append(r);accept_equation(r)
        elif kind=='target':
            assert event['target']==7
            answer=event['answer'];assert answer['status'] in ['certified','unresolved']
            if answer['status']=='certified':
                product.check_product([5]*4,base,answer['factors'],6);combined['targets'][6]=answer;new_literal.add(7)
    assert len(accepted_rules)<=256
    rules_checker.verify_rules(dict(rules=accepted_rules),base,6)
    summary=[e for e in events if e['kind']=='summary']
    if summary:
        assert len(summary)==1 and summary[0]['only_search_target']==7
        counters=summary[0]['accounting']
        if counters:
            assert counters['rule_pair_jobs_processed']<=counters['rule_pair_jobs_queued']<=4000
            assert counters['compatible_placements_not_submitted'] in [0,1]
            assert counters['compatible_overlap_placements']==counters['submitted_overlap_equations']+counters['oversize_overlap_placements']+counters['compatible_placements_not_submitted']
            assert counters['offset_tests']>=counters['compatible_overlap_placements']
        assert summary[0]['completion_rules']<=256 and summary[0]['search_wall_seconds']<=5.10
        assert summary[0]['original_rows_seeded']==plan['completion_input_order'][:summary[0]['original_rows_seeded_count']]
    direct=product.verify(combined)['certified_targets']
    inventory=json.loads((ROOT/'docs/evidence/prime7-spanning-preparation/inventory.json').read_text())
    rows=inventory['candidate_occurrence_matrix']+inventory['existing_zero_identity_matrix']
    rows += [[int(j==i-1) for j in range(32)] for i in direct]
    witnesses={}
    for i in range(32):
        vector=[int(i==j) for j in range(32)];c,rank=representation(rows,vector)
        if c is not None:
            assert [sum(k*r[j] for k,r in zip(c,rows))%7 for j in range(32)]==vector
            witnesses[str(i+1)]=c
    closure=sorted(map(int,witnesses))
    return dict(r7_certified=7 in direct,direct_certified_originals=direct,new_literal_certificates=sorted(new_literal-set([3,5,9,12,15])),
                all_certified_originals=closure,additional_linear_consequences=sorted(set(closure)-set(direct)),
                unresolved_originals=sorted(set(range(1,33))-set(closure)),linear_row_rank=rank,linear_witnesses=witnesses,
                full_spanning_established=len(closure)==32,verified_completion_rules=len(accepted_rules),verified_power_rules=power_count,
                verified_auxiliary_equations=len(auxiliary),verified_preflight_centrality_equations=len(preflight['equations']),discarded_lines=discarded,summary=summary[0] if summary else None,resources=usage),combined


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,required=True);p.add_argument('--write-results',action='store_true');a=p.parse_args()
    result,combined=verify(a.base)
    if a.write_results:
        (a.base/'result.json').write_text(json.dumps(result,indent=2)+'\n')
        (a.base/'verified-products.json').write_text(json.dumps(combined,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['linear_witnesses','resources']},indent=2))

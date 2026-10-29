#!/usr/bin/env python3
"""Independent bidirectional quotient/continuation certificates; no search imports."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def load(name,path):
    sp=importlib.util.spec_from_file_location(name,ROOT/path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m


def inputs(base):
    product=load('independent_products','scripts/check-relation-span-certificate.py')
    rulecheck=load('independent_rules','scripts/check-power-certificate.py')
    prep=base/'preparation';frozen=(prep/'input.json.gz').read_bytes()
    assert hashlib.sha256(frozen).hexdigest()=='d33076b1c1b20c9950349645e77c0dbcebe9c8e326ba77dd041b6b696b134a60'
    blueprint=json.loads(gzip.decompress(frozen));assert product.verify(blueprint)['certified_targets']==[3,5,9,12,15]
    q=product.make_quotient(blueprint['problem']);assert q==blueprint['quotient_relators'] and len(q)==236
    checkpoint=json.loads((prep/'checkpoint.json').read_text());rules=checkpoint['rules'];plan=json.loads((prep/'schedule.json').read_text())
    trace=(prep/'prior-trace.jsonl').read_bytes();assert hashlib.sha256(trace).hexdigest()==checkpoint['prior_trace_sha256']
    assert trace==(ROOT/'benchmarks/results/prime7-a4-1-2026-10-28/worker/stdout.txt').read_bytes()
    old=[json.loads(l)['rule'] for l in trace.splitlines() if json.loads(l)['kind']=='rule']
    assert len(old)==233 and len(rules)==241 and rules[:233]==old
    for k in range(8):
        assert rules[233+k]==dict(id=233+k,lhs=q[216+k],rhs=[],factors=[[[],217+k,1]],origin='unsimplified_Q'+str(217+k))
    rulecheck.verify_rules(dict(rules=rules),q,6)
    for r in rules:assert max(len(r['lhs']),len(r['rhs']))<=512 and len(r['factors'])<=2000
    reverse=checkpoint['original_Q_coverage'];assert set(reverse)==set(map(str,range(1,237)))
    rb=[product.cancel(r['lhs']+product.inv(r['rhs'])) for r in rules]
    for i,w in enumerate(q,1):
        assert len(reverse[str(i)])<=2000
        product.check_product(w,rb,reverse[str(i)],6)
    jobs=plan['jobs'];assert len(jobs)<=4000 and len(set(map(tuple,jobs)))==len(jobs)
    for pair in jobs:assert len(pair)==2 and all(type(i) is int for i in pair) and 0<=pair[0]<=pair[1]<241
    coverage={str(i):sum(i in pair for pair in jobs) for i in range(233,241)}
    assert coverage==plan['long_power_job_counts'] and all(n>0 for n in coverage.values())
    for k in range(8):
        i,j=jobs[k];assert j==233+k and i<233 and rules[i]['origin']!='free'
        u,v=rules[i]['lhs'],rules[j]['lhs']
        matches=0
        for offset in range(1-len(v),len(u)):
            start,stop=max(0,offset),min(len(u),offset+len(v))
            if all(u[t]==v[t-offset] for t in range(start,stop)):matches+=1
        assert matches>0
    assert plan['only_target']==7 and plan['target_word']==[5]*4
    assert plan['limits']==dict(search_seconds=5,memory_bytes=536870912,cpu_seconds=6,wall_seconds=10,output_bytes=8388608,max_rules=256,max_jobs=4000,max_word=512,max_factors=2000,max_steps=2000)
    state_path=base/'loaded-state.json'
    if state_path.exists():
        state=json.loads(state_path.read_text())
        assert state['rules']==rules and state['jobs']==jobs and state['queued_jobs']==len(jobs)
    summary=dict(verified_checkpoint_rules=241,forward_original_Q_products=241,reverse_original_Q_products=236,
                 normal_closure_equality_established=True,jobs=len(jobs),long_power_job_counts=coverage,
                 largest_reverse_certificate=max(map(len,reverse.values())))
    return summary,blueprint,rules,plan


def verify(base):
    input_summary,blueprint,initial,plan=inputs(base)
    product=load('independent_products','scripts/check-relation-span-certificate.py')
    rulecheck=load('independent_rules','scripts/check-power-certificate.py')
    q=blueprint['quotient_relators'];target=[5]*4;attempt=json.loads((base/'attempt.json').read_text())
    assert attempt['attempt']==1 and attempt['no_retry'] and attempt['only_target']==7
    for path,digest in attempt['source_sha256'].items():
        assert hashlib.sha256((base/'source'/path).read_bytes()).hexdigest()==digest,path
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    for name,digest in attempt['preparation_sha256'].items():assert hashlib.sha256((base/'preparation'/name).read_bytes()).hexdigest()==digest,name
    for path,digest in attempt['gate_sha256'].items():assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest,path
    resources=json.loads((base/'worker/resources.json').read_text())
    assert resources['limits']==dict(memory_bytes=536870912,cpu_seconds=6,wall_seconds=10.0,output_bytes=8388608) and resources['cleanup_verified']
    events=[];discarded=[]
    for n,line in enumerate((base/'worker/stdout.txt').read_bytes().splitlines(keepends=True),1):
        try:
            if not line.endswith(b'\n'):raise ValueError('incomplete record')
            events.append(json.loads(line))
        except (ValueError,UnicodeDecodeError):discarded.append(n)
    new=[];starts=[];ends=[];success=None;summary=None;incidental={}
    def classify(r):
        w=product.cancel(r['lhs']+product.inv(r['rhs']))
        for i,t in enumerate(blueprint['problem']['relators'],1):
            if w==t:proof=r['factors']
            elif product.inv(w)==t:proof=[[c,j,-s] for c,j,s in reversed(r['factors'])]
            else:continue
            product.check_product(t,q,proof,6);incidental[i]=proof
    for e in events:
        if e['kind']=='header':
            assert e['only_target']==7 and e['loaded_rules']==241 and e['queued_jobs']==len(plan['jobs'])
            assert e['checkpoint_sha256']==attempt['preparation_sha256']['checkpoint.json']
            assert e['schedule_sha256']==attempt['preparation_sha256']['schedule.json']
            assert e['effective_os_limits']=={'RLIMIT_AS':[536870912]*2,'RLIMIT_CPU':[6]*2,'RLIMIT_FSIZE':[8388608]*2}
        elif e['kind']=='new_rule':
            r=e['rule'];assert r['id']==241+len(new);new.append(r)
            assert max(len(r['lhs']),len(r['rhs']))<=512 and len(r['factors'])<=2000
            product.check_product(r['lhs']+product.inv(r['rhs']),q,r['factors'],6);classify(r)
        elif e['kind']=='job_start':
            assert e['ordinal']==len(starts) and e['pair']==plan['jobs'][len(starts)];starts.append(e)
        elif e['kind']=='job_end':
            assert e['ordinal']==len(ends) and e['pair']==plan['jobs'][len(ends)];ends.append(e)
            assert all(x>=0 for x in e['delta'].values())
        elif e['kind']=='target':
            assert e['only_target']==7 and e['answer']['status'] in ['certified','unresolved']
            if e['answer']['status']=='certified':
                product.check_product(target,q,e['answer']['factors'],6);success=e['answer']['factors']
        elif e['kind']=='summary':summary=e
    all_rules=initial+new;assert len(all_rules)<=256;rulecheck.verify_rules(dict(rules=all_rules),q,6)
    if 7 in incidental:success=incidental[7]
    if summary:
        assert summary['search_wall_seconds']<=5.10 and summary['rules']<=256
        c=summary['accounting'];assert c['rule_pair_jobs_processed']==len(starts)<=len(plan['jobs'])<=4000
        assert c['rule_pair_jobs_queued']==len(plan['jobs'])
        assert summary['jobs_completed']==sum(e['completed'] for e in ends)
        for key in ['offset_tests','compatible_overlap_placements','submitted_overlap_equations','oversize_overlap_placements']:
            assert c[key]==sum(e['delta'][key] for e in ends)
        assert c['compatible_overlap_placements']==c['submitted_overlap_equations']+c['oversize_overlap_placements']+c['compatible_placements_not_submitted']
    direct=set([3,5,9,12,15])|set(incidental)
    if success is not None:direct.add(7)
    # Only literal certificates already emitted are classified; no extra goal search.
    linear=load('independent_linear','scripts/check-a4-experiment.py')
    inv=json.loads((ROOT/'docs/evidence/prime7-spanning-preparation/inventory.json').read_text())
    rows=inv['candidate_occurrence_matrix']+inv['existing_zero_identity_matrix']+[[int(j==i-1) for j in range(32)] for i in sorted(direct)]
    witnesses={}
    for i in range(32):
        v=[int(i==j) for j in range(32)];coeff,rank=linear.representation(rows,v)
        if coeff is not None:
            assert [sum(k*r[j] for k,r in zip(coeff,rows))%7 for j in range(32)]==v;witnesses[str(i+1)]=coeff
    certified=sorted(map(int,witnesses))
    equation_inventory=[]
    for r in new:
        w=product.cancel(r['lhs']+product.inv(r['rhs']));conjugator=[]
        while len(w)>1 and w[0]==-w[-1]:conjugator.append(w[0]);w=w[1:-1]
        pure_a=sum(1 if x>0 else -1 for x in w) if w and all(abs(x)==5 for x in w) else None
        equation_inventory.append(dict(id=r['id'],lhs=r['lhs'],rhs=r['rhs'],proof_factors=len(r['factors']),pure_a_exponent=pure_a))
    return dict(new_equation_inventory=equation_inventory,input_verification=input_summary,r7_certified=success is not None,target_certificate=success,
                verified_new_rules=len(new),new_literal_originals=sorted(set(incidental)-{3,5,9,12,15}),
                all_certified_originals=certified,additional_linear_consequences=sorted(set(certified)-direct),
                linear_rank=rank,linear_witnesses=witnesses,full_spanning_established=len(certified)==32,
                summary=summary,resources=resources,discarded_lines=discarded,
                long_power_jobs_started={str(i):sum(i in e['pair'] for e in starts) for i in range(233,241)})


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,required=True);p.add_argument('--inputs-only',action='store_true');p.add_argument('--write-results',action='store_true');a=p.parse_args()
    result=inputs(a.base)[0] if a.inputs_only else verify(a.base)
    if a.write_results:(a.base/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['linear_witnesses','target_certificate','resources']},indent=2))

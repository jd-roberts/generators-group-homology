#!/usr/bin/env python3
"""Small-only three-way benchmarks and fail-closed adversarial tests."""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def cases():
    original=json.loads((ROOT/'tests/fixtures/relation-span-small.json').read_text())
    original.append(dict(name='cyclic7_long_powers',rank=1,prime=7,relators=[[1]*7],candidates=[[1]*14],
                         candidate_membership=[[[[],1,1],[[],1,1]]],expected_spanning=True))
    return original+json.loads((ROOT/'tests/fixtures/power-conjugation-small.json').read_text())


def worker(a):
    case=next(c for c in cases() if c['name']==a.case)
    # Common imports precede the measured search for all three methods.
    import experiments.relation_span, experiments.certified_completion, experiments.certified_power
    method=a.method;start=time.monotonic()
    if 'relators' in case:
        if method=='bfs':
            from experiments.relation_span import produce
            result=produce(case,seconds=1,max_rules=20000,max_states=1000)
        elif method=='completion':
            from experiments.certified_completion import produce
            result=produce(case,seconds=1)
        else:
            from experiments.certified_power import produce
            result=produce(case,seconds=1,**(dict(max_rules=1) if a.limited else {}))
    else:
        base,targets=case['base_relators'],case['targets']
        if method=='bfs':
            from experiments.relation_span import FixedQuotient
            engine=FixedQuotient(base,seconds=1,max_rules=20000,max_states=1000)
            answers=[engine.prove(t) for t in targets];rules=[]
            metrics=dict(rule_count=engine.rule_count,index_truncated=engine.build_limit)
        elif method=='completion':
            from experiments.certified_completion import Completion
            engine=Completion(case['rank'],base,seconds=1)
            initial=[engine.prove(t) for t in targets]
            if not all(t['status']=='certified' for t in initial): engine.complete(targets)
            answers=engine.goal_answers or [old if old['status']=='certified' else engine.prove(t) for old,t in zip(initial,targets)]
            rules=engine.rules
            metrics=dict(rule_count=len(rules),critical_pairs=engine.pairs,truncations=sorted(engine.truncated))
        else:
            from experiments.certified_power import PowerSimplifier
            engine=PowerSimplifier(base,seconds=1)
            answers=[engine.prove(t) for t in targets];rules=engine.rules
            metrics=dict(rule_count=len(rules),operations=engine.operations,truncations=sorted(engine.truncations),
                         inversion_patterns=len(engine.inversions),centrality_patterns=len(engine.centralities))
        result=dict(identity_problem=case,targets=answers,rules=rules,metrics=metrics)
    result['measured_search_seconds']=time.monotonic()-start
    Path(a.record).write_text(json.dumps(result,separators=(',',':'))+'\n')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path);p.add_argument('--worker',action='store_true')
    p.add_argument('--case',choices=[c['name'] for c in cases()]);p.add_argument('--method',choices=['bfs','completion','power'])
    p.add_argument('--record');p.add_argument('--limited',action='store_true');a=p.parse_args()
    if a.worker: worker(a);return
    if a.output is None: p.error('--output required')
    a.output.mkdir(parents=True,exist_ok=False)
    checker=load('independent_power','scripts/check-power-certificate.py')
    rows=[]
    def run(case,method,limited=False):
        stem=case['name']+'.'+method+('.limited' if limited else '')
        record=(a.output/(stem+'.json')).resolve();guard=(a.output/(stem+'.guard')).resolve()
        command=[sys.executable,'experiments/resource_guard.py','--output',str(guard),'--cpu-seconds','3','--wall-seconds','5','--',
                 sys.executable,str(Path(__file__).resolve()),'--worker','--case',case['name'],'--method',method,'--record',str(record)]
        if limited: command.append('--limited')
        process=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=8)
        (a.output/(stem+'.supervisor.txt')).write_text(process.stdout+process.stderr)
        resources=json.loads((guard/'resources.json').read_text())
        assert process.returncode==0 and resources['returncode']==0 and resources['cleanup_verified'],(stem,resources)
        data=json.loads(record.read_text());started=time.monotonic();verdict=checker.verify(data);check_seconds=time.monotonic()-started
        row=dict(case=case['name'],method=method,limited=limited,verdict=verdict,
                 search_seconds=data['measured_search_seconds'],independent_check_seconds=check_seconds,
                 target_factors=sum(len(t.get('factors',[])) for t in data['targets']),
                 target_bytes=len(json.dumps(data['targets'],separators=(',',':')).encode()),
                 rule_factors=sum(len(r['factors']) for r in data.get('rules',[])),
                 rule_bytes=len(json.dumps(data.get('rules',[]),separators=(',',':')).encode()),
                 record_bytes=record.stat().st_size,targets=[{k:v for k,v in t.items() if k!='factors'} for t in data['targets']],
                 metrics=data.get('metrics',dict(rule_count=data.get('rule_count',0))),resources=resources,command=command)
        return data,row
    for case in cases():
        for method in ['bfs','completion','power']:
            data,row=run(case,method);verdict=row['verdict']
            if 'relators' in case:
                expected='proved' if case['expected_spanning'] else 'disproved'
                if not(case['name']=='cyclic7_long_powers' and method=='bfs'):
                    assert verdict['spanning']==expected,(case['name'],method,verdict)
            elif not case['expected_identity']:
                assert verdict['proved_nonmembers']==list(range(1,len(case['targets'])+1))
                assert not verdict['certified_targets']
            elif method=='power':
                assert verdict['all_targets']=='proved',(case['name'],verdict)
            rows.append(row);print(case['name'],method,verdict,flush=True)
    checks=[]
    # An unrelated eight-row toy base tests a noncontiguous, permuted adapter.
    from experiments.restricted_identity import subset, map_record
    from experiments.certified_power import PowerSimplifier
    full=[[] for _ in range(8)];full[6]=[1]*6;full[1]=[1]*9
    indices=[7,2];local=subset(full,indices)
    adapter_engine=PowerSimplifier(local)
    raw=dict(rules=adapter_engine.rules,targets=[adapter_engine.prove([1]*3)])
    mapped=map_record(raw,indices)
    checker.products.check_product([1]*3,full,json.loads(json.dumps(mapped['targets'][0]['factors'])),1)
    for rule in mapped['rules']:
        checker.products.check_product(list(rule['lhs']),full,json.loads(json.dumps(rule['factors'])),1)
    checks.append('permuted noncontiguous adapter products checked against original base')
    try: subset(full,[7,7])
    except ValueError: checks.append('duplicate adapter indices rejected')
    else: raise AssertionError('duplicate indices accepted')
    try: map_record(raw,[99])
    except ValueError: checks.append('out-of-range local proof index rejected')
    else: raise AssertionError('missing local index accepted')
    def reject(name,data):
        try: checker.verify(data)
        except (ValueError,KeyError,IndexError,TypeError): checks.append(name);return
        raise AssertionError('accepted '+name)
    good=json.loads((a.output/'dihedral_power_control.power.json').read_text())
    bad=copy.deepcopy(good);bad['targets'][0]['factors'][0][2]*=-1;reject('changed target factor sign',bad)
    bad=copy.deepcopy(good);r=next(r for r in bad['rules'] if r['origin']=='inversion_and_centrality');r['factors']=[];reject('uncertified inversion-centrality consequence',bad)
    bad=copy.deepcopy(good);bad['identity_problem']['base_relators'][1]=[2,2];reject('reuse under another centrality relation',bad)
    bad=copy.deepcopy(good);r=next(r for r in bad['rules'] if r['factors']);r['factors'][0][0]=[3];reject('invalid conjugator generator',bad)
    bad=copy.deepcopy(good);r=bad['rules'][0];r['lhs'],r['rhs']=r['rhs'],r['lhs'];reject('increasing orientation',bad)
    bad=copy.deepcopy(good);bad['targets'][0]['status']='nonmember';reject('search asserted nonmembership',bad)
    # Literal noncommutative counterexamples have independently checked images.
    checks += [c['name']+' finite obstruction verified' for c in cases() if c.get('expected_identity') is False]
    limited_case=next(c for c in cases() if c['name']=='C3_power_basis')
    data,row=run(limited_case,'power',True)
    assert row['verdict']['spanning']=='unresolved';checks.append('rule-limited true positive unresolved');rows.append(row)
    sources=['experiments/certified_power.py','scripts/check-power-certificate.py','scripts/test-certified-power.py',
             'tests/fixtures/power-conjugation-small.json','experiments/restricted_identity.py','experiments/certified_completion.py','experiments/relation_span.py',
             'scripts/check-relation-span-certificate.py','experiments/resource_guard.py','tests/fixtures/relation-span-small.json']
    summary=dict(all_passed=True,results=rows,acceptance_checks=checks,
                 source_sha256={s:hashlib.sha256((ROOT/s).read_bytes()).hexdigest() for s in sources},
                 notes='One measurement per method/case; functional comparison, not a statistically meaningful speedup claim. Positive plain-group examples need not be solved by every incomplete method.')
    (a.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('PASS: twenty small cases, three methods, independent rules/targets and adversarial checks.',flush=True)


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Small/formal tests only. No arithmetic input or target search is loaded."""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from experiments.relation_span import reduce_word as red,inverse as inv,quotient
from experiments.certified_completion import Completion
from experiments.counted_completion import CountedCompletion
from experiments.a4_structure import commuting_equations


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    checker=load('independent','scripts/check-relation-span-certificate.py');checks=[]
    # Formal lemma test: arbitrary free generators, not the arithmetic quotient.
    aa,z,u1,u2,u3,b1=(5,),(1,),(2,),(3,),(4,),(6,)
    c=(-1,)*3+b1+(1,)*3;b=red(c+(-5,));t=(5,5)
    comm=lambda x,y:red(inv(x)+inv(y)+x+y)
    r=lambda u:red(u+aa+u+inv(aa))
    base=[()]*236
    for i,w in {225:r(z),227:r(u1),228:red(b*3+t),75:comm(u2,r(u2)),139:comm(aa,r(u2)),100:comm(u3,r(u3)),132:comm(aa,r(u3))}.items():base[i-1]=w
    lemmas=json.loads(json.dumps(commuting_equations()))
    for lemma in lemmas:checker.check_product(lemma['lhs']+checker.inv(lemma['rhs']),[list(w) for w in base],lemma['factors'],6)
    checks.append('all twenty signed centrality equations verified as formal free identities')
    bad=copy.deepcopy(lemmas[0]);bad['factors'].pop()
    try:checker.check_product(bad['lhs']+checker.inv(bad['rhs']),[list(w) for w in base],bad['factors'],6)
    except ValueError:checks.append('missing centrality factor rejected')
    else:raise AssertionError('bad lemma accepted')
    (a.output/'formal-lemmas.json').write_text(json.dumps(dict(base_relators=base,equations=lemmas),separators=(',',':'))+'\n')
    fixtures=json.loads((ROOT/'tests/fixtures/relation-span-small.json').read_text())
    comparisons=[]
    for case in fixtures:
        relations,_=quotient(case['rank'],case['prime'],case['relators'],case['candidates'])
        old=Completion(case['rank'],relations,seconds=1);old.complete()
        new=CountedCompletion(case['rank'],relations,seconds=1);new.complete()
        assert json.loads(json.dumps(old.rules))==json.loads(json.dumps(new.rules)),case['name']
        for rule in new.rules:
            checker.check_product(list(rule['lhs'])+checker.inv(rule['rhs']),[list(w) for w in relations],json.loads(json.dumps(rule['factors'])),case['rank'])
        comparisons.append(dict(case=case['name'],rules=new.rules,accounting=new.accounting()))
    checks.append('ten small fixtures: counted subclass retains exactly parent rules/proofs')
    class Recorder(CountedCompletion):
        def equation(self,lhs,rhs,proof,origin):self.recorded.append((lhs,rhs,proof))
    probe=Recorder(1,[],seconds=1);probe.recorded=[]
    probe.overlaps(dict(lhs=(1,1,1),rhs=(),factors=[((),1,1)]),dict(lhs=(1,1),rhs=(),factors=[((),2,1)]))
    assert probe.offset_tests==probe.compatible_overlap_placements==probe.submitted_overlap_equations==4
    for lhs,rhs,proof in probe.recorded:checker.check_product(list(lhs)+checker.inv(rhs),[[1]*3,[1]*2],json.loads(json.dumps(proof)),1)
    checks.append('one pair has exactly four overlap placements; products independently verified')
    sources=['experiments/a4_structure.py','experiments/counted_completion.py','scripts/test-a4-infrastructure.py',
             'experiments/certified_completion.py','experiments/certified_power.py','experiments/resource_guard.py']
    (a.output/'summary.json').write_text(json.dumps(dict(all_passed=True,checks=checks,comparisons=comparisons,
        counter_probe=probe.accounting(),source_sha256={s:hashlib.sha256((ROOT/s).read_bytes()).hexdigest() for s in sources}),indent=2)+'\n')
    print('PASS: formal centrality products, adversarial factor deletion, ten parent comparisons, separate four-placement accounting.')


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Independent products-only checker. Imports no simplifier or search code."""
import argparse
import importlib.util
import json
from pathlib import Path

spec=importlib.util.spec_from_file_location('products',Path(__file__).with_name('check-relation-span-certificate.py'))
products=importlib.util.module_from_spec(spec);spec.loader.exec_module(products)


def verify_rules(record, base, rank):
    for i,rule in enumerate(record.get('rules',[])):
        lhs,rhs=rule['lhs'],rule['rhs']
        if rule['id']!=i or not lhs or (len(lhs),tuple(lhs)) <= (len(rhs),tuple(rhs)):
            raise ValueError('invalid orientation or rule index')
        if any(type(x) is not int or not 1<=abs(x)<=rank for x in lhs+rhs):
            raise ValueError('letter outside the original free group')
        products.check_product(lhs+products.inv(rhs),base,rule['factors'],rank)
    return len(record.get('rules',[]))


def verify(record):
    if 'problem' in record:
        result=products.verify(record)
        base=products.make_quotient(record['problem']);rank=record['problem']['rank']
    else:
        case=record['identity_problem'];rank=case['rank'];base=case['base_relators']
        if any(type(x) is not int or not 1<=abs(x)<=rank for w in base+case['targets'] for x in w):
            raise ValueError('invalid input word')
        if len(case['targets'])!=len(record['targets']):
            raise ValueError('wrong target inventory')
        certified=[]
        for i,(word,answer) in enumerate(zip(case['targets'],record['targets']),1):
            if answer['status']=='certified':
                products.check_product(word,base,answer['factors'],rank);certified.append(i)
            elif answer['status']!='unresolved':
                raise ValueError('search cannot declare nonmembership')
        negative=[]
        if case.get('obstruction'):
            images=case['obstruction']['generator_permutations']
            if len(images)!=rank: raise ValueError('wrong finite-image rank')
            identity=list(range(len(images[0])))
            if any(products.permutation_word(w,images)!=identity for w in base):
                raise ValueError('finite image does not satisfy all input relations')
            negative=[i for i,w in enumerate(case['targets'],1) if products.permutation_word(w,images)!=identity]
            if set(negative)&set(certified): raise ValueError('contradictory claims')
        result=dict(certified_targets=certified,proved_nonmembers=negative,
                    all_targets='proved' if len(certified)==len(case['targets']) else 'disproved' if negative else 'unresolved')
    return dict(**result,verified_rules=verify_rules(record,base,rank))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('record',type=Path);a=p.parse_args()
    print(json.dumps(verify(json.loads(a.record.read_text())),indent=2))

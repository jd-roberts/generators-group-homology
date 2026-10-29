#!/usr/bin/env python3
"""Independent restricted-control replay; never imports any search or adapter."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
BLUEPRINT_SHA='d33076b1c1b20c9950349645e77c0dbcebe9c8e326ba77dd041b6b696b134a60'


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def verify(base):
    product=load('independent_products','scripts/check-relation-span-certificate.py')
    rule_checker=load('independent_rules','scripts/check-power-certificate.py')
    frozen=(base/'full-input.json.gz').read_bytes()
    if hashlib.sha256(frozen).hexdigest()!=BLUEPRINT_SHA: raise ValueError('wrong frozen fixed quotient')
    blueprint=json.loads(gzip.decompress(frozen))
    previous=product.verify(blueprint)
    if previous['certified_targets']!=[3,5,9,12,15]: raise ValueError('previous certificates failed')
    full=product.make_quotient(blueprint['problem']);source=json.loads((base/'control-input.json').read_text())
    indices=source['original_indices'];rank=blueprint['problem']['rank'];target=blueprint['problem']['relators'][11]
    if indices!=[225,140,204] or source['target']!=target or target!=[1]*7 or source['rank']!=rank:
        raise ValueError('wrong restricted target or relation indices')
    if source['base_relators']!=[full[i-1] for i in indices]: raise ValueError('wrong restricted relation words')
    if source['base_relators']!=[[1,5,1,-5],[-5]+[-1]*7+[5]+[1]*7,[1]*49]: raise ValueError('source interpretation changed')
    resources=json.loads((base/'worker/resources.json').read_text())
    if resources['limits']!={'memory_bytes':536870912,'cpu_seconds':3,'wall_seconds':5.0,'output_bytes':8388608} or not resources['cleanup_verified']:
        raise ValueError('incorrect OS controls')
    events=[];discarded=[]
    for line in (base/'worker/stdout.txt').read_bytes().splitlines(keepends=True):
        try:
            if not line.endswith(b'\n'): raise ValueError('incomplete record')
            events.append(json.loads(line))
        except (ValueError,UnicodeDecodeError): discarded.append(len(line))
    outcomes={};rules=0;pairs=0
    for event in events:
        if event['kind']=='header':
            if event['effective_os_limits']!={'RLIMIT_AS':[536870912]*2,'RLIMIT_CPU':[3]*2,'RLIMIT_FSIZE':[8388608]*2}:
                raise ValueError('effective OS limits differ')
            if event['original_indices']!=indices or event['target']!=target or event['search_seconds']!=1 or event['combined_rule_limit']!=128:
                raise ValueError('wrong worker header')
        if event['kind']!='method_result':continue
        local,mapped=event['local'],event['mapped'];method=local['method']
        if method not in ['power','completion'] or method in outcomes: raise ValueError('duplicate/unexpected method')
        if len(local['targets'])!=1 or len(mapped['targets'])!=1 or len(local['rules'])!=len(mapped['rules']): raise ValueError('extra targets/rules')
        def mapped_proof(proof):
            result=[]
            for q,i,s in proof:
                if type(i) is not int or not 1<=i<=3: raise ValueError('out-of-subset input relation')
                result.append([q,indices[i-1],s])
            return result
        for a,b in zip(local['rules'],mapped['rules']):
            expected=dict(a,factors=mapped_proof(a['factors']))
            if b!=expected: raise ValueError('incorrect rule reindexing')
        for a,b in zip(local['targets'],mapped['targets']):
            expected=dict(a,factors=mapped_proof(a['factors'])) if a['status']=='certified' else a
            if b!=expected: raise ValueError('incorrect target reindexing')
            if a['status']=='certified':
                product.check_product(target,source['base_relators'],a['factors'],rank)
                product.check_product(target,full,b['factors'],rank)
            elif a['status']!='unresolved': raise ValueError('invalid negative inference')
        rule_checker.verify_rules(local,source['base_relators'],rank)
        rule_checker.verify_rules(mapped,full,rank)
        limits=local['limits']
        if limits['seconds']>1 or limits['max_rules']>128 or limits['max_word']!=128 or limits['max_factors']!=2000 or limits['max_steps']!=2000:
            raise ValueError('search limits changed')
        if method=='completion':
            pairs=local['metrics']['critical_pairs']
            if limits['max_pairs']!=1000 or pairs>1000 or local['metrics']['queued_pairs']>1000: raise ValueError('critical-pair limit changed')
        rules+=len(local['rules']);outcomes[method]=dict(answer=mapped['targets'][0],verified_rules=len(mapped['rules']),metrics=local['metrics'])
    if rules>128: raise ValueError('combined retained-rule limit exceeded')
    summary=[e for e in events if e['kind']=='summary']
    if summary and (len(summary)!=1 or summary[0]['search_wall_seconds']>1.05 or not summary[0]['no_other_targets']):
        raise ValueError('search time or target inventory invalid')
    return dict(methods=outcomes,combined_verified_rules=rules,critical_pairs=pairs,
                discarded_record_bytes=discarded,resources=resources,
                original_target=12,new_certified_original_targets=[],
                total_certified_original_targets=[3,5,9,12,15],full_spanning_established=False,
                note='Only known R12 was attempted. Missing/incomplete method outputs are unresolved, not obstructions.')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,required=True);a=p.parse_args()
    print(json.dumps(verify(a.base),indent=2))

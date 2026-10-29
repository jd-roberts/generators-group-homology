#!/usr/bin/env python3
"""Replay new power evidence, source hashes and products. Never run searches."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--small',type=Path,required=True);p.add_argument('--control',type=Path,required=True);a=p.parse_args()
    checker=load('independent_power','scripts/check-power-certificate.py')
    summary=json.loads((a.small/'summary.json').read_text())
    assert summary['all_passed'] and len(summary['results'])==61
    for path,digest in summary['source_sha256'].items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    rules=0;certified=0
    for row in summary['results']:
        stem=row['case']+'.'+row['method']+('.limited' if row['limited'] else '')
        record=json.loads((a.small/(stem+'.json')).read_text())
        verdict=checker.verify(record);assert verdict==row['verdict']
        usage=json.loads((a.small/(stem+'.guard/resources.json')).read_text())
        assert usage==row['resources'] and usage['cleanup_verified'] and usage['returncode']==0
        rules+=verdict['verified_rules'];certified+=len(verdict['certified_targets'])
    attempt=json.loads((a.control/'control-attempt.json').read_text())
    assert attempt['authorized_control']==1 and attempt['no_retry'] and attempt['target']==12 and attempt['indices']==[225,140,204]
    for path,digest in attempt['source_sha256'].items():
        assert hashlib.sha256((a.control/'source'/path).read_bytes()).hexdigest()==digest,path
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    for path,digest in attempt['gate_sha256'].items():assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest,path
    control=load('independent_control','scripts/check-power-control.py').verify(a.control)
    assert control==json.loads((a.control/'result.json').read_text())
    records=[json.loads(line) for line in (a.control/'worker/stdout.txt').read_text().splitlines()]
    assert [e['method'] for e in records if e['kind']=='method_start']==['power','completion']
    assert len([e for e in records if e['kind']=='header'])==1 and len([e for e in records if e['kind']=='summary'])==1
    for event in records:
        if event['kind']!='method_result':continue
        data=event['mapped']
        for rule in data['rules']:
            assert max(len(rule['lhs']),len(rule['rhs']))<=128 and len(rule['factors'])<=2000
        for target in data['targets']:
            assert len(target.get('factors',[]))<=2000
    assert control['resources']['returncode']==0 and control['resources']['termination']=='completed'
    print(json.dumps(dict(small_records=61,small_verified_rules=rules,small_certified_target_occurrences=certified,
                          single_control_attempt=True,control_verified_rules=control['combined_verified_rules'],
                          control_methods={k:v['answer']['status'] for k,v in control['methods'].items()},
                          newly_certified_arithmetic_targets=[],full_spanning=False),indent=2))


if __name__=='__main__':main()

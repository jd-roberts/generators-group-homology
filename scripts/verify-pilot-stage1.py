#!/usr/bin/env python3
"""Replay all existing checks and small workers, then record a fail-closed gate."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--base',type=Path,required=True)
    p.add_argument('--gap',default='gap')
    a=p.parse_args();stage=a.base/'stage1'
    safety=json.loads((stage/'safety/summary.json').read_text())
    assert safety['all_passed'] and len(safety['tests'])==8,'safety gate failed; abort pilot'
    for f,h in safety['source_sha256'].items():
        assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,'safety-tested source changed'
    out=stage/'verification';out.mkdir(parents=True,exist_ok=False)
    summary={'all_passed':False,'checks':[],'small_workers':[]}
    try:
        checks=[
            ('benchmark_regressions',[sys.executable,'tests/test_benchmark.py'],12),
            ('formal_corrections',[sys.executable,'scripts/verify-prime7-corrections.py','--gap',a.gap],8),
            ('presentation_certificates',[sys.executable,'scripts/verify-prime7-presentation.py','--gap',a.gap],12),
            ('spanning_inventory',[sys.executable,'scripts/check-prime7-spanning-inventory.py','--gap',a.gap],12),
            ('small_suite',[sys.executable,'scripts/test-relation-span.py','--gap',a.gap,'--output',str((out/'small-suite').resolve())],45),
        ]
        for name in ['smoke','historical-h1','presentation-sanity','identification-impact','paper-provenance','prime7-proof-check']:
            checks.append((name,[a.gap,'-q','-b','--quitonbreak',f'tests/{name}.g'],5))
        for name,cmd,timeout in checks:
            run=subprocess.run(cmd,cwd=ROOT,text=True,capture_output=True,timeout=timeout)
            (out/(name+'.stdout.txt')).write_text(run.stdout)
            (out/(name+'.stderr.txt')).write_text(run.stderr)
            assert run.returncode==0,(name,run.stdout,run.stderr)
            assert not any(x in run.stdout+run.stderr for x in ['Syntax error:','Error,','Traceback (most recent call last)']),name
            summary['checks'].append({'name':name,'command':cmd,'timeout':timeout,'returncode':run.returncode})
            print('PASS',name,flush=True)
        checker=module('independent_checker','scripts/check-relation-span-certificate.py')
        fixtures=json.loads((ROOT/'tests/fixtures/relation-span-small.json').read_text())
        for name in ['C3_power_basis','V4_conjugated','V4_missing_commutator']:
            case=next(c for c in fixtures if c['name']==name)
            inp=out/(name+'.input.json');inp.write_text(json.dumps(case)+'\n')
            guard=out/(name+'.guard')
            cmd=[sys.executable,'experiments/resource_guard.py','--output',str(guard.resolve()),'--',
                 sys.executable,'-u','experiments/spanning_worker.py','--input',str(inp.resolve()),
                 '--targets',','.join(str(i) for i in range(1,len(case['relators'])+1)),'--tag','small-verification']
            run=subprocess.run(cmd,cwd=ROOT,text=True,capture_output=True,timeout=14)
            assert run.returncode==0,(name,run.stdout,run.stderr)
            resources=json.loads((guard/'resources.json').read_text())
            assert resources['termination']=='completed' and resources['cleanup_verified']
            records=[json.loads(line) for line in (guard/'stdout.txt').read_text().splitlines()]
            assert records[0]['kind']=='header' and records[-1]['kind']=='summary'
            base=json.loads((out/'small-suite'/(name+'.json')).read_text())
            for event in records:
                if event['kind']=='target':
                    base['targets'][event['target']-1]=event['answer']
                    assert event['answer'].get('states',0)<=1000
                    assert event['answer'].get('max_word_length',0)<=len(case['relators'][event['target']-1])+6
            result=checker.verify(base)
            assert result['spanning']==('proved' if case['expected_spanning'] else 'disproved')
            (out/(name+'.checked.json')).write_text(json.dumps(base,indent=2)+'\n')
            summary['small_workers'].append({'name':name,'checked':result,'resources':resources})
            print('PASS limited worker',name,flush=True)
        summary['all_passed']=True
    except BaseException as error:
        summary['failure']=repr(error);raise
    finally:
        paths=['experiments/resource_guard.py','tests/resource_probes.py','scripts/test-resource-guard.py',
               'experiments/spanning_worker.py','experiments/relation_span.py','scripts/verify-pilot-stage1.py',
               'scripts/check-relation-span-certificate.py']
        summary['source_sha256']={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in paths}
        summary['safety_summary_sha256']=hashlib.sha256((stage/'safety/summary.json').read_bytes()).hexdigest()
        (stage/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('PASS: Stage 1 safety, previous certificates, old controls and constrained-worker checks.')


if __name__=='__main__':
    main()

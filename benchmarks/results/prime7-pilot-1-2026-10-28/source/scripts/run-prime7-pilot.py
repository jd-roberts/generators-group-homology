#!/usr/bin/env python3
"""ONE authorized pilot after a successful, unchanged Stage 1 gate. No retries."""
import argparse
import copy
import datetime
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
SELECTED=[1,2,4,6,7,8,10,11,13,14,18,26,28,29,30]


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def exclusive_json(path,value):
    with path.open('x') as stream:
        json.dump(value,stream,indent=2);stream.write('\n')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,required=True)
    a=parser.parse_args();base=a.base.resolve()
    marker=base/'pilot-attempt.json'
    if marker.exists():
        parser.error('one pilot was already reserved or launched; automatic retries are forbidden')
    safety=json.loads((base/'stage1/safety/summary.json').read_text())
    gate=json.loads((base/'stage1/verification-summary.json').read_text())
    assert safety['all_passed'] and len(safety['tests'])==8 and gate['all_passed'],'Stage 1 failed; abort'
    for record in [safety,gate]:
        for path,digest in record['source_sha256'].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,('Stage 1 source changed',path)
    assert hashlib.sha256((base/'stage1/safety/summary.json').read_bytes()).hexdigest()==gate['safety_summary_sha256']
    inventory=json.loads((ROOT/'docs/evidence/prime7-spanning-preparation/inventory.json').read_text())
    assert inventory['sufficient_future_targets']==SELECTED
    original_input=ROOT/'docs/evidence/prime7-spanning-preparation/fixed-quotient-blueprint.json.gz'
    proposal=json.loads((ROOT/'docs/evidence/prime7-spanning-preparation/pilot-proposal.json').read_text())
    raw=original_input.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==proposal['quotient_blueprint_sha256']
    blueprint=json.loads(gzip.decompress(raw))
    checker=module('independent_checker','scripts/check-relation-span-certificate.py')
    assert checker.verify(blueprint)['certified_targets']==[3,5,9,12,15]
    paths=['experiments/resource_guard.py','experiments/spanning_worker.py','experiments/relation_span.py',
           'scripts/run-prime7-pilot.py','scripts/check-relation-span-certificate.py',
           'scripts/prepare-prime7-spanning.py','docs/evidence/prime7-spanning-preparation/inventory.json']
    sources={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths}
    attempt={'authorized_attempt':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
             'input_sha256':hashlib.sha256(raw).hexdigest(),'selected_targets':SELECTED,
             'stage1_gate_sha256':hashlib.sha256((base/'stage1/verification-summary.json').read_bytes()).hexdigest(),
             'source_sha256':sources,'no_retry':True}
    # Atomic reservation precedes launch. Even a launch failure consumes this attempt.
    exclusive_json(marker,attempt)
    frozen=base/'pilot-input.json.gz'
    with frozen.open('xb') as stream: stream.write(raw)
    source_dir=base/'source'
    for path in paths:
        destination=source_dir/path;destination.parent.mkdir(parents=True,exist_ok=True)
        destination.write_bytes((ROOT/path).read_bytes())
    guard=base/'pilot'
    command=[sys.executable,'experiments/resource_guard.py','--output',str(guard),
             '--memory-mib','512','--cpu-seconds','6','--wall-seconds','10','--output-bytes',str(8*1024*1024),
             '--',sys.executable,'-u','experiments/spanning_worker.py','--input',str(frozen),
             '--targets',','.join(map(str,SELECTED)),'--tag','prime7-authorized-pilot']
    run=subprocess.run(command,cwd=ROOT,text=True,capture_output=True,timeout=14)
    (base/'pilot-supervisor.stdout.txt').write_text(run.stdout)
    (base/'pilot-supervisor.stderr.txt').write_text(run.stderr)
    assert run.returncode==0,('supervisor failed; no retry',run.stdout,run.stderr)
    resources=json.loads((guard/'resources.json').read_text())
    assert resources['cleanup_verified']
    assert resources['limits']=={'memory_bytes':512*1024*1024,'cpu_seconds':6,'wall_seconds':10.0,'output_bytes':8*1024*1024}
    events=[];discarded=[]
    for i,line in enumerate((guard/'stdout.txt').read_bytes().splitlines(keepends=True),1):
        try:
            if not line.endswith(b'\n'): raise ValueError('incomplete final record')
            events.append(json.loads(line))
        except (ValueError,UnicodeDecodeError) as error:
            discarded.append({'line':i,'reason':str(error)})
    headers=[r for r in events if r.get('kind')=='header']
    if headers:
        assert len(headers)==1 and headers[0]['selected_targets']==SELECTED and headers[0]['input_sha256']==attempt['input_sha256']
    combined=copy.deepcopy(blueprint)
    new_certificates=[];invalid=[];answers={}
    # Independently verify EVERY complete successful record before accepting it.
    for event in events:
        if event.get('kind')!='target': continue
        target=event['target'];answer=event['answer']
        assert target in SELECTED and answer.get('states',0)<=1000
        assert answer.get('max_word_length',0)<=len(blueprint['problem']['relators'][target-1])+6
        if answer['status']=='certified':
            try:
                checker.check_product(blueprint['problem']['relators'][target-1],blueprint['quotient_relators'],answer['factors'],6)
                combined['targets'][target-1]=answer
                if target not in new_certificates: new_certificates.append(target)
            except (ValueError,IndexError,KeyError) as error:
                invalid.append({'target':target,'error':repr(error)})
        elif answer['status']=='unresolved' and target not in new_certificates:
            combined['targets'][target-1]=answer
        else:
            assert answer['status']=='unresolved'
        answers[target]=answer
    for target in SELECTED:
        if target not in answers:
            combined['targets'][target-1]={'status':'unresolved','reason':'no_complete_result_before_'+resources['termination']}
    direct=checker.verify(combined)
    exclusive_json(base/'verified-products.json',combined)
    verification=subprocess.run([sys.executable,'scripts/check-relation-span-certificate.py',str(base/'verified-products.json')],cwd=ROOT,capture_output=True,text=True,timeout=10)
    (base/'independent-verifier.stdout.txt').write_text(verification.stdout)
    (base/'independent-verifier.stderr.txt').write_text(verification.stderr)
    assert verification.returncode==0 and not verification.stderr
    assert json.loads(verification.stdout)==direct
    linear=module('static_linear','scripts/prepare-prime7-spanning.py')
    rows=inventory['candidate_occurrence_matrix']+inventory['existing_zero_identity_matrix']
    direct_targets=direct['certified_targets']
    rows += [[int(j==i-1) for j in range(32)] for i in direct_targets]
    covered=[];witnesses={}
    for i in range(32):
        witness,rank=linear.representation(rows,[int(i==j) for j in range(32)])
        if witness is not None:
            covered.append(i+1);witnesses[str(i+1)]=witness
    result={'attempts':1,'selected_targets':SELECTED,'new_direct_certificates':sorted(new_certificates),
            'all_direct_certificates':direct_targets,'additional_linear_consequences':sorted(set(covered)-set(direct_targets)),
            'certified_original_targets':covered,'certified_original_count':len(covered),
            'unresolved_selected_targets':sorted(set(SELECTED)-set(covered)),
            'unresolved_original_targets':sorted(set(range(1,33))-set(covered)),
            'full_spanning_established':len(covered)==32,'linear_combination_witnesses':witnesses,
            'linear_row_order':'12 candidate rows,46 verified zero rows,unit rows for all_direct_certificates in listed order',
            'formal_residual_dimension_upper_bound':32-rank,'resources':resources,
            'index_events':[r for r in events if r.get('kind')=='index'],
            'search_summary':[r for r in events if r.get('kind')=='summary'],
            'discarded_records':discarded,'invalid_complete_certificates':invalid,
            'termination_is_not_nonmembership':True,'no_additional_trial_authorized_or_launched':True}
    exclusive_json(base/'result.json',result)
    assert not invalid,'invalid complete proof encountered; no retry permitted'
    print(json.dumps({k:result[k] for k in ['new_direct_certificates','additional_linear_consequences','certified_original_count','unresolved_selected_targets','full_spanning_established']},indent=2))


if __name__=='__main__':
    main()

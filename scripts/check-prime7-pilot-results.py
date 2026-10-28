#!/usr/bin/env python3
"""Independent post-run replay. Never imports or invokes the search worker."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--base',type=Path,required=True)
    a=p.parse_args();base=a.base
    attempt=json.loads((base/'pilot-attempt.json').read_text())
    result=json.loads((base/'result.json').read_text())
    assert attempt['authorized_attempt']==result['attempts']==1 and attempt['no_retry']
    for path,digest in attempt['source_sha256'].items():
        assert hashlib.sha256((base/'source'/path).read_bytes()).hexdigest()==digest,path
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    frozen=(base/'pilot-input.json.gz').read_bytes()
    assert hashlib.sha256(frozen).hexdigest()==attempt['input_sha256']
    safety=json.loads((base/'stage1/safety/summary.json').read_text())
    gate=json.loads((base/'stage1/verification-summary.json').read_text())
    assert safety['all_passed'] and gate['all_passed']
    assert hashlib.sha256((base/'stage1/verification-summary.json').read_bytes()).hexdigest()==attempt['stage1_gate_sha256']
    for record in [safety,gate]:
        for path,digest in record['source_sha256'].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    r=result['resources']
    assert r==json.loads((base/'pilot/resources.json').read_text())
    assert r['limits']=={'memory_bytes':536870912,'cpu_seconds':6,'wall_seconds':10.0,'output_bytes':8388608}
    assert r['cleanup_verified'] and r['returncode']==0 and r['termination']=='completed'
    assert r['worker']['user_seconds']+r['worker']['system_seconds']<6
    assert r['wall_seconds']<10 and r['worker']['max_rss_kib']<512*1024
    assert r['stdout_bytes']<=8388608 and r['stderr_bytes']<=8388608
    events=[json.loads(line) for line in (base/'pilot/stdout.txt').read_text().splitlines()]
    header=events[0];summary=events[-1]
    assert header['kind']=='header' and header['selected_targets']==attempt['selected_targets']
    assert header['input_sha256']==attempt['input_sha256']
    assert summary['kind']=='summary' and summary['index_builds']==1
    assert summary['search_wall_seconds']<=5 and summary['rule_instances']<=20000
    targets=[e for e in events if e['kind']=='target']
    assert [e['target'] for e in targets]==attempt['selected_targets']
    blueprint=json.loads(gzip.decompress(frozen))
    for e in targets:
        answer=e['answer']
        assert answer.get('states',0)<=1000
        assert answer.get('max_word_length',0)<=len(blueprint['problem']['relators'][e['target']-1])+6
    products=json.loads((base/'verified-products.json').read_text())
    assert products['problem']==blueprint['problem'] and products['quotient_relators']==blueprint['quotient_relators']
    checker=load('independent_product_checker','scripts/check-relation-span-certificate.py')
    direct=checker.verify(products)
    assert direct['certified_targets']==result['all_direct_certificates'] and not direct['proved_nonmembers']
    # Each raw claimed success, not just the selected combined record, is checked.
    successes=[]
    for e in targets:
        if e['answer']['status']=='certified':
            checker.check_product(blueprint['problem']['relators'][e['target']-1],blueprint['quotient_relators'],e['answer']['factors'],6)
            successes.append(e['target'])
    assert sorted(successes)==result['new_direct_certificates']
    inv=json.loads((base/'source/docs/evidence/prime7-spanning-preparation/inventory.json').read_text())
    rows=inv['candidate_occurrence_matrix']+inv['existing_zero_identity_matrix']
    rows += [[int(j==i-1) for j in range(32)] for i in direct['certified_targets']]
    linear=load('independent_rank_checker','scripts/check-prime7-spanning-inventory.py')
    rank=linear.rank(rows)
    closure=[i+1 for i in range(32) if linear.rank(rows+[[int(i==j) for j in range(32)]])==rank]
    assert closure==result['certified_original_targets']
    for key,coefficients in result['linear_combination_witnesses'].items():
        assert len(coefficients)==len(rows)
        assert [sum(c*r[j] for c,r in zip(coefficients,rows))%7 for j in range(32)]==[int(j==int(key)-1) for j in range(32)]
    assert result['unresolved_original_targets']==sorted(set(range(1,33))-set(closure))
    assert result['full_spanning_established']==(len(closure)==32)
    assert result['additional_linear_consequences']==sorted(set(closure)-set(direct['certified_targets']))
    assert not result['invalid_complete_certificates'] and not result['discarded_records']
    # Recheck no recorded probe child/worker survived with the same PID/start time.
    for pidfile in (base/'stage1/safety').glob('*.pids.json'):
        for record in json.loads(pidfile.read_text()).values():
            path=Path(f"/proc/{record['pid']}/stat")
            if path.exists():
                assert int(path.read_text().rsplit(')',1)[1].split()[19])!=record['start']
    for record in r['observed_processes']:
        path=Path(f"/proc/{record['pid']}/stat")
        if path.exists():
            assert int(path.read_text().rsplit(')',1)[1].split()[19])!=record['start_ticks']
    print('PASS: one attempt, Stage 1 gate, exact input/source hashes, all resource bounds, cleanup, free products and linear consequences.')
    print('New certificates:',result['new_direct_certificates'])
    print('Certified originals:',closure,'; full spanning:',result['full_spanning_established'])


if __name__=='__main__':
    main()

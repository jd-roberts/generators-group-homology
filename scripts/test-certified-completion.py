#!/usr/bin/env python3
"""Whitelisted small-only experiments, each isolated by the existing OS guard."""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def fixtures():
    cases = json.loads((ROOT/'tests/fixtures/relation-span-small.json').read_text())
    # C7 is a finite cyclic toy, NOT the arithmetic-group presentation.
    cases.append(dict(name='cyclic7_long_powers', rank=1, prime=7, relators=[[1]*7],
                      candidates=[[1]*14], candidate_membership=[[[[],1,1],[[],1,1]]], expected_spanning=True))
    return cases


def worker(a):
    case = next(c for c in fixtures() if c['name'] == a.case)
    if a.method == 'bfs':
        from experiments.relation_span import produce
        options = dict(seconds=1, max_rules=20000, max_states=1000)
    else:
        from experiments.certified_completion import produce
        options = dict(seconds=1, max_rules=256, max_pairs=4000, max_word=128, max_factors=2000)
        if a.case == 'C3_power_basis' and a.limited:
            options['max_rules'] = 2  # Only the two free cancellation rules fit.
    started = time.monotonic()
    result = produce(case, **options)
    result['measured_search_wall_seconds'] = time.monotonic()-started
    Path(a.record).write_text(json.dumps(result, separators=(',', ':'))+'\n')


def rejected(checker, record):
    try:
        checker.verify(record)
    except (ValueError, IndexError, KeyError, TypeError):
        return True
    return False


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path)
    p.add_argument('--worker', action='store_true')
    p.add_argument('--case', choices=[c['name'] for c in fixtures()])
    p.add_argument('--method', choices=['bfs','completion'])
    p.add_argument('--record')
    p.add_argument('--limited', action='store_true')
    a = p.parse_args()
    if a.worker:
        worker(a)
        return
    if a.output is None:
        p.error('--output required')
    a.output.mkdir(parents=True, exist_ok=False)
    checker = load('completion_checker', 'scripts/check-completion-certificate.py')
    base_checker = load('base_checker', 'scripts/check-relation-span-certificate.py')
    summaries = []
    for case in fixtures():
        for method in ('bfs', 'completion'):
            stem = case['name']+'.'+method
            record = (a.output/(stem+'.json')).resolve()
            command = [sys.executable, 'experiments/resource_guard.py', '--output', str((a.output/(stem+'.guard')).resolve()),
                       '--memory-mib','512','--cpu-seconds','3','--wall-seconds','5','--output-bytes',str(8*1024*1024),'--',
                       sys.executable, str(Path(__file__).resolve()), '--worker','--case',case['name'],'--method',method,'--record',str(record)]
            completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=8)
            (a.output/(stem+'.supervisor.txt')).write_text(completed.stdout+completed.stderr)
            usage = json.loads((a.output/(stem+'.guard')/'resources.json').read_text())
            assert completed.returncode == 0 and usage['returncode'] == 0 and usage['cleanup_verified'], (stem,usage)
            result = json.loads(record.read_text())
            started = time.monotonic()
            verdict = (checker if method == 'completion' else base_checker).verify(result)
            check_seconds = time.monotonic()-started
            expected = 'unresolved' if case['name'] == 'cyclic7_long_powers' and method == 'bfs' else ('proved' if case['expected_spanning'] else 'disproved')
            assert verdict['spanning'] == expected, (stem,verdict)
            factors = sum(len(t.get('factors',[])) for t in result['targets'])
            summaries.append(dict(case=case['name'], method=method, verdict=verdict,
                                  search_seconds=result['measured_search_wall_seconds'], check_seconds=check_seconds,
                                  target_factors=factors, certificate_bytes=record.stat().st_size,
                                  target_certificate_bytes=len(json.dumps(result['targets'],separators=(',',':')).encode()),
                                  rule_certificate_bytes=len(json.dumps(result.get('rules',[]),separators=(',',':')).encode()),
                                  bfs_expanded_states=sum(t.get('states',0) for t in result['targets']),
                                  rule_factors=sum(len(r['factors']) for r in result.get('rules',[])),
                                  metrics=result.get('metrics',dict(rule_count=result['rule_count']) if 'rule_count' in result else {}),
                                  resources=usage, command=command))
            print(stem, verdict['spanning'], f"{result['measured_search_wall_seconds']:.6f}s", flush=True)
    good = json.loads((a.output/'C3_full.completion.json').read_text())
    checks = []
    def reject(name, bad):
        assert rejected(checker,bad), name
        checks.append(name)
    bad = copy.deepcopy(good)
    rule = next(r for r in bad['rules'] if r['factors'])
    rule['factors'][0][2] *= -1
    reject('corrupted rule sign',bad)
    bad = copy.deepcopy(good)
    rule = next(r for r in bad['rules'] if r['factors'])
    rule['lhs'],rule['rhs'] = rule['rhs'],rule['lhs']
    reject('reversed orientation without inverse proof',bad)
    bad = copy.deepcopy(good)
    bad['rules'][0]['rhs'] = [1]
    reject('unsound free simplification',bad)
    bad = copy.deepcopy(good)
    bad['rules'].append(dict(id=len(bad['rules']),lhs=[1],rhs=[],factors=[],origin='forged'))
    reject('unsupported short rule',bad)
    bad = copy.deepcopy(good)
    bad['problem']['candidates'] = []
    bad['problem']['candidate_membership'] = []
    bad['quotient_relators'] = base_checker.make_quotient(bad['problem'])
    reject('stronger quotient rule reuse after removing candidate',bad)
    bad = copy.deepcopy(good)
    bad['quotient_relators'].append([1]*3)
    reject('raw defining relator added to fixed quotient',bad)
    bad = copy.deepcopy(good)
    bad['problem']['candidate_membership'] = [[]]
    reject('missing candidate membership',bad)
    bad = copy.deepcopy(good)
    bad['targets'][0]['factors'] = []
    reject('forged target identity',bad)
    # Orientation can be wrong even when the equation and its proof are valid.
    bad = copy.deepcopy(good)
    rule = next(r for r in bad['rules'] if r['rhs'])
    rule['lhs'],rule['rhs'] = rule['rhs'],rule['lhs']
    rule['factors'] = [[q,i,-s] for q,i,s in reversed(rule['factors'])]
    reject('valid equation with increasing orientation',bad)
    power = json.loads((a.output/'cyclic7_long_powers.completion.json').read_text())
    assert any(r['origin']=='critical_pair' for r in power['rules'])
    bad = copy.deepcopy(power)
    derived = next(r for r in bad['rules'] if r['origin']=='critical_pair')
    derived['factors'][0][0] = [2]  # Outside the rank-one alphabet.
    reject('corrupted critical-pair conjugator',bad)
    bad = copy.deepcopy(power)
    derived = next(r for r in bad['rules'] if r['origin']=='critical_pair')
    derived['factors'][0][2] *= -1
    reject('corrupted critical-pair derivation',bad)
    # An overlapping two-path ambiguity must cancel to its original relators.
    from experiments.certified_completion import Completion
    engine = Completion(2, [], seconds=1)
    engine.equation((1,2), (), [((),1,1)], 'input')
    engine.equation((2,1,1), (), [((),2,1)], 'input')
    engine.complete()
    for r in engine.rules:
        base_checker.check_product(list(r['lhs'])+base_checker.inv(r['rhs']), [[1,2],[2,1,1]], json.loads(json.dumps(r['factors'])),2)
    checks.append('nonabelian overlapping paths independently cancelled')
    # Independently check inclusion ambiguities, inverse orientations and
    # both-side simplification; these use only two tiny noncommuting words.
    assert any(r['origin']=='critical_pair' for r in engine.rules)
    (a.output/'nonabelian-overlap-probe.json').write_text(json.dumps(dict(
        base_relations=[[1,2],[2,1,1]], rules=engine.rules),separators=(',',':'))+'\n')
    # Fail-closed, bounded true positive. Never infer nonmembership.
    stem = 'deliberately-limited'
    record = (a.output/(stem+'.json')).resolve()
    command = [sys.executable,'experiments/resource_guard.py','--output',str((a.output/(stem+'.guard')).resolve()),
               '--cpu-seconds','3','--wall-seconds','5','--',sys.executable,str(Path(__file__).resolve()),
               '--worker','--case','C3_power_basis','--method','completion','--limited','--record',str(record)]
    completed = subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=8)
    assert completed.returncode == 0, completed.stderr
    limited = json.loads(record.read_text())
    assert checker.verify(limited)['spanning'] == 'unresolved'
    checks.append('rule-limited true positive remains unresolved')
    sources = ['experiments/certified_completion.py','scripts/check-completion-certificate.py',
               'scripts/test-certified-completion.py','experiments/relation_span.py',
               'scripts/check-relation-span-certificate.py','experiments/resource_guard.py',
               'tests/fixtures/relation-span-small.json']
    (a.output/'summary.json').write_text(json.dumps(dict(results=summaries, acceptance_checks=checks,
        source_sha256={s:hashlib.sha256((ROOT/s).read_bytes()).hexdigest() for s in sources},
        notes='One measurement per method/case; no statistical speedup claim. Per-worker RSS includes Python startup. Negative verdicts come only from independent finite obstructions.'), indent=2)+'\n')
    print('PASS: 11 small cases x 2 methods; adversarial and deliberately unresolved checks.')


if __name__ == '__main__':
    main()

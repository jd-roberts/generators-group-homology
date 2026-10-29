#!/usr/bin/env python3
"""Certificate-only replay of the recorded small suite. Never imports search."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT/path)
    loaded = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(loaded)
    return loaded


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--base', type=Path, required=True)
    a = p.parse_args()
    summary = json.loads((a.base/'summary.json').read_text())
    for source, expected in summary['source_sha256'].items():
        assert hashlib.sha256((ROOT/source).read_bytes()).hexdigest() == expected, source
    completion = module('completion_checker', 'scripts/check-completion-certificate.py')
    baseline = module('products', 'scripts/check-relation-span-certificate.py')
    fixtures = {c['name']:c for c in json.loads((ROOT/'tests/fixtures/relation-span-small.json').read_text())}
    assert len(summary['results']) == 22
    rules = successes = 0
    for row in summary['results']:
        stem = row['case']+'.'+row['method']
        record = json.loads((a.base/(stem+'.json')).read_text())
        if row['case'] in fixtures:
            assert record['problem'] == fixtures[row['case']]
        else:
            assert row['case'] == 'cyclic7_long_powers'
            problem = record['problem']
            assert (problem['rank'],problem['prime'],problem['relators'],problem['candidates']) == (1,7,[[1]*7],[[1]*14])
        verdict = (completion if row['method']=='completion' else baseline).verify(record)
        assert verdict == row['verdict']
        resources = json.loads((a.base/(stem+'.guard')/'resources.json').read_text())
        assert resources == row['resources'] and resources['returncode'] == 0 and resources['cleanup_verified']
        rules += verdict.get('verified_rules',0)
        successes += len(verdict['certified_targets'])
    limited = json.loads((a.base/'deliberately-limited.json').read_text())
    assert completion.verify(limited)['spanning'] == 'unresolved'
    limited_usage = json.loads((a.base/'deliberately-limited.guard/resources.json').read_text())
    assert limited_usage['returncode'] == 0 and limited_usage['cleanup_verified']
    overlap = json.loads((a.base/'nonabelian-overlap-probe.json').read_text())
    assert overlap['base_relations'] == [[1,2],[2,1,1]]
    assert any(r['origin']=='critical_pair' for r in overlap['rules'])
    for index, rule in enumerate(overlap['rules']):
        assert rule['id'] == index
        assert (len(rule['lhs']), tuple(rule['lhs'])) > (len(rule['rhs']),tuple(rule['rhs']))
        baseline.check_product(rule['lhs']+baseline.inv(rule['rhs']), overlap['base_relations'],rule['factors'],2)
    print(json.dumps(dict(records=22, verified_rules=rules, certified_target_occurrences=successes,
                          nonabelian_probe_rules=len(overlap['rules']), limited_positive='unresolved',
                          arithmetic_search_executed=False),indent=2))


if __name__ == '__main__':
    main()

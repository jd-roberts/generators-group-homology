#!/usr/bin/env python3
"""Small, whitelisted fixed-quotient tests and unchanged GAP comparisons."""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import resource
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from experiments.relation_span import produce


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


checker = load("span_checker", "scripts/check-relation-span-certificate.py")
measure = load("baseline_measure", "benchmarks/run.py")


def rejects(result):
    try:
        checker.verify(result)
    except (ValueError, IndexError):
        return True
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gap", default="gap")
    parser.add_argument("--output", type=Path, required=True, help="new directory; never overwrites")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    fixtures = json.loads((ROOT / "tests/fixtures/relation-span-small.json").read_text())
    summary = []
    for case in fixtures:
        # Only the ten committed, small fixtures can reach unchanged KBMAG.
        assert case["rank"] <= 2 and len(case["relators"]) <= 3
        started = time.monotonic()
        result = produce(case)
        search_wall = time.monotonic() - started
        started = time.monotonic()
        status = checker.verify(result)
        check_wall = time.monotonic() - started
        assert status["spanning"] == ("proved" if case["expected_spanning"] else "disproved"), (case["name"], result, status)
        bound = case["tor_dimension"] + len(case["candidates"]) - case["integer_relator_rank"] if status["spanning"] == "proved" else None
        if bound is not None:
            assert bound == case["known_h2"]
        record_path = args.output / (case["name"] + ".json")
        record_path.write_text(json.dumps(result, indent=2) + "\n")
        gap_script = r'''Read("Algorithms.g");;
(function()
 local f,r,words,answer,a,t;
 f:=FreeGroup(%d);
 words:=function(xs) return Product(xs,x->f.(AbsInt(x))^SignInt(x)); end;
 r:=List(%s,words);
 answer:=SecondHomologyCoefficients(f,r,%d,r);
 a:=Tor(f,r,%d);
 if IsEmpty(r) then t:=0; else
 t:=RankMat(List(r,w->List(GeneratorsOfGroup(f),g->ExponentSumWord(w,g)))); fi;
 Print("SPAN_CONTROL ",answer[2]," GAP ",GAPInfo.Version,
       " KBMAG ",PackageInfo("kbmag")[1].Version," Tor ",a," rank ",t,"\n");
 if answer[2]<>%d or a<>%d or t<>%d then Error("known small control bound mismatch"); fi;
end)();
QUIT;
''' % (case['rank'], json.dumps(case['relators']), case['prime'], case['prime'], case['known_h2'], case['tor_dimension'], case['integer_relator_rank'])
        script = args.output / (case["name"] + ".control.g")
        script.write_text(gap_script)
        log = args.output / (case["name"] + ".gap.txt")
        command = [args.gap, "-q", "-b", "--quitonbreak", str(script.resolve())]
        resources = measure.execute(command, log, 5)
        text = log.read_text()
        assert resources["status"] == "completed" and "SPAN_CONTROL " in text, (case['name'], resources, text)
        summary.append({"case": case["name"], "search_wall_seconds": round(search_wall, 6),
                        "independent_check_wall_seconds": round(check_wall, 6),
                        "fixed_quotient_status": status, "candidate_h2_upper_bound": bound,
                        "known_h2": case['known_h2'], "original_h2_upper_bound": case['known_h2'],
                        "fixed_rule_count": result['rule_count'], "rule_index_builds": result['rule_index_builds'],
                        "unchanged_gap_command": command, "unchanged_gap_control_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
                        "unchanged_gap_resources": resources})
        print(case['name'], status['spanning'], f"search {search_wall:.6f}s", flush=True)
    # Test the acceptance boundary, not just successful examples.
    good = json.loads((args.output / 'C3_full.json').read_text())
    bad = copy.deepcopy(good)
    bad['targets'][0]['factors'][0][2] *= -1
    assert rejects(bad), 'tampered identity certificate accepted'
    bad = copy.deepcopy(good)
    bad['problem']['candidate_membership'][0] = []
    assert rejects(bad), 'missing candidate N-membership accepted'
    bad = copy.deepcopy(good)
    bad['quotient_relators'].append(bad['problem']['relators'][0])
    assert rejects(bad), 'vacuous quotient with raw defining relator accepted'
    # A sound proof search can be incomplete even for a true positive.
    limited_case = next(c for c in fixtures if c['name'] == 'C3_power_basis')
    limited = produce(limited_case, max_states=1)
    assert checker.verify(limited)['spanning'] == 'unresolved'
    (args.output / 'deliberately-limited.json').write_text(json.dumps(limited, indent=2)+'\n')
    sources = ['experiments/relation_span.py','scripts/check-relation-span-certificate.py',
               'scripts/test-relation-span.py','tests/fixtures/relation-span-small.json',
               'Algorithms.g','benchmarks/run.py']
    evidence = {'results': summary, 'producer_runner_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss, 'acceptance_boundary_checks': 4,
                'source_sha256': {s: hashlib.sha256((ROOT/s).read_bytes()).hexdigest() for s in sources},
                'limits': {'search_seconds_per_case': 5,'original_gap_wall_limit_seconds': 5,
                           'note':'Existing harness allows termination grace; kills/reaps descendants.'},
                'measurement_notes':'Search/check times are in-process wall times; search memory not isolated; runner peak RSS is cumulative across cases, excluding child processes. GAP wait4 RSS is the max, not aggregate concurrent memory. Startup included. Known-case tests do not predict arithmetic completion costs.'}
    (args.output / 'summary.json').write_text(json.dumps(evidence, indent=2)+'\n')
    print('PASS: ten small cases, unchanged GAP comparisons, four acceptance-boundary checks.')


if __name__ == '__main__':
    main()

# Small-only three-method power/conjugation comparison

[Technical report](../../../docs/CERTIFIED-POWER-CONTROL.md).

`comparison/` contains sixty method/case records (twenty whitelisted cases),
one deliberately rule-limited true positive, exact mathematical inputs,
every retained equation and product certificate, independent verdicts,
negative permutation witnesses, source hashes and measurements. Each worker's
`.guard/` directory retains raw streams, limits, termination and cleanup.
`suite-run.guard/` contains the full driver log and outer resource record.
`comparison/summary.json` also records sixteen adversarial/adapter checks.
The new fixtures are in `tests/fixtures/power-conjugation-small.json`.

The driver imports all three implementations before starting measured search;
its common runtime/import memory remains included in worker peak RSS. These
are single functional measurements, not a statistical speedup study.

No arithmetic-group search occurs in this directory. The separately authorized
single known-identity control is in `prime7-power-control-1-2026-10-28`.
Certificate-only replay:

```
python3 scripts/replay-power-experiments.py \
  --small benchmarks/results/power-conjugation-small-2026-10-28/comparison \
  --control benchmarks/results/prime7-power-control-1-2026-10-28
```

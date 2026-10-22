# Recorded quick baseline, 2026-10-21

These are observations, not algorithm changes or replacements for the
original archived tables. See [the interpretation and timing tables](../../../docs/BASELINE.md).

- `runs.jsonl`: 78 measured invocations, one JSON object per line. Includes
  numerical outputs, individual wall/CPU times, RSS measurements, and optional
  GAP profiles / external-process intervals. Every invocation completed.
- `raw.jsonl`: the corresponding unabridged GAP outputs and optional strace
  text. Match records by `suite`, `case`, `coefficient_prime`, and `repeat`.
- `metadata.json`: source commit, original-file and driver hashes, exact
  arguments, resource limits, and the postprocessing parser hash.
- `validation.json` and `validation.log`: separately timed smoke, H1,
  presentation-identification, and harness-test checks.
- `parser-validation.log`: harness tests rerun after fixing handling of split
  `execve` / resumed events in the trace parser. Numerical runs were not rerun
  or altered to make the trace counts agree.

All five measurement suites used the clean source revision
`86a99c67d612e2664657778a94b027376da3fec7` (the full hash is authoritative in
`metadata.json`). GAP/KBMAG code and all original research artifacts were
unchanged. The trace parser was subsequently corrected and raw traces were
reprocessed; its hash is recorded separately. Derived process intervals must
not be confused with CPU profiles of the external C routines.

The dataset contains 36 small H2 replays (12 inputs, three repetitions),
18 separate diagnostic H2 invocations including six at coefficient primes
11 and 13, and 24 arithmetic **component-only** runs. It contains no full
Anton-family H2 computation. The earlier cancelled sweep and development
probes are excluded. Case `SL2F5` means the stored presentation, verified to
be C5 rather than the matrix group SL(2,5).

Read the records without extra Python dependencies:

```python
import json
from pathlib import Path
root = Path("benchmarks/results/2026-10-21")
runs = [json.loads(line) for line in (root / "runs.jsonl").read_text().splitlines()]
for run in runs:
    if run["suite"] == "small":
        print(run["case"], run["coefficient_prime"], run["repeat"],
              run["upper_bound"], run["wall_seconds"], run["status"])
```

Collection from retained raw suite directories can be repeated with
`python benchmarks/collect.py RAW_ROOT NEW_OUTPUT_DIRECTORY`. Collection
does not launch GAP. Run commands for generating new raw suites are in the
baseline guide; use a new directory and keep each invocation bounded.

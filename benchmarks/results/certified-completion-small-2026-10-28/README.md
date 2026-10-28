# Small-only certified completion evidence

No arithmetic proof search was executed. See
[the technical report](../../../docs/CERTIFIED-COMPLETION-SMALL-TESTS.md).

- `comparison/summary.json`: exact measurements and verdicts for eleven small
  fixtures, two methods each, plus adversarial-check names and source hashes.
- `comparison/*.json`: original problem, fixed quotient, positive target
  products, and every completion rule with expanded proof. The deliberately
  limited true-positive record is unresolved. The nonabelian probe records
  its exact free-group basis words and independently checked derived rules.
- `comparison/*.guard/`: each worker's resources, termination and raw streams.
- `suite-run.guard/`: outer driver resources and exact run log. This also
  bounds the direct nonabelian probe and independent checks in the driver.
- `regression/stage1/`: eight safety probes, eleven prior verification commands,
  three constrained small workers, exact outputs and acceptance records.
  `paper-provenance.stdout.txt.gz` is losslessly compressed (957 raw bytes).
- `independent-replay.stdout.txt`: final certificate-only replay, no search.
- `environment.json`: Python/platform and previous commit reference.
- `evidence-manifest.json`: hashes of evidence and the new implementation,
  independent checkers, runner and report. The manifest excludes itself.

The five already certified arithmetic targets and all previous research
artifacts/certificates are unchanged. Old pilot manifest hashes were checked.
The measurements are one final run per small method/case, not a statistically
controlled performance study. Development iterations used only bounded small
inputs and are described in the report; their scratch data are not benchmark
samples. No mathematical nonmembership is inferred from an unresolved search.

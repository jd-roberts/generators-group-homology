# Small fixed-quotient certificate tests

These are ten whitelisted small-group tests; no arithmetic proof search or completion ran.
Each case JSON contains exact inputs, candidate membership products, accepted Q-products,
and (for negative controls) finite permutation obstructions. The `.control.g` and
`.gap.txt` files preserve the unchanged GAP comparison input and scalar output.
`summary.json` records runtimes, wait4 resource usage and source hashes.

See [the full report](../../../docs/PRIME7-SPANNING-CERTIFICATE-PLAN.md) for the
criterion, mathematical controls, measured table and limits. Negative status here
comes from verified finite obstructions, not a nonidentity search remainder.
`deliberately-limited.json` is a true positive intentionally left unresolved by a
state cap. Timings compare different workloads and do not establish a speedup.

Reproduce into a NEW directory:

```sh
python3 scripts/test-relation-span.py --gap /path/to/gap --output /tmp/new-span-tests
python3 scripts/check-relation-span-certificate.py /tmp/new-span-tests/V4_conjugated.json
```

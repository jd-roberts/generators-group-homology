# One authorized bounded prime-7 pilot

Exactly one pilot was launched. No new target was certified; the total remains
R3,R5,R9,R12,R15. Full spanning remains unresolved. No retries ran.

- `stage1/safety/`: eight passing OS-limit/cleanup probes, raw logs, PID/start
  records, resource metadata and source hashes.
- `stage1/verification-summary.json`: eleven existing-suite checks plus three
  workers constrained by the new wrapper. Raw controls/certificates are below
  `stage1/verification/`.
  Its paper-provenance stdout is losslessly gzip-compressed to retain exact
  GAP whitespace; the pilot stdout is retained byte-for-byte as plain JSONL.
- `pilot-attempt.json`: exclusive one-shot launch reservation and source/gate hashes.
- `pilot-input.json.gz`: exact frozen quotient, candidates, membership witnesses,
  stable relation labels and original targets.
- `source/`: snapshots of the pilot-relevant source and static inventory.
- `pilot/`: exact JSONL output, empty stderr, OS resource and termination record.
- `verified-products.json`: independently checked existing products plus all
  unresolved attempted target statuses.
- `result.json`: direct and linear coverage, witnesses, resources and status.

See [the full report](../../../docs/PRIME7-PILOT-1-RESULTS.md).
Replay certificates only (no search):

```sh
python3 scripts/check-prime7-pilot-results.py --base benchmarks/results/prime7-pilot-1-2026-10-28
```

Limits were 5 shared search seconds, 20,000 indexed rules, 1,000 states per
target, length growth 6, 512 MiB address space, 6 CPU seconds, external wall
10 seconds, and 8 MiB per output file. The search took 0.120148061 seconds;
all targets stopped at the state limit, with index construction capped.
These are unresolved computations, not nonmembership results or evidence
of independence. The full rule index was not serialized; frozen inputs,
source, counts, complete output and accepted products are preserved.

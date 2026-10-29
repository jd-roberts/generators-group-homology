# ONE authorized R7 checkpoint continuation

[Concise Track A assessment](../../../docs/TRACK-A-CONTINUATION-ASSESSMENT.md).
[Frozen pre-launch plan](../../../docs/PRIME7-A4-CONTINUATION-PLAN.md).

R7 remains unresolved. The first frozen job began, examined 163 offsets and
submitted one compatible overlap; normalization made 332 reductions, then
stopped at the unchanged 2,000-factor proof cap. No job completed and no new
rule or original-target certificate was accepted. No retry or later arithmetic
experiment occurred. Verification-machinery development stopped after the run.

- `preparation/checkpoint.json`: verbatim 233 saved rules plus eight raw,
  one-factor Q217–Q224 rules; 241 forward products in Q and 236 reverse
  products establishing full normal-closure equality in the same free group.
- `preparation/schedule.json`: exact frozen 4,000 jobs, including 325 jobs
  involving the long powers and one for each long power in the first eight.
- `preparation/prior-trace.jsonl`, `input.json.gz`: unchanged prior checkpoint
  source and original full fixed-Q blueprint.
- `preparation.guard/`: static schedule/coverage reconstruction measurements;
  it forms no critical equation and performs no R7 search.
- `loaded-state.json`: actual engine loader roundtrip matches checkpoint and
  frozen queue. `loader-final.guard/`, `loader-gate.json` and `small-test.json`
  record the passing final loader/coverage/small-completion/adversarial gate.
  `loader.guard/` retains the earlier passing test before one stricter
  independent loaded-state check was added. Only the final gate authorized launch.
- `attempt.json`: exclusive one-attempt marker, preparation/gate/source hashes.
- `source/`: immutable implementation and plan snapshots taken before launch.
- `worker/stdout.txt`: exact header, first job start/end, unresolved answer and
  accounting summary; stderr is empty.
- `worker/resources.json`: actual limits, CPU/wall/RSS, bytes, termination,
  cleanup. The search stop is a handled proof cap, not a kernel resource kill.
- `input-verification.*`, `independent-check.*`, `result.json`: independent
  forward/reverse input checks and post-run certificates/counters/linear status.
- `stage1/`: eight OS safety probes, eleven previous verification commands,
  three constrained small workers, raw results. Paper-provenance stdout is
  preserved losslessly as gzip to avoid whitespace-only repository noise.
- `prior-replay*`: saved-checkpoint and previous suite certificate/manifests gate.
- `post-replay.stdout.txt`: final use of the existing independent checker;
  no discovery and no newly developed post-run verification code.
- `preservation-check.json`, `evidence-manifest.json`: unchanged original/prior
  evidence hashes and the final new evidence/source/report manifest.

The 4,000 queue count describes the installed frozen arithmetic schedule.
The parent constructor's 78 temporary free-cancellation setup jobs were cleared
before installation and never processed. No automatic job replenishment occurs.

All 241 inputs are independently valid in original Q, and all 236 Q rows follow
from them. No new equation was accepted by the search. Certified originals
remain R3,R5,R9,R12,R15. Full spanning remains unverified.

Certificate-only replay:

```
python3 scripts/check-a4-continuation.py \
  --base benchmarks/results/prime7-a4-continuation-1-2026-10-29
```

The one search authorization is consumed. Do not relaunch the controller or
regard a new output directory as permission. No subsequent experiment is planned
or initiated by this artifact.

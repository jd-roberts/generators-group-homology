# First authorized prime-7 pilot: safety passed, spanning remains unresolved

Exactly one prime-7 pilot was executed after all Stage 1 checks passed.
It found **no new identity certificate**. There were no additional linear
consequences. The certified original targets remain **R3,R5,R9,R12,R15**:
five of 32. All fifteen selected targets and 27 original targets remain
unresolved. The twelve-word spanning assertion has **not** been established.
No nonmembership, independence, nontriviality, or new homology result follows.

Original GAP algorithms, published presentations and archived research
artifacts are unchanged. No Knuth–Bendix arithmetic completion, second
pilot, automatic retry or increased-limit trial was launched.

## 1. Inputs and one-attempt authorization

Inputs are the correctly transcribed Proposition 3.2 presentation, verified
presentation maps and the twelve words interpreted using
`f7=b0=z^-3*b1*z^3`, as specified in the
[spanning plan](PRIME7-SPANNING-CERTIFICATE-PLAN.md). This interpretation is
not assumed to be the unrecovered historical input convention.

The fixed quotient is unchanged:

```
Q=F/normal_closure([xi,Rj], Rj^7, sk).
```

Its 236 stored relations (234 nonempty) do not include the raw original
Rj as additional defining equations. The 32 targets, twelve candidate
membership certificates, exact quotient words and stable relation indices
are frozen in
[the pilot input](../benchmarks/results/prime7-pilot-1-2026-10-28/pilot-input.json.gz).
An exclusive-create [attempt record](../benchmarks/results/prime7-pilot-1-2026-10-28/pilot-attempt.json)
reserved this single launch before the worker started. Even a failed launch
would consume it. The controller refuses another launch with this marker.
The exclusive-create guard was tested on a temporary file without invoking
any arithmetic worker.

The selected order was exactly

```
1,2,4,6,7,8,10,11,13,14,18,26,28,29,30.
```

Source snapshots, SHA-256 hashes, the Stage 1 gate hash, original input
hash, commands, stdout, stderr, resource measurements and final status are
preserved in [the complete run directory](../benchmarks/results/prime7-pilot-1-2026-10-28/README.md).
The code base before the new experimental additions was commit d68cfd8.
The derived combined-product JSON is stored compactly without changing its
data. The paper-provenance replay's stdout is gzip-compressed losslessly
to preserve GAP's exact trailing whitespace; raw pilot output is unchanged.

## 2. Stage 1: OS controls and cleanup

[resource_guard.py](../experiments/resource_guard.py) is a dedicated Linux
supervisor. A bootstrap installs hard and soft RLIMIT_AS, RLIMIT_CPU and
RLIMIT_FSIZE with equal values before exec. Descendants inherit these hard
limits and cannot raise them. Core dumps are disabled. A supervisor wall
clock limit covers the entire owned process tree.

The supervisor is a child subreaper. It kills the original process group,
then scans/reaps its remaining descendants, including children that started
new sessions and escaped that process group. Cleanup also runs after normal
exit, process error, and handled supervisor SIGINT/SIGTERM. PID start times
are recorded to distinguish survival from PID reuse. The direct worker has
a parent-death SIGKILL safeguard. Cleanup failure is a failed gate, not a
successful run. This is a resource supervisor, not a security sandbox.

Eight safety probes passed. Limit-exhaustion tests deliberately used smaller
limits for fast, controlled checks; a separate readback verified the exact
512 MiB, six CPU-second and 8 MiB values later used for the pilot. The
external wall parameter was tested at 0.5 seconds and set to ten for the
pilot. Every exhaustion/exit probe created an escaped-session child; each
was killed and reaped, and PID/start-time absence was checked again after
the pilot.

| Probe | Test setting / expected behavior | Observed outcome |
| --- | --- | --- |
| Exact inherited limit readback | 512 MiB AS; CPU 6; file size 8 MiB | All soft/hard values match |
| Memory exhaustion | 64 MiB address space; allocate until failure | MemoryError, expected exit 73; child cleaned |
| CPU exhaustion | 1 CPU second; busy loop | Kernel SIGKILL at CPU limit; child cleaned |
| Wall timeout | 0.5 seconds; sleeping parent/child | Supervisor wall termination; child cleaned |
| Output exhaustion | 4,096 bytes; repeated writes | SIGXFSZ; file exactly 4,096 bytes; child cleaned |
| Normal parent exit | Leave sleeping escaped child | Parent exit 0; child killed/reaped |
| Parent crash | Exit 17 with sleeping escaped child | Exit 17 preserved; child killed/reaped |
| Supervisor interruption | Send SIGTERM after child ready | Signal recorded; worker and escaped child killed/reaped |

RLIMIT_AS limits virtual address space, not resident memory. An allocation
can therefore fail while RSS is below the address-space cap. The memory
probe's `process_error` classification preserves its expected nonzero exit;
the explicit MemoryError marker verifies why it stopped. Per-process memory,
CPU and per-file output limits are not aggregate multi-process budgets;
the pilot itself creates no descendants. Wall time and cleanup cover the
tree. Observed RSS samples may double-count shared memory; wait4 peak RSS
is reported separately.

The [safety summary](../benchmarks/results/prime7-pilot-1-2026-10-28/stage1/safety/summary.json)
and raw probe records preserve exact settings, outcomes and usage. All
safety checks passed before any prime-7 search began.

## 3. Stage 1: existing verification suite and constrained small workers

The [verification gate](../benchmarks/results/prime7-pilot-1-2026-10-28/stage1/verification-summary.json)
records eleven successful suite commands plus three constrained-worker
checks. These include:

- Existing benchmark failure/timeout/interrupt/child-reaping regressions.
- Earlier correction matrices/free-word checks. This does not rehabilitate
  the old b1-interpreted nonmembers; their documented status is unchanged.
- All previous presentation/membership products and static spanning witnesses.
- A fresh ten-case small spanning suite and unchanged GAP comparisons.
- Original smoke, historical H1, presentation sanity, finite identification,
  paper-provenance and prime-7 display-rank checks.
- Worker runs inside the new resource wrapper for C3's transformed basis,
  C2 x C2's conjugated candidate basis, and its missing-commutator negative
  control. Every accepted product was independently checked. The negative
  control remained a finite-obstruction result, not a search inference.

The new worker reuses the existing indexed identities/BFS method and checks
the state budget **before** retaining a new state, so it never retains a
1,001st state under a 1,000-state limit. This is local to the new pilot
worker; the old GAP algorithms and earlier certificate engine are preserved.
The worker also checks its deadline inside the search loops and has a
five-second SIGALRM covering index construction and all selected targets.
It never resets that timer per target. Source hashes were checked against
the passing safety/verification gate before launch.

## 4. Stage 2: exact limits and measured resource use

| Control | Authorized/enforced value | Observed |
| --- | ---: | ---: |
| Shared search time | 5 seconds, one timer | 0.120148061 seconds |
| Indexed rule instances | 20,000 | 20,000; construction stopped at cap |
| Retained states per target | 1,000 | 1,000 for each selected target |
| Word-length growth | At most 6 | At most 6 for every target |
| Address space per process | 512 MiB hard/soft | Effective limit read back correctly |
| CPU time | 6 seconds hard/soft | 0.183975 user + 0.007900 system seconds |
| External worker/tree wall time | 10 seconds | 0.197924 seconds including bootstrap/cleanup |
| Output file size | 8 MiB hard/soft | stdout 3,256 bytes; stderr 0 bytes |
| Peak worker RSS | Measured, not the AS limit | 25,484 KiB |

The worker returned **0 / completed**. No memory, CPU, wall-time or output
limit terminated this pilot. Its mathematical search stopped on the rule
and state budgets. No leftover time was used for another attempt.
The sampled process-tree RSS peak was 25,356 KiB; individual process records
retain their last observation, while the separate peak fields retain peaks.
The [raw resource record](../benchmarks/results/prime7-pilot-1-2026-10-28/pilot/resources.json)
and [JSONL worker output](../benchmarks/results/prime7-pilot-1-2026-10-28/pilot/stdout.txt)
are preserved. The full rule index was not serialized; its exact inputs,
construction code, cap and counts are frozen, and no per-rule activity
profile is claimed.

All fifteen target outcomes were **unresolved / state_limit**. “Visited”
means dequeued/expanded words, distinct from the 1,000 retained/discovered
states. No nonidentity normal form was interpreted as nonmembership.

| Target | Status | Retained states | Visited | Maximum word length |
| --- | --- | ---: | ---: | ---: |
| R1 | unresolved: state_limit | 1000 | 42 | 10 |
| R2 | unresolved: state_limit | 1000 | 42 | 10 |
| R4 | unresolved: state_limit | 1000 | 35 | 10 |
| R6 | unresolved: state_limit | 1000 | 35 | 10 |
| R7 | unresolved: state_limit | 1000 | 23 | 10 |
| R8 | unresolved: state_limit | 1000 | 34 | 10 |
| R10 | unresolved: state_limit | 1000 | 31 | 10 |
| R11 | unresolved: state_limit | 1000 | 31 | 10 |
| R13 | unresolved: state_limit | 1000 | 38 | 14 |
| R14 | unresolved: state_limit | 1000 | 32 | 18 |
| R18 | unresolved: state_limit | 1000 | 21 | 22 |
| R26 | unresolved: state_limit | 1000 | 13 | 33 |
| R28 | unresolved: state_limit | 1000 | 11 | 36 |
| R29 | unresolved: state_limit | 1000 | 9 | 48 |
| R30 | unresolved: state_limit | 1000 | 7 | 54 |

## 5. Independent checking and all 32 target statuses

Every complete successful worker record is required to pass the independent
free-cancellation checker before acceptance. There were **no new successful
records** in this run. The five existing products were replayed, and no
partial or invalid output record was accepted. The combined
[verified-product record](../benchmarks/results/prime7-pilot-1-2026-10-28/verified-products.json)
is also checked in a separate Python process. The checker imports no search
producer code.

The prior exact identity rows and candidate occurrence rows were retained.
The controller recomputed all linear combinations, saved every coverage
witness, and the independent post-run checker recomputed the finite-field
rank/coverage separately. Because no new target was certified, no new unit
row was added and there are **no additional linear consequences**. The
formal combined row rank remains 17; formal residual dimension 15 is an
upper bound in this presentation of the quotient, not a nonspanning
obstruction or lower bound on its true dimension.

- **Certified originals (5):** R3,R5,R9,R12,R15.
- **Unresolved originals (27):** R1,R2,R4,R6,R7,R8,R10,R11,R13,R14,R16,R17,
  R18,R19,R20,R21,R22,R23,R24,R25,R26,R27,R28,R29,R30,R31,R32.
- **Additional linear consequences:** none.
- **Twelve-word spanning established:** no.

The twelve b0-interpreted candidates retain their existing certified
membership in N, and the six valid corrected words retain their certified
kernel status. This pilot did not establish that they span H2 or decide
whether any class is nonzero. The historical twelve-word spanning assertion
remains unreproduced. Identification of the original presented group with
the intended arithmetic matrix group still uses the separate presentation
theorem/hypotheses; the verified comparison between the two stored
presentations is unaffected.

## 6. What this says about more advanced methods

This particular finite cyclic-split breadth-first method ran out of
representational/search capacity, not elapsed time or process memory.
It retained 1,000 states after expanding only 7–42 words per target, while
index construction reached its rule cap after about 0.0504 seconds. The
observations point to heavy branching and an incomplete finite rule index.
They do not measure the difficulty of the underlying identities and do not
show that an uncapped search or completion would finish.

There is also a structural limitation already noted in the plan. For
example, the available z^7 certificate uses the auxiliary word z^49. A
near-half cyclic split of that power has left side length at least 23,
whereas this pilot's length-growth policy would cap a z^7 target path at
13. Thus that input power cannot directly act as a rule on such a path.
This does not exclude other proofs; it illustrates why useful derived
short equations or algebraic collection may be necessary. z^7 was already
certified and was not one of the fifteen attempted targets.

The pilot gives **no demonstrated speedup** over the original calculations
and no evidence that a larger time allowance alone would help. It also
cannot forecast the runtime or memory needed by proof-producing completion.

**Single recommended next experiment, not executed:** build a proof-producing
critical-pair completion layer for the fixed-quotient engine and validate
it only on the existing small test suite. Each new oriented equation must
carry a product-of-conjugates derivation in the original fixed Q relations,
checked independently before use. The purpose is to test whether derived,
directed reductions can avoid the observed branching and expose short
consequences of long power relations. Preserve the negative controls and
resource caps. This is a proposal requiring further authorization; no such
adapter, additional arithmetic run or increased-limit trial was executed.

## 7. Replay without running another pilot

```sh
python3 scripts/check-prime7-pilot-results.py --base benchmarks/results/prime7-pilot-1-2026-10-28
python3 scripts/check-relation-span-certificate.py benchmarks/results/prime7-pilot-1-2026-10-28/verified-products.json
```

The post-run checker verifies the single attempt, gate/source/input hashes,
resource bounds, child absence, every complete claimed product, finite-field
coverage witnesses and unresolved status. It never invokes the search
worker. The archived run's one-shot controller refuses another launch.
New safety tests or pilot attempts should not be mixed into this immutable
run directory. The original research inputs and mathematical algorithms
remain byte-identical to the preserved originals; work stays on
codex-development and no merge to main is performed.

# Track A: checkpoint continuation and verification assessment

**R7=a^4 remains unresolved.** The one authorized continuation entered critical
processing, but its first overlap exceeded the unchanged 2,000-factor
accumulated-proof cap. No new equation or original-target certificate was
accepted. This is computational exhaustion of a proof-size budget, not a
mathematical obstruction. No retry, other arithmetic target or follow-up
experiment was run. Machinery development stopped after this experiment.

## What the loader establishes

The 233 saved rules from commit 515b306 were loaded verbatim. Original
Q217–Q224 were appended without simplification as rules 233–240, with singleton
products in their original Q indices. There are 241 rules, not 241 new
relations added without justification.

The independent checker verifies both normal-closure containments in F6:

- All 241 rule discrepancies L_j*R_j^-1 are explicit products of conjugates
  of the original 236 Q relations.
- All 236 original Q words are explicit products of the loaded discrepancies.
  These reverse certificates reconstruct the known seeding trace; the largest
  has 44 factors. The eight raw long-power rows have one-factor certificates.

Consequently the loaded system presents the **full intended quotient Q**,
not a stronger or weaker quotient. A load-only roundtrip separately checks
that the engine installed those exact rules, certificates and frozen jobs.
No R7 relation was inserted. Full inputs and both-direction certificates are
in [checkpoint.json](../benchmarks/results/prime7-a4-continuation-1-2026-10-29/preparation/checkpoint.json).

The eight OS safety probes passed again, as did eleven existing verification
commands, three constrained small workers, the saved-checkpoint and previous
certificate/manifests replays, the loader tests and adversarial checks. A
small x^2/x^3 example verified actual certified completion and four overlap
placements in one frozen job. All gates passed before launch.

## Frozen schedule and actual work

The [pre-launch plan](PRIME7-A4-CONTINUATION-PLAN.md) fixes the exact
[4,000 ordered jobs](../benchmarks/results/prime7-a4-continuation-1-2026-10-29/preparation/schedule.json).
The first eight pair each long-power rule with a compatible checkpoint rule.
The full schedule assigns Q217–Q224 respectively 58,34,35,37,23,22,52,64 jobs:
325 long-power jobs in total. New equations could simplify subsequent frozen
jobs, but no jobs involving new rules would be added. The finite schedule
cannot certify nonmembership or confluence.

Only the **first job** was reached: zero-based rules (22,233). Rule 22 is
`a^2*z -> z*a^2`; rule 233 is original Q217=R25^7 -> empty. The overlap
concerns commuting a^2 across the initial z of the long-power word. Its
normalization accumulated proof factors faster than the allowed proof budget.
The rejected expanded proof was not serialized; its exact attempted factor
count and per-rule contribution are not known.

| Quantity | Recorded outcome |
| --- | ---: |
| Loaded / retained final rules | 241 / 241 |
| Frozen rule-pair jobs | 4,000 |
| Jobs begun / completed | **1 / 0** |
| Candidate offsets examined | 163 |
| Compatible overlap placements | **1** |
| Overlap equations submitted / completed | **1 / 0** |
| Oversized placements | 0 |
| Reductions before stop | 332 |
| Largest equation submitted | length 163 |
| Accepted new equations / original-target certificates | **0 / 0** |
| Search stop | factor_limit |
| Shared search wall | 0.592883933 s |
| Supervised worker wall | 0.689313 s |
| Worker CPU user / system | 0.667725 / 0.015738 s |
| Peak worker RSS | 15,360 KiB |
| Stdout / stderr | 1,212 / 0 bytes |
| Process return / termination / cleanup | 0 / completed / verified |

“Jobs begun” is the inherited counter named `rule_pair_jobs_processed`; it
counts entry to a job, not successful completion. The job-end record explicitly
marks it incomplete. Q218–Q224 were scheduled early but **not processed** after
Q217's first job stopped the run. Neither 4,000 scheduled jobs nor one submitted
overlap should be reported as completed critical processing.

Bookkeeping detail: 4,000 is the installed frozen queue. The parent constructor
briefly creates 78 generic free-cancellation pair jobs; the loader discards
that setup queue before installing the frozen schedule. None of those setup
jobs is processed. Peak queue occupancy is 4,000; the reported count is not
a count of all heap insertions including discarded constructor setup: that
literal insertion count is **4,078**. Thus a strict cumulative interpretation
including constructor setup is not attested by the reported 4,000-job counter.
The frozen selected list, peak occupancy and jobs eligible for processing are
still bounded by 4,000; no setup job was executed. This accounting limitation
is preserved rather than repaired by an unauthorized repeat.

All requested OS caps were enforced: 512 MiB AS, six CPU seconds, ten external
wall seconds and 8 MiB per output file, with literal inherited limits read back.
The shared search alarm was five seconds; retained rules were capped at 256,
the installed queue at 4,000, word/overlap length at 512, accumulated proof
factors at 2,000, and reduction steps per call at 2,000. The proof cap stopped
the run well before its time or memory allowances. Remaining allowances were
not used for a retry or increased limits.

Every accepted input certificate and any streamed new equation is checked
against original Q by a checker importing no discovery code. Here there were
no new equations to accept. Exact sources, hashes, forward/reverse witnesses,
raw logs, per-job accounting, resource measurements and termination are in
[the evidence directory](../benchmarks/results/prime7-a4-continuation-1-2026-10-29/).

## Mathematical outcome

The loader equivalence is established. The earlier verified a^2-centrality
identities remain valid. **No new arithmetic relation follows from this
search output.** R7 remains unresolved; the certified originals are still
R3,R5,R9,R12,R15, with 27 unresolved and linear witness rank 17. No new unit
row or additional linear consequence was obtained. Full twelve-word spanning
is not established. The six corrected b0 classes remain legitimate kernel
classes, with their spanning still conditional; no independence, nontriviality
or exact dimension-six assertion is made.

This run does test an actual critical overlap, unlike the previous initialization
stop. It does not show that its normalized equation lacks a short certificate,
that all 4,000 jobs would fail, or that unrestricted completion cannot succeed.
The observed bottleneck is repeated expansion of accumulated product proofs
during normalization, not an exhausted five-second clock or a nonmembership
obstruction. A faster rewriting backend alone is not demonstrated to remove
that proof-recording bottleneck.

## Concise assessment: what remains to verify the original work

1. **Close the spanning gap.** Produce original-Q products killing all 32
   defining relators, or the verified sufficient set of fifteen unresolved
   targets. This certifies that the twelve b0-interpreted words span
   A=N/(N^7[F,N]); it would establish that the corrected six classes span H2.
   Full confluence is unnecessary if positive certificates are available.
2. **Resolve historical provenance.** Recover the actual historical generator
   coordinates, candidate words, presentations and successful FindBasis
   reductions, if available. Our verified b0 convention does not prove that
   it was the one used historically. Retain the distinction between the
   printed words and the separately corrected representatives.
3. **Keep the arithmetic identification separate.** The six-/fourteen-generator
   presentation maps are certified. Identification with the intended arithmetic
   matrix group still needs the cited presentation theorem and its hypotheses;
   matching names or a finite matrix image does not supply it.

The 2009 claim is an upper bound of six; the 2020 objective is spanning.
Neither verification requires proving six independent or nonzero classes.
No result here refutes the original upper bound, but these bounded trials
have not independently reproduced its historical expensive arithmetic run.

**Recommendation:** preserve Track A's verified inputs and acceptance checker,
but pause custom rewriting/infrastructure development and repeated short
arithmetic trials. The finite mathematical verification goal is worthwhile;
more of this particular implementation has not earned a research investment.
Prioritize recovery of historical successful reduction artifacts or a
mathematically guided derivation of the missing identities. Proof-producing
KBMAG would be a separate, substantial research decision requiring explicit
proof provenance, not an evidenced automatic speedup. No new machinery,
checkpoint continuation or further experiment was initiated after this run.

Certificate-only replay, without discovery:

```sh
python3 scripts/check-a4-continuation.py \
  --base benchmarks/results/prime7-a4-continuation-1-2026-10-29
```

Original algorithms, presentations, publications, historical results and all
prior certificates are unchanged. Findings are committed on codex-development;
PR #2 remains draft and main is not modified or merged.

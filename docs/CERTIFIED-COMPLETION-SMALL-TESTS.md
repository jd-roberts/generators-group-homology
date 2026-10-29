# Certified critical-pair completion: small-case implementation and assessment

The experimental engine and independent checker are implemented. All ten
existing small presentations pass, including three independently obstructed
nonspanning lists. A finite cyclic power example succeeds where the old bounded
search is unresolved. **There is no general speedup on the original ten cases.**
No new arithmetic-group proof search, completion, or prime-7 pilot was run.
The arithmetic certified total remains R3, R5, R9, R12, R15: five of 32;
twelve-word spanning remains unresolved. The six valid b0-interpreted kernel
classes retain their earlier membership status, without a spanning,
independence, nontriviality, or dimension-six conclusion.

## What causes the original search to branch

[The unchanged engine](../experiments/relation_span.py) indexes rotations of
both signs of each freely reduced Q relator, then many splits of each rotation.
Before deduplication, a length-L input contributes on the order of L squared
indexed instances. Instances retain distinct conjugate proofs, so two instances
with the same replacement can still occupy separate index entries. At every
substring of a target state, the search tries every matching replacement.
Many are length increasing, subject to the target-length-plus-six bound. A
word-level seen set merges identical descendants, but distinct insertions and
positions still produce many distinct words. Each queued state also copies
its accumulated proof. There is no derivation of new shared short equations.

The [first arithmetic pilot](PRIME7-PILOT-1-RESULTS.md) reached 20,000 instances
while constructing its index and 1,000 retained states after only 7–42 expanded
states per target. These are measured limits, not proof of exponential
asymptotics or of nonmembership. More wall time alone cannot overcome the same
state and index caps. The present comparison uses the unchanged baseline
`FixedQuotient`, not the pilot worker's strict retained-state subclass; that
baseline can transiently retain 1,001 words before reporting its state limit.
No baseline code or previously recorded evidence was changed.

## Implementation and bounded strategy

[certified_completion.py](../experiments/certified_completion.py) implements
string rewriting on the signed free-generator alphabet. It uses:

- Free cancellation rules x*x^-1 -> empty, with empty product certificates.
- Q_i -> empty seeds and one balanced split per cyclic rotation of either sign.
  It does not enumerate every split of every rotation.
- Shortlex orientation: longer words decrease; equal-length ties use the fixed
  signed-integer alphabet order. Leftmost matches are preferred, then longest
  left side, then rule creation order.
- Simplification of **both sides of every new equation** by retained rules.
  Old rules are retained, rather than deleted or silently reinterpreted.
- All compatible intersecting placements of two left sides: proper overlaps,
  inclusions, self-overlaps and either positional direction. Disjoint placements
  commute and do not require an ambiguity equation.
- A priority queue favoring the sum of the two left-side lengths, with FIFO
  ties. This is a cheap overlap-length estimate, not a measured optimal policy.
- Target-directed stopping: accept cheap seed reductions first; after a pair
  adds rules, stop if all requested targets have identity certificates.

There is no backtracking queue of target words. Strictly decreasing rules
prevent rewrite loops. This moves possible growth into the equation/pair
queue and proof storage; it does not make the word problem decidable.

Every worker shares one one-second monotonic budget across seeding, completion
and target reductions. It has at most 256 retained rules (including cancellation
rules), 4,000 distinct queued rule pairs cumulatively, word/overlap length 128,
2,000 factors in an equation/reduction proof, and 2,000 reduction steps per
reduction call. These are completeness-limiting caps. Deadline checks occur
inside the loops; OS limits also cover allocation and operations between checks.
Oversized words/overlaps and missing pairs are logged as truncations. Other
budget exhaustion stops the relevant search. No exhausted queue is promoted
to a confluence assertion, even without truncation.

Each measured worker uses the unchanged [resource guard](../experiments/resource_guard.py):
512 MiB address space, three CPU seconds, five external wall seconds, 8 MiB
per output file. The entire comparison driver, including its tiny direct
nonabelian probe, also runs under that guard (six CPU / ten wall seconds).
CPU, memory and file caps are inherited per-process/per-file hard limits,
not aggregate tree CPU/memory/file totals. The wall guard and child cleanup
cover descendants. No production unrestricted-completion mode is exposed by
the test runner: it accepts only the ten committed fixtures and the specified
finite cyclic toy.

## Certificate invariant and correctness

Let Q_1,...,Q_m be the **actual fixed-quotient relations**, never the raw
presentation relators added as extra killing relations. For an equation l=r,
its stored proof is a flat, ordered product

    l*r^-1 = product_t c_t * Q_(i_t)^(epsilon_t) * c_t^-1

as an equality in the original free group. All words are signed letter lists;
indices refer directly to this fixed input. Every retained equation, including
a critical-pair rule, has such an expanded proof. No opaque reference to a
completion assertion or another rule survives in its certificate.

The constructors preserve this invariant:

1. **Seeds.** Q_i=1 has the one-factor product Q_i. If Q_i^e=U*V, the
   rotation V*U equals U^-1*Q_i^e*U. Splitting V*U=L*T yields
   L=T^-1 with that conjugate certificate. Freely cancelling either side
   preserves the free-group equality.
2. **A rewrite.** Replacing P*l*S by P*r*S gives discrepancy
   `(P*l*S)*(P*r*S)^-1 = P*(l*r^-1)*P^-1`.
   Prefix-conjugate every factor. Consecutive rewrite discrepancies telescope,
   so concatenate their factor lists in execution order.
3. **Simplification.** If D proves l*r^-1, L proves l*l'^-1, and R proves
   r*r'^-1, the simplified equation l'=r' has product `L^-1 * D * R`.
4. **Orientation.** Swapping l and r reverses the factor order and negates
   each factor sign. It does not just negate signs in the original order.
5. **Critical pairs.** If a common overlapping word w takes two one-step
   paths to a and b, with discrepancies A=w*a^-1 and B=w*b^-1, then
   `a*b^-1 = A^-1 * B`. Simplify and orient this equation by steps 3–4.

Thus every emitted identity target is in the normal closure of the specified
Q_i. Termination of rewriting follows from the context-compatible shortlex
order, including free cancellation. **Soundness of a positive proof does not
require confluence or complete overlap enumeration.** Nonidentity remainders,
truncated completion and timeouts remain unresolved. A negative verdict in
the tests comes only from the existing independent finite-image obstruction.

The separate [checker](../scripts/check-completion-certificate.py) imports
only the existing independent free-cancellation checker, never the completion
engine. It reconstructs Q from the original problem, verifies candidate
membership in N, checks every retained rule's product directly, checks
orientation, and independently checks each claimed target product. This
checks algebraic consequences; it does not certify the heuristic's speed,
confluence or the absence of other consequences. Flat products intentionally
trade larger artifacts for a small acceptance boundary.

## Recorded comparisons

Exact words, output proofs, all retained rules, settings, checker results,
commands, CPU/wall/RSS measurements and termination/cleanup records are in
[the comparison summary](../benchmarks/results/certified-completion-small-2026-10-28/comparison/summary.json).
Times below are single in-process search measurements, including quotient
construction and indexing/seeding. They exclude interpreter startup and
independent checking. RSS is wait4 worker peak KiB, including startup; it is
not the incremental memory occupied by the algorithm. The summary also
records supervised wall time and user/system CPU separately.

| Fixture | Checked spanning status, BFS / completion | Search seconds, BFS / completion | Peak RSS KiB, BFS / completion | Target product factors, BFS / completion |
| --- | --- | ---: | ---: | ---: |
| C3_full | proved / proved | 0.000510 / 0.000390 | 11904 / 11904 | 1 / 1 |
| C3_power_basis | proved / proved | 0.000716 / 0.000436 | 11904 / 11904 | 2 / 3 |
| C3_missing_p3 | disproved / disproved | 0.000456 / 0.001322 | 11904 / 11904 | 0 / 0 |
| C3_missing_p2 | disproved / disproved | 0.000341 / 0.000648 | 11904 / 11904 | 0 / 0 |
| C3_power_basis_p2 | proved / proved | 0.000939 / 0.000522 | 11904 / 11904 | 2 / 4 |
| C3_redundant | proved / proved | 0.003128 / 0.000792 | 12032 / 11904 | 3 / 3 |
| V4_full | proved / proved | 0.001747 / 0.004507 | 12032 / 12032 | 3 / 14 |
| V4_conjugated | proved / proved | 0.001782 / 0.005288 | 12032 / 12032 | 3 / 21 |
| V4_missing_commutator | disproved / disproved | 0.018789 / 0.032021 | 12544 / 12032 | 2 / 6 |
| free_rank2 | proved / proved | 0.000013 / 0.000041 | 11904 / 11904 | 0 / 0 |
| cyclic7_long_powers (finite toy) | unresolved / proved | 0.019315 / 0.006157 | 13184 / 12032 | 0 / 5 |

For the original ten, total measured search time was 0.028420 seconds for BFS
and 0.045966 seconds for completion. Completion is slower overall, particularly
on V4. Seven positive original fixtures finish after seeding without any
critical pairs being processed; their behavior does not demonstrate a benefit
from completion. Missing-candidate controls still spend effort on equations
that cannot kill the independently obstructed target. Proof-carrying
simplification can also yield longer target products: V4_conjugated has 21
factors rather than three. There is no general certificate-size advantage.

The artifacts distinguish target-only JSON byte sizes, retained-rule JSON
bytes and whole records, which include shared mathematical input. Whole-record
sizes are not like-for-like proof sizes: the old producer emits targets but
not its internal index; the new producer emits every retained rule and proof.
The new checker independently accepts **166 retained rules** across the eleven
completion records and 27 certified target occurrences across both methods.
The additional nonabelian overlap probe has twelve checked rules. Targets
repeated in two methods are not distinct mathematical results.

These single measurements are functional benchmarks, not a statistically
controlled speedup study. Development runs used the same bounded small inputs;
the committed comparison is one final run per method/case. Early test-harness
assertions were corrected to expect the long-power BFS case to be unresolved
and to force a genuine critical pair in the nonabelian probe. No rejected
mathematical certificate was accepted or used to justify an algorithm change.

## Long powers and adversarial checks

The extra fixture is the **finite cyclic group C7**, with original relator
x^7, prime seven and candidate x^14. It is not any arithmetic-group presentation.
The normal-subgroup membership certificate is x^14=(x^7)^2. Its fixed Q has
empty commutator row, Q2=x^49 and Q3=x^14. Completion proves

    x^7 = (x^14)^4 * (x^49)^-1,

with five independently checked conjugate factors (one conjugator is a power
of x and freely commutes with that pure power). It uses twelve retained rules,
20 processed rule pairs, maximum equation length 49, and no truncation. The
search stops when the target is certified, not when confluence is established.
The old search builds 2,926 indexed instances but exhausts its two reachable
states under growth-six; this is an incomplete-search result, not nonmembership.
Here deriving short consequences of long powers works without equation growth
past the longest input. This is a capability example, not evidence that mixed
arithmetic relators have a comparable structure or cost.

Thirteen acceptance checks cover corrupted input-rule signs, wrong inverse
orientation, unsound free simplification, unsupported short rules, reuse from
a stronger quotient after removing its candidate, insertion of raw original
relators into Q, missing candidate membership, forged target identities,
a valid equation oriented increasingly, corrupted critical-pair conjugators
and signs, genuine nonabelian overlapping paths, and a rule-limited true
positive that remains unresolved. The latter allows only the two cancellation
rules in C3_power_basis; no negative conclusion is accepted.

All eight resource probes were repeated, including intentional memory, CPU,
wall and output-file exhaustion and escaped-session descendant cleanup. All
passed. The existing eleven verification commands and three constrained
small workers also passed: prior presentation/candidate membership products,
linear witnesses, previous corrections, original GAP/KBMAG controls and the
old small suite remain valid. [Regression records](../benchmarks/results/certified-completion-small-2026-10-28/regression/stage1/verification-summary.json)
retain exact commands and logs. One whitespace-heavy provenance log is
losslessly gzip-compressed; no mathematical output is removed. The previous
one-pilot arithmetic evidence is unchanged and replays independently.

## Recommendation and proposed arithmetic control — not executed

**Do not scale this generic implementation to all fifteen arithmetic targets
on the evidence above.** The full fixed quotient is much larger than the toys,
old rules are not interreduced, matching scans the rule list, many redundant
seed equations are retained, and flat proof expansion costs memory. The queue
has not been profiled on arithmetic inputs. Fewer target states need not mean
less total computation. No prediction of replacing the historical multi-day
calculations follows.

The most promising alternative is a **targeted, certificate-producing power
and conjugation simplifier**, rather than a larger generic completion budget.
For pure powers of the same verified word, extended Euclid can compile a
Bezout identity directly into products of the already certified power
relations. Inversion/conjugation identities can supply the requisite powers,
as in the existing elementary z^14 and z^7 certificates. This exploits the
successful toy mechanism without enumerating unrelated critical pairs. It
has not been implemented or timed here; it must first be compared with this
engine on small conjugation/power fixtures, including obstructed ones.

For a separately authorized prime-7 **control**, propose just the already
known target R12=z^7 from the three actual Q relations Q140=[a,z^7],
Q204=z^49 and Q225=z*a*z*a^-1. This would test whether completion recovers a
known mixed conjugation/power identity, not search the fifteen unresolved
targets or improve the certified count. Seed those three in short-length
order, preserve their full-Q indices with an explicit checked reindexing, and
use the same original six free generators. No raw Rj may be inserted.

Proposed limits: one shared search second; 128 retained rules; 1,000 cumulative
rule pairs; word/overlap length 128; 2,000 proof factors; 2,000 reduction steps
per call; 512 MiB address space; three CPU seconds; five external wall seconds;
8 MiB per output file. No retry or limit increase. Abort unless the existing
certificates and safety checks replay. Translate every retained rule and target
product back to the original 236-row Q and independently cancel it. Save rules,
full input, source hashes, all limits, proof sizes, termination and resources.
A timeout or nonidentity remainder is unresolved, even though this control
identity is already known by another proof.

This is a proposed diagnostic, **not authorization or a ready arithmetic
launcher**: the whitelist runner deliberately cannot execute it. An adapter
for the three-row reindexing and control record would be required. If it fails
or emits much larger proofs, pursue the targeted algebraic compiler instead
of broadening completion. Even if it succeeds, another explicitly authorized
plan would be required before testing unresolved arithmetic targets.

## Reproduction without arithmetic search

```sh
# Check every saved small positive product, rule and independent obstruction:
python3 scripts/replay-completion-tests.py \
  --base benchmarks/results/certified-completion-small-2026-10-28/comparison
# One independent check, without importing the completion engine:
python3 scripts/check-completion-certificate.py \
  benchmarks/results/certified-completion-small-2026-10-28/comparison/cyclic7_long_powers.completion.json
# Re-run only the whitelisted small comparisons into a new directory:
python3 experiments/resource_guard.py --output /tmp/new-completion-driver \
  --cpu-seconds 6 --wall-seconds 10 -- \
  python3 scripts/test-certified-completion.py --output /tmp/new-completion-tests
```

All additions are experimental code, tests, documentation and new evidence.
Original GAP algorithms, published presentations, research artifacts and
previously verified certificates are unmodified; main is not merged or edited.

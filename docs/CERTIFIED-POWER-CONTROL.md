# Targeted powers, conjugation, and the single prime-7 control

The targeted simplifier passes the original ten fixtures, the long-power toy,
and new noncommutative controls. In **one authorized arithmetic control**, both
it and the unchanged certified completion engine recover the already known
identity R12=z^7. Every retained rule and positive target product was independently
checked against its original relations. **No previously unresolved arithmetic
target was attempted or certified.** The total remains five of 32; full
spanning and the historical twelve-word assertion remain unverified.

## 1. Exact mathematical operations and their certificates

[certified_power.py](../experiments/certified_power.py) is a limited identity
compiler, not a completion or general word-problem solver. It accepts one fixed
list of base relations Q_i. Every retained equation w=1 carries the free-group
identity

    w = product c_j Q_(i_j)^(epsilon_j) c_j^-1.

No rule is imported from a stronger quotient. For relation-module fixtures the
old independent checker reconstructs Q and checks candidate membership in N.
For the nine additional word-problem fixtures, Q is simply the exact listed
base presentation. Those controls are not homology calculations.

### Powers of exactly the same free word

Freely reduce an input word, strip its conjugating prefix, and detect repetition
of its cyclically reduced core. Choose a canonical primitive cyclic word u,
allowing cyclic rotations and inverse orientation. The algorithm explicitly
retains q and e satisfying the **free-group equality**

    w = q u^e q^-1.

This is recognition of literal repeated free words, not extraction of roots
in a presented group. A certificate for w gives one for u^e by conjugating
all factors by q^-1. Negative exponents invert the product in reverse order.
Canonicalization of cyclic conjugates uses the matching conjugator, not merely
an equality of cyclic strings. The same conversion applies to target words.

If certified powers u^m and u^n are available, extended Euclid gives
am+bn=d=gcd(m,n). The certificate for u^d is the ordered product of the existing
u^m certificate a times and the u^n certificate b times, using inverse products
for negative coefficients. This is valid because all factors are powers of
**the same free word**; their concatenation freely reduces to u^(am+bn).
Powers of different words are never collected from exponent arithmetic.
The target q u^e q^-1 is certified only if the stored d divides e, with the
appropriate multiplicity and conjugator explicitly restored.

### Inversion plus centrality

The implemented additional pattern is deliberately narrow: for a cyclically
reduced free word u and a **one-letter** conjugator h, recognize certified
relations, including cyclic conjugates/inverses,

    S = u h u h^-1,
    K = [h,u^k] = h^-1 u^-k h u^k,  k > 0.

It does not infer centrality of u from centrality of u^k. Instead the following
identity holds in the free group:

    u^(2k) = (h u^k) K^-1 (h u^k)^-1
              * product_(j=1..k) u^-j S u^j.                  (1)

The ordered product on the right telescopes: its second part is
`h u^k h^-1 u^k`; multiplying the first part gives u^(2k). Substitute the
certificates for S and K, preserving product order and all conjugators.
If the centrality input involves u^-k, use the exact identity

    [h,u^k] = u^-k [h,u^-k]^-1 u^k.

Then feed the resulting power to the common-root Euclidean step. Recognizers
require the same literal h and matching u powers after the recorded cyclic
transformations. Different h, a commutation equation in place of inversion,
or centrality of an unrelated word cannot enable (1).

General relations h u^m h^-1=u^n, arbitrary multi-letter h, collection in a
polycyclic presentation, and identities among arbitrary mixed relators are
**not** implemented. This limited scope prevents the module from growing into
another general completion engine.

### Independent acceptance

[check-power-certificate.py](../scripts/check-power-certificate.py) imports
only the existing independent free-cancellation checker. It imports no search,
power recognition, Euclid or adapter implementation. It checks every retained
equation's flat product, orientation and free alphabet, and each target proof.
Optional negative verdicts require an independently verified finite permutation
image. An unrecognized target, exhausted limit or unsuccessful completion is
always unresolved.

[restricted_identity.py](../experiments/restricted_identity.py) translates
local indices to original indices. The arithmetic-control checker independently
reconstructs the input quotient, checks the exact subset words, repeats both
local and original-Q product checks, and compares the reindexing factor by
factor. It does not import or trust this adapter. No opaque derived equation
or unchecked generator substitution is accepted.

## 2. Small-case validation and comparison

The [new fixture file](../tests/fixtures/power-conjugation-small.json) contains
nine additional exact presentations. The comparison uses all ten original
fixtures and the previous C7 long-power toy, for **twenty cases and three methods**.
A separate rule-limited true-positive case makes 61 measured worker records.
All three methods have a one-second shared search budget per case. The old
methods are unchanged: BFS uses 20,000 indexed instances / 1,000 states /
growth six; completion uses 256 rules / 4,000 queued pairs. The power compiler
uses 128 retained equations, word length 128, 2,000 factors and 2,000 counted
operations total. It has no critical-pair queue or general replacement search.

Every measured worker has inherited hard limits of 512 MiB address space,
three CPU seconds and 8 MiB per output file, with five external wall seconds.
The driver also runs under the unchanged guard. Imports of all three modules
occur before the measured search interval for every worker. Individual worker
CPU/wall/RSS includes startup and those common imports; the search column
excludes them. Peak RSS is a process high-water mark, not incremental engine
memory. Results are **one final measurement per method/case**, not a controlled
statistical speedup study. Development iterations used only these bounded
small inputs and did not touch the arithmetic control.

Exact words, settings, proof bytes/factors, failures, retained rules, negative
witnesses, source hashes, raw streams and individual measurements are in
[the summary](../benchmarks/results/power-conjugation-small-2026-10-28/comparison/summary.json).

| Case | Certified requested targets, BFS / completion / power | Search ms, BFS / completion / power | Target factors, BFS / completion / power |
| --- | --- | ---: | ---: |
| C3_full | 1/1 / 1/1 / 1/1 | 0.355 / 0.338 / 0.129 | 1 / 1 / 1 |
| C3_power_basis | 1/1 / 1/1 / 1/1 | 0.557 / 0.918 / 0.169 | 2 / 3 / 2 |
| C3_missing_p3 | 0/1 / 0/1 / 0/1 | 0.687 / 0.988 / 0.163 | 0 / 0 / 0 |
| C3_missing_p2 | 0/1 / 0/1 / 0/1 | 0.348 / 1.760 / 0.180 | 0 / 0 / 0 |
| C3_power_basis_p2 | 1/1 / 1/1 / 1/1 | 0.687 / 0.599 / 0.256 | 2 / 4 / 2 |
| C3_redundant | 2/2 / 2/2 / 2/2 | 2.975 / 1.221 / 0.297 | 3 / 3 / 3 |
| V4_full | 3/3 / 3/3 / 3/3 | 1.712 / 4.183 / 0.805 | 3 / 14 / 3 |
| V4_conjugated | 3/3 / 3/3 / 3/3 | 1.427 / 4.443 / 0.705 | 3 / 21 / 3 |
| V4_missing_commutator | 2/3 / 2/3 / 2/3 | 8.907 / 40.572 / 0.883 | 2 / 6 / 2 |
| free_rank2 | 0/0 / 0/0 / 0/0 | 0.015 / 0.038 / 0.017 | 0 / 0 / 0 |
| cyclic7_long_powers | 0/1 / 1/1 / 1/1 | 20.902 / 5.987 / 0.290 | 0 / 5 / 4 |
| dihedral_power_control | 0/1 / 1/1 / 1/1 | 26.038 / 7.598 / 0.399 | 0 / 42 / 13 |
| conjugated_inverse_cyclic_powers | 0/1 / 1/1 / 1/1 | 17.529 / 6.423 / 0.923 | 0 / 4 / 2 |
| negative_conjugator_composite_root | 0/1 / 1/1 / 1/1 | 49.432 / 6.161 / 1.234 | 0 / 13 / 13 |
| invalid_power_distribution | 0/1 / 0/1 / 0/1 | 0.430 / 0.768 / 0.110 | 0 / 0 / 0 |
| invalid_root_centrality | 0/1 / 0/1 / 0/1 | 33.143 / 1000.074 / 0.163 | 0 / 0 / 0 |
| mismatched_conjugators | 0/1 / 0/1 / 0/1 | 35.226 / 157.835 / 0.243 | 0 / 0 / 0 |
| inversion_without_centrality | 0/1 / 0/1 / 0/1 | 23.960 / 33.469 / 0.275 | 0 / 0 / 0 |
| commutation_is_not_inversion | 0/1 / 0/1 / 0/1 | 37.478 / 28.434 / 0.160 | 0 / 0 / 0 |
| different_roots_do_not_combine | 0/1 / 0/1 / 0/1 | 2.260 / 9.303 / 0.215 | 0 / 0 / 0 |

The three original nonspanning candidate lists still have their independently
checked finite-image obstructions. V4_missing_commutator has two valid positive
targets and a third obstructed one. The six new adversarial target identities
are all independently disproved by exact permutation images; **each search
itself reports unresolved**, never nonmembership. Thus zero successes in the
table is not the source of a negative conclusion.

The three new positive noncommutative cases are:

- `dihedral_power_control`: S=x*h*x*h^-1, [h,x^3] and x^21 imply x^3.
  For example x=(0 1 2), h=(1 2) gives a nonabelian S3 image;
  commutativity cannot explain
  the proof. Equation (1) supplies x^6, then Euclid uses 6 and 21.
- `conjugated_inverse_cyclic_powers`: different conjugates of (x*y)^14 and
  an inverse cyclic rotation raised to 21 imply a specified conjugate of
  (x*y)^7. Nielsen generators exhibit the quotient as C7 * F2, so this is
  a genuinely noncommutative presentation, not a commuting-letter shortcut.
- `negative_conjugator_composite_root`: u=x*z, h=y^-1, with inversion,
  [h,u^3] and u^21. The negative h and composite word u test literal sign
  and conjugator handling. Setting x=(0 1 2), z=1, y=(1 2) gives a nonabelian S3 image.

BFS leaves all three positive noncommutative cases unresolved under its
finite limits. Both completion and the compiler prove them. The new negative
controls prohibit distributing (x*y)^2 into x^2*y^2, extracting centrality of
x from centrality of x^2, mixing different conjugators, using inversion without
centrality, treating commutation as inversion, and applying Euclid to different
roots. Their finite obstructions are retained in the fixtures and replayed.

Sixteen acceptance checks additionally include altered factor signs, unsupported
conjugation consequences, reuse after changing the base centrality relation,
out-of-alphabet conjugators, increasing orientation, a forged nonmembership
claim, a checked noncontiguous/permuted indexing adapter, malformed adapter
indices, and a one-rule true-positive case that remains unresolved.
Independent replay checks **778 retained equations** across the 61 records;
47 successful target occurrences include repetitions across methods.

On the original ten cases, summed search times were 0.017672 seconds for BFS,
0.055061 for completion and 0.003606 for the compiler. On the three new positive
noncommutative cases the respective sums were 0.093000, 0.020182 and 0.002557.
These functional measurements favor the compiler on **recognized structures**;
no asymptotic or arithmetic speedup follows from submillisecond differences.
The twenty-case peak worker RSS ranges were 12,032–13,440 KiB (BFS),
11,776–13,312 KiB (completion) and 12,032 KiB (power), dominated by the common
Python runtime/imports. There is no supported substantial memory reduction.

The long-power toy produces four target factors with Euclid, versus five with
completion; the conjugated-power example produces two versus four; the dihedral
control produces thirteen versus forty-two. Artifact byte sizes are recorded
separately for targets and retained equations. Whole output files also contain
shared mathematical input; BFS does not serialize its internal index, whereas
the other methods serialize all retained rules. Smaller or faster proofs on
these selected structures do not establish superiority on general mixed inputs.
On invalid_root_centrality completion reached its one-second budget and on
mismatched_conjugators it reached its rule budget. Those are unresolved searches,
with nonmembership supplied separately by their finite witnesses.

## 3. The one authorized prime-7 control

The eight existing OS safety probes were repeated, including deliberate memory,
CPU, external wall and output exhaustion and escaped-session child cleanup.
All passed. Eleven previous verification commands and three constrained small
workers also passed. The old completion evidence, five arithmetic products,
presentation maps, candidate membership proofs and old pilot manifests replayed
unchanged. The new small-suite/adversarial/adapter gate passed before launch.

[run-prime7-power-control.py](../scripts/run-prime7-power-control.py) atomically
reserved **one** attempt before starting. It froze the full existing blueprint
SHA256 `d33076b1c1b20c9950349645e77c0dbcebe9c8e326ba77dd041b6b696b134a60`,
the three-row input, gates and source snapshots. No retry or limit increase
occurred. The only search target was original R12=z^7. Restricted local rows,
ordered by length, were:

| Local index | Original index | Exact word |
| ---: | ---: | --- |
| 1 | Q225 | z*a*z*a^-1 |
| 2 | Q140 | a^-1*z^-7*a*z^7 = [a,z^7] |
| 3 | Q204 | z^49 |

No other Q relation or raw original relator was inserted. Both methods started
from these same three original relations; completion did **not** import the
power compiler's derived rules or target proof. The compiler ran first, with
at most 32 equations; completion received the remainder of the **combined
128-rule ceiling**, including its cancellation rules. A single SIGALRM deadline
covered both methods, seeding and completion, without resetting the clock.
Retaining five compiler equations left a completion ceiling of 123. This is
a stricter allocation of the authorized cap, not an increased budget.

Budget-accounting detail: each queued pair of rules can have several
compatible overlapping placements. The engine does not count these placements
separately. The recorded 903/688 counts are **rule-pair jobs**, not counts of
individual critical equations. This follows the earlier report's proposed
`max_pairs` setting; a 1,000-placement bound is not independently attested by
this trace. No additional arithmetic run was made to refine that measurement.

Other enforced settings: `max_pairs=1000`, the existing engine
limit on distinct queued pairs of rules (903 queued / 688 processed); word/overlap length 128; 2,000 proof factors; 2,000 reduction
steps per completion call; 512 MiB hard address space; three hard CPU seconds;
five external wall seconds; 8 MiB per output file. The worker read back the
inherited hard AS/CPU/FSIZE limits and asserted their exact values before
searching. Its source contains only this target/subset. JSONL checkpoints allow
complete records to be retained even if a later method is interrupted.

| Recorded quantity | Result |
| --- | ---: |
| Compiler equations / target factors | 5 / 25 |
| Compiler counted operations / truncations | 237 / none |
| Compiler result elapsed on shared clock | 0.001700 s |
| Completion rules / target factors | 42 / 90 |
| Completion processed / queued pairs | 688 / 903 |
| Completion reduction steps / truncations | 807 / none |
| Completion result elapsed on shared clock | 0.046225 s |
| Total shared search wall (including emitted records) | 0.047328092 s |
| Total retained rules, independently verified | 47 |
| Supervised worker wall | 0.143383 s |
| Worker CPU user / system | 0.134024 / 0.005024 s |
| Peak worker RSS | 11,008 KiB |
| Raw stdout / stderr bytes | 31,512 / 0 |
| Worker return / termination / descendant cleanup | 0 / completed / verified |

These are sequential methods in one shared worker: there is no separately
measured per-method memory or CPU. Startup, serialization and shared-clock
overhead differ from the small-suite search timing definition. The control
is functional evidence of recovering a known identity, not a performance
comparison with the historical multi-day computation.

[check-power-control.py](../scripts/check-power-control.py) independently
checked **every one of the 47 rules** in both local and full-Q indexing and
both target products against the original 236 relations. It checked the
adapter factor by factor. Exact products, source snapshots, inputs, raw streams,
termination and measurements are retained in
[the control directory](../benchmarks/results/prime7-power-control-1-2026-10-28/).

The compiler's shorter certificate is easy to understand. Let T denote the
eight-factor right side of (1) with u=z, h=a, k=7, so T=z^14 as a free word.
Then its accepted 25-factor target product is

    z^7 = T^-3 * Q204,                                      (2)

because -3*14+49=7. The old 33-factor certificate used T^4*Q204^-1 instead.
Both are exact positive certificates; the old one and its evidence are
preserved. The completion engine's ninety-factor output also checks, despite
its less economical derivation. This is a certificate-size observation for an
already known identity, not a new homology result.

No new unit-vector direction is added to the verified linear witness system:
R12 was already certified. The original certified targets remain
**3,5,9,12,15**. The other **27** remain unresolved. The fifteen sufficient
unresolved targets remain 1,2,4,6,7,8,10,11,13,14,18,26,28,29,30; none was searched
in this control. The six b0-interpreted corrected words remain legitimate
kernel classes, with spanning conditional on the unverified twelve-word
spanning certificate; no independence or nontriviality follows.

## 4. Research strategy and the next mathematical question

**Established algebraically:** the exact power-normalization conjugations,
common-root Bezout product construction, and identity (1), with no commuting
assumptions on unrelated words. The finite spanning criterion in the earlier
report remains unchanged.

**Independently certified:** all recorded positive small-case identities and
the two restricted z^7 products. The finite negative witnesses establish only
their specified toy obstructions. Existing presentation/membership certificates
remain valid.

**Measured experimentally:** the tabled times, memory high-water marks, proof
sizes, and successful termination. This is evidence of useful short consequences
for these recognized patterns. It is not evidence that the full 236-row
arithmetic quotient becomes tractable, or that a multi-day run has been sped up.

**Conditional/unresolved:** full spanning, all remaining arithmetic identities,
transfer to new primes, and any resulting new homology theorem. Even perfect
verification of this control cannot address them.

The compiler is worth keeping as a small certified algebraic tool. It avoids
irrelevant critical pairs and reliably handles the tested power structures.
There is no present evidence that its narrow inversion/centrality patterns
supply the mixed identities needed for the fifteen targets. In particular,
most targets are commutators or longer unit/b relations, not two powers of
one word. Building increasingly general recognition infrastructure would defer
the actual mathematical question.

Of the fifteen, **R7=a^4** is the most direct next structural test. This is a
static observation from the unchanged target list, not another experiment.
Its fixed-quotient power row is Q199=(a^4)^7=a^28. That row alone cannot justify
extracting a fourth power or seventh root. The control's inversion equation
acts on z, so it does not supply a missing a-power relation.

**Single most informative next experiment (proposed, not run):** seek an explicit
full-Q product for `(a^4)^m` with 7 not dividing m, using the existing candidate
and conjugation identities, then compile its Bezout combination with Q199 into
a verified certificate for R7=a^4. A direct R7 certificate also counts. Any completion component of a future
plan must explicitly distinguish and budget rule-pair jobs and individual
overlap placements. This
would test transfer to one genuinely unresolved sufficient target, rather than
repeat the known control or expand the software framework. Any search must
have a separately approved bounded plan; none was launched here. Success is
an original-Q product checked by free cancellation. Failure to find the
required bridge identity remains unresolved, not a lower bound or obstruction.

If this focused test exposes genuinely non-power interactions, proof-producing
KBMAG instrumentation becomes a better next engineering option than adding
more general patterns to this compiler. That would still need proof provenance
for every used rule; a nonconfluent nonidentity remainder cannot settle the
question. There is no evidence yet to abandon verification for unrelated new
bounds, or to promise that either software approach will produce publishable
results. A certificate for an actual unresolved relation is the meaningful
next research milestone.

## 5. Reproduction and preservation

Certificate-only replay, with **no search**:

```sh
python3 scripts/replay-power-experiments.py \
  --small benchmarks/results/power-conjugation-small-2026-10-28/comparison \
  --control benchmarks/results/prime7-power-control-1-2026-10-28
python3 scripts/check-power-control.py \
  --base benchmarks/results/prime7-power-control-1-2026-10-28
```

To repeat only the whitelisted small suite, use a new output directory:

```sh
python3 experiments/resource_guard.py --output /tmp/new-power-driver \
  --cpu-seconds 6 --wall-seconds 40 -- \
  python3 scripts/test-certified-power.py --output /tmp/new-power-small
```

Do **not** relaunch the arithmetic-control controller: the authorized attempt
has been consumed. No further arithmetic experiment is authorized by this
report. The original GAP algorithms, group presentations, papers, historical
computations and previously certified evidence are unchanged. All changes
are experimental code, new fixtures, reports and new evidence on
codex-development; nothing is merged into or modified on main.

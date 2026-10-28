# Prioritized arithmetic-computation optimization plan

This is a proposal, not implemented optimization. `Algorithms.g` and every
original presentation remain unchanged. Full expensive computations remain
deferred; every initial experiment should fit the existing small-case limits.
The [presentation audit](PRESENTATION-PROVENANCE.md) and
[recorded baseline](BASELINE.md) define what is currently verified.

## Mathematical invariant to preserve

For `G=F/N`, q prime, let `E=N/([F,N]N^q)`, `t` be the rank of the relator
exponent lattice, and `a=dim Tor(H1(G;Z),F_q)`. The existing method uses

```
dim H2(G;F_q) = a + dim E - t,
a <= dim H2(G;F_q) <= a + e - t,
```

where `e` is the size of a certified spanning candidate set for E. With all
m defining relators as candidates, the initial bound is `a+m-t`; certified
deletions can only lower it. The rank `t=c-b` is already available from the
current scalar stages. No change of presentation, rewriting heuristic or
caching rule may invalidate candidate coverage or a reduction certificate.

## 0. Verify inputs and paper dependencies before timing comparisons

Use the [completed uploaded-version audit](PAPER-AUDIT.md) and retain explicit
group identifications, source maps, and source-version labels.
Use the actual matrix SL(2,F5) as an independent homology reference; retain
C5 as a separate test with nonzero mod-5 homology. Do not relabel a stored
input or silently substitute a guessed corrected exponent. Resolve the
G11 mismatch with Anton's perfect SE2 before optimizing it as that group.
Recover the prime-7 reduced inputs and clarify R20's displayed reductions
and explicit cycle representatives before using its final six words as a
certified spanning set. The [proof reexamination](PRIME7-PROOF-REEXAMINATION.md)
confirms that the literal last-six auxiliary images have rank six; no
independence of the six homology classes is required.

**Small tests:** existing presentation sanity checks, the new independent
matrix-group multiplier check, cyclic groups, C2 x C2, and SL(2,3).
**Acceptance:** input word lists, group maps, expected results, and source
citations are explicit. Claims about a target group never rest on a label
or matching abelianization alone.

## 1. Reproduce a published fixed-quotient spanning certificate

Anton v1 Lemma 7.4 (pp.21–22) already supplies a more targeted prime-5
strategy than independently rebuilding a rewriting system for every relator.
Choose its eleven-word list e, form the single quotient
`F/[F,N]N^5<e>`, and reduce the 28 complementary relators in the same system.
If all reduce to identity, e spans the relation quotient. Its image rank is
11, giving a matching lower dimension and vanishing of the kernel.

The source comparison verifies the e/n partition and rank 11 without
completion. The expensive 28 reductions remain unrun. This is a published
certificate strategy to reproduce, **not a new method or a demonstrated
speedup**. One fixed completion can be harder than the many stronger
quotients used by the greedy algorithm; completion-call counts are not
runtime factors.

**Small tests:** fixed-quotient batch certificates for cyclic examples and
identified finite groups. Include C2 x C2 with two candidate squares: their
relation images alone must not be declared to span the full relation quotient
without reducing the omitted commutator. Use actual SL(2,3), and retain C5
with its correct name. Compare returned bounds with unchanged controls.
**Acceptance:** every omitted relator has a positive identity witness; e spans
by those witnesses, not just by its abelian image rank. Record confluence but
allow sound positive reductions from a nonconfluent system; unresolved words
mean the batch certificate is unfinished. Only a later explicitly authorized
arithmetic pilot should attempt A08's eleven-word case.

## 2. Avoid completion when an existing mathematical bound already settles the answer

If `a+e-t` meets a certified lower bound, the dimension is settled. In
particular, `e=t` gives the lower bound `a` exactly. An implementation could
stop greedy elimination at that point, avoiding attempts to prove further
independence. This uses the same relation-quotient method, not a new homology
theory. It requires a separate reviewed code change and a clear convention
for candidate reductions not executed after stopping.

Two small stored examples already illustrate the opportunity without any
optimization run: `Free3/R3` and `Free5/R5` each have m=t=2. Their initial
bound equals their Tor lower bound, so no Knuth–Bendix completion is needed
to determine their H2 dimensions mathematically. The current code still runs
two word-test completions. This observation also explains why these easy
examples cannot predict performance on the arithmetic cases.

For the checked-in arithmetic cases at matching coefficient primes, the
measured scalar data give these *initial* upper bounds before elimination:

| Stored input | a | m | t | Initial bound a+m-t |
| --- | --- | --- | --- | --- |
| G3 / q=3 | 0 | 21 | 8 | 13 |
| G5 / q=5 | 0 | 39 | 11 | 28 |
| G7 / q=7 | 0 | 64 | 14 | 50 |
| G11 / q=11, as stored | 0 | 123 | 19 | 104 |

These are deductions from spanning and the measured scalars, not reproduced
sharp historical bounds or arithmetic vanishing results. For G3/G5/G7,
reaching e=8/11/14 would settle vanishing at those coefficients. Whether a
particular ordering reaches that point cheaply is unmeasured. G11 remains
subject to the identification gate.

**Small tests:** compare answers and certificates with the unchanged routine
on both zero and nonzero homology cases; confirm that no positive lower bound
is inferred just from an incomplete normal-form computation.
**Acceptance:** same justified result, fewer measured completion calls, and
explicitly marked unexecuted reductions. A timeout remains unfinished.

## 3. Add cheap one-sided linear certificates before hard word tests

For a candidate x and the other candidates S, take their exponent-sum vectors
modulo q. If the vector of x is outside the F_q span of the vectors of S,
then x is nontrivial in the test quotient: every generator–relator commutator
has zero exponent vector, every q-th power has zero vector modulo q, and
every killed candidate maps into that span. This is a rigorous certificate
to retain x without completing a rewriting system.

The converse is false: a word with zero exponent vector can still be
nontrivial. A failed linear test must fall through to the original word
test, not authorize deletion. Commutator candidates and torsion examples
are essential negative controls. This precheck may avoid some independence
tests, but no arithmetic call-count or runtime saving has been measured.

**Small tests:** independent exponent vectors, dependent vectors, zero-vector
commutators, and C3 at characteristic 3 (where a nontrivial relator class has
zero exponent vector modulo 3). Compare every certificate to a completed
small-group rewriting calculation.
**Acceptance:** no false nontriviality certificates, preserved spanning, and
accounted fallback calls. Measure linear-algebra overhead as well as saved work.

## 4. Establish effective KBMAG options, then tune search on small derived quotients

The original code writes `tindyint`, while KBMAG reads `tidyint`. Fixing this
in a separate experiment is necessary before interpreting intended tuning.
Keep the old execution path as a control. A08 supplies a concrete comparison:
`maxeqns=500000`, `tidyint=1000`, `confnum=100`; R09 Appendix A p.11
already has the ignored `tindyint` spelling. Compare small grids of supported
tidy intervals, generator/word orders, and candidate orders under equal
budgets, with confluence status, rule counts, output bounds and resource use.
Run each trial independently; record effective serialized options.

Restrictions on stored-rule or overlap lengths can leave a nonconfluent
system. They must never turn an unresolved nonidentity into a proof.
Increasing the equation cap from 500,000 to 10,000,000 is not by itself a
demonstrated speedup or a memory budget.

**Acceptance:** all small expected homology results remain correct; reported
statuses are accurate; reductions supporting deletions remain sound. Distinct
survivor lists or incomplete runs are not automatically mathematical errors.
Only a later authorized bounded arithmetic pilot could establish transfer
of any performance benefit.

## 5. Test certified presentation reduction before larger arithmetic pilots

G3/G5/G7 contain explicit definitions of `b_i` and `w`. Tietze elimination
with retained forward/inverse word maps could reduce the derived presentation
dramatically. For G7, eliminating those eight definitions would change
14 generators/64 relators to 6/56 and reduce the first-test relation count
from 1023 to 447 before further simplification. Those are static counts,
not runtime measurements: substitution may lengthen words and worsen overlaps.

This eight-definition elimination count is only a first static estimate. R09
p.10 reports a further reduced 6-generator/34-relator presentation, while
R20 Proposition 3.2 provides a 6-generator/32-relator version and forward
word maps. Recover and certify those actual source inputs instead of treating
6/56 as the best known target or mixing their candidate counts.

**Small tests:** genuine identified finite groups with redundant generators,
then construction-only comparisons of the arithmetic inputs. Verify all
maps and relator consequences; transport any chosen candidate list correctly.
**Acceptance:** group identification and candidate coverage certified, results
checked in original words, and both word lengths and equation growth recorded.
Do not apply a presentation pattern inferred from smaller primes to G11.

## 6. Cache safe data; investigate rewriting reuse with explicit support

Cache exponent/Smith data and static powers/commutators where the inputs are
identical. Existing measurements put scalar stages at milliseconds, so that
alone cannot justify a claim of eliminating days of work.

Reusing completion data is potentially more valuable and much more delicate.
Successive tests remove and add killed candidates. Rules valid only after
adding a relation are not automatically valid after removing it. Reuse must
retain certificates of the relations supporting each rule, or be restricted
to proven-compatible quotient changes. Completing one fixed central extension
and doing subsequent linear algebra is a possible research experiment; that
fixed completion may be harder than the original quotient tests.

**Small tests:** pairs of stronger/weaker quotients where blindly reused
rules would change the answer, plus repeated identical quotients.
**Acceptance:** support survives every reuse; invalidated rules are discarded;
answers and proof witnesses match fresh controls. Supported checkpointing
should preserve completed progress and mappings; it must not claim that live
external processes or temporary files alone constitute a reusable checkpoint.

## 7. Parallelize independent trials, then expand scope by explicit decision

Independent cases, coefficient primes and parameter trials can be scheduled
in separate bounded processes, with isolated files and memory budgets. The
greedy deletions within one `FindBasis` call are dependent; they cannot be
combined naively in parallel. CPU sharing must be disclosed when comparing
wall times, and core counts must respect actual quotas.

After the earlier gates pass, propose a specific bounded arithmetic pilot
with a verified presentation, target bound, stop criteria, and restart records.
Do not launch a multi-day calculation without a new scope decision.

Additional **coefficient** primes for an existing group and additional
**arithmetic-family** primes are distinct extensions. The latter also require
the presentation theorem's hypotheses and a verified generator-to-matrix
correspondence. Published novelty would need certified mathematical results
and source comparison, not just a faster solver or an improved unverified bound.

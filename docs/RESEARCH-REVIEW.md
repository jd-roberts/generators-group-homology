# Research review and next experiments

Review date: 2026-10-21. Research source revision:
`f684175285d780752f56d1baf6d0bf5f7d87ef33`. Runtime: GAP 4.14.0,
KBMAG 1.6.1 at `82d1c1bea633485d2415df73b6d93ddddb97f721`, Debian 13 x86_64.
This change documents and tests the original implementation; it does not
alter algorithms, presentations, archived results, or theorem statements.

## What reproduced

- All 36 H1 entries in `undergrad-research/Capture2.JPG` agree with the
  checked-in presentations at primes 2, 3, 5, and 7.
- All 16 new smoke checks pass, including small known H2 values, free versus
  torsion contributions, valuations, KBMAG binaries, presentation helpers,
  and both standard and large-parameter paths.
- A bounded sweep attempted all 36 H2 table inputs using **all defining
  relators**, the standard path, and a five-second limit per invocation.
  Eighteen completed and eighteen timed out. No timeout was treated as a value.
- The `G3`, coefficient-3 H2 invocation timed out at ten seconds. H2 for `G5`,
  `G7`, and `G11` was not run in this review. Their presentations were loaded
  and their abelianizations measured.

These time limits are reproducibility probes, not estimates of the total
time needed or claims that the historical work cannot be reproduced.
Raw run logs were retained outside the checkout during the review. The
runner creates equivalent provenance records for subsequent experiments.

In the following table `T` means unfinished at five seconds. Each cell has
the format **archived entry / current computed upper bound**. An archived
entry without an inequality is transcribed as such, but this implementation
still returns an upper bound; this audit does not independently certify every
equality in the image.

| Presentation | F2 | F3 | F5 | F7 |
| --- | --- | --- | --- | --- |
| GL2Z | ≤4 / T | ≤2 / T | ≤2 / T | ≤2 / T |
| SL2Z | ≤2 / T | ≤2 / 1 | ≤1 / 0 | ≤1 / T |
| SL2F2 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| SL2F3 | 0 / 0 | 1 / 1 | 0 / 0 | 0 / 0 |
| SL2F5 | 0 / 0 | 0 / 0 | 1 / 1 | 0 / 0 |
| SL2Zi | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| SL2w | ≤1 / T | ≤2 / T | ≤1 / T | ≤1 / T |
| SL2Zneg5 | ≤3 / T | ≤3 / T | 0 / T | 0 / T |
| PSL2Z | ≤1 / T | ≤1 / T | 0 / T | 0 / T |

The two smaller SL2Z bounds are current observations under the documented
spanning assumptions, not edits to the historical results. Version changes,
candidate order, and undocumented original parameters prevent an exact
historical transcript comparison. The arithmetic problem pictured in
`Capture.JPG` is not numerically answered by the table above.

## Presentation audit

Loading `Library-of-groups.g` gives the following counts. Total word length
means the sum of GAP `Length` over the freely reduced stored relator words.

| Case | Generators n | Relators m | Total word length | n × m commutators per word test | Abelian invariants |
| --- | --- | --- | --- | --- | --- |
| G3 | 8 | 21 | 115 | 168 | `[]` |
| G5 | 11 | 39 | 262 | 429 | `[]` |
| G7 | 14 | 64 | 488 | 896 | `[]` |
| G11 | 20 | 123 | 1654 | 2460 | `[0,2,3,3,3,3,3,3,3,3,3,3]` |

The first three stored groups have trivial abelianization. The stored G11
has a free summand, 2-torsion, and ten 3-torsion factors. This is a concrete
sanity-check discrepancy deserving author/literature review; it is not a
proof of what the intended arithmetic group's abelianization must be.

Unlike the G3/G5/G7 lists, `k11` does not visibly include analogous explicit
definitions of every `b_i` in terms of `z,b,a`, nor a defining word for `w`.
Its displayed `b_i` commutator block also starts at index 1 rather than 0.
Some relations could follow from others, so these observations alone do not
establish the missing mathematical relations or authorize a repair. Compare
the complete presentation to Anton/Roberts and recover original input files
before identifying G11 with the intended family member. The runner retains
`G11` as the **stored presentation**, with no assertion of that identification.

To reproduce the audit interactively after reading the library:

```gap
for pair in [[F3,k3],[F5,k5],[F7,k7],[F11,k11]] do
  Print(Length(GeneratorsOfGroup(pair[1])), " ", Length(pair[2]), " ",
        Sum(List(pair[2],Length)), " ",
        AbelianInvariants(pair[1]/pair[2]), "\n");
od;
```

Other recorded interface issues: the printed library banner uses `SL_2Zw`
where the actual global is `SL_2w`; the fp presentation helper's comment
omits its isomorphism return field; and `PrimePrimaryRank` computes a
valuation sum, not an F_q dimension. No globals or functions are renamed here.

## Performance bottlenecks

1. **A fresh completion for each candidate.** `FindBasis` calls `Reduce_Word`
   once per original candidate. Each call reconstructs powers, generator–relator
   commutators, an fp quotient, and a KBMAG system, and invokes external
   Knuth–Bendix from scratch. With all relators as candidates this means `m`
   completions. The quotient also changes as candidates are eliminated, so
   naively reusing one completed system would change the question being asked.
2. **Large presentations before completion starts.** Each word test constructs
   `n*m + m + |S|` relators before simplification, not merely the original `m`.
   The abelian stages additionally create `n^2` generator commutators,
   including identities and inverse-related redundancy. Larger coefficient
   primes lengthen the relator powers. Increasing a presentation-family prime
   can increase generators, relators, and word lengths together.
3. **Unpredictable rule and automaton growth.** Overlap resolution can generate
   many long equations. `maxeqns=500000` or `10000000` is an equation-count
   cap, not a memory or wall-time budget. More rules can exceed available
   memory without resolving the difficult overlap patterns. The large path
   is not a parallel solver, and `make -j2` only parallelizes compilation.
4. **An ineffective tuning field.** Both paths write `tindyint`, while the
   installed KBMAG serializes `tidyint`. Thus the intended large-path tidy
   interval is ignored. Correcting it could change the search trajectory and
   observed bound, so it should be a separate reviewed experiment.
5. **Repeated integer linear algebra and external-process overhead.** The
   abelian functions repeatedly request invariants on newly constructed
   quotients; there is no explicit project-level cache of exponent matrices,
   Smith data, or prime-independent quantities. GAP may cache properties of
   individual objects, but these functions do not deliberately reuse them.
   Process startup matters for tiny examples; completion dominates hard ones.

These identify mechanisms visible in the code, not a measured allocation or
CPU profile. Timeouts do not locate an individual slow candidate. The new
runner records whole-run wall time and resident memory; per-candidate rule
counts, timings, and confluence would need additional instrumentation in a
separate algorithm-change task.

## Mathematical limits

- There is no general terminating word-problem algorithm for all finitely
  presented groups. A useful finite confluent system need not be found for
  these derived quotients. More RAM and longer limits do not remove that
  obstruction.
- `MakeConfluent` can return false; the research code ignores this and still
  reduces words. Under valid rewriting rules, identity reductions justify
  eliminations, while nonidentity results without confluence are unresolved.
  Survivors may be redundant. This is why the output is an upper bound.
- `Sublist` must span `N/([F,N]N^q)`, not just be a convenient collection of
  relators. The functions do not validate this, primality, or word parents.
  Arbitrary subsets can invalidate the bound.
- A spanning set of this relation quotient is not yet a basis of H2 or
  chain-level representatives. Positive bounds do not prove nonzero homology.
- Changing a group's presentation requires preserving its identification
  and transporting the candidate words. A matching H1 is a useful sanity
  check, not a proof of isomorphism or an H2 result.
- The library hard-codes only four arithmetic presentation primes. Changing
  the coefficient prime of a fixed group is different from constructing the
  next arithmetic-family group. There is no general presentation generator
  for arbitrary primes in this checkout.
- Larger-prime claims require the hypotheses of the presentation theorem
  and of the homology interpretation. Characteristic-zero results, finite
  quotients, or calculations for a different ring do not automatically settle
  the target infinite arithmetic group's mod-q homology.

## Recommended next changes, in order

These are proposals; none is implemented by this documentation PR.

| Priority | Proposed experiment | Why it may help | Required validation |
| --- | --- | --- | --- |
| 1 | Recover paper inputs, candidate lists, GAP/KBMAG versions and original logs; audit G11 against the presentation source | Avoid spending larger budgets on the wrong group or comparing different experiments | Document source correspondence, generator maps, and known invariants; preserve original files |
| 2 | Validate primes, word parents, and candidate coverage; expose completion status and effective options; retain positive reduction witnesses | Separate certificates from unresolved tests and improve diagnosis | Known finite/abelian groups, deliberately incomplete completions, invalid inputs, and failure propagation |
| 3 | Fix `tindyint` in a separately reviewed change; benchmark `tidyint`, equation limits, generator orders, and candidate orders under fixed resource budgets | Correct the intended tuning and reduce overlap growth or improve eliminations | Same presentations and spanning inputs; compare bound soundness and completion status, not literal survivor lists alone |
| 4 | Reuse exponent matrices/Smith data, derive `c-b` from matrix rank, cache static powers/commutators, remove proven redundant abelian relations | Reduce repeated linear algebra and quotient construction | Independent Smith-normal-form comparisons, including free summands and higher prime powers |
| 5 | Try Tietze simplification and shorter certified spanning lists with explicit word maps | Fewer generators/relations can sharply reduce the derived completion input | Track isomorphisms and witnesses that the candidate images span E; check original-word results |
| 6 | Test incremental completion or certified reuse of rewriting data only for compatible quotient changes | Avoid restarting every candidate from nothing | Each removed/added relation must be tracked; rules valid only in a stronger quotient must never be reused in a weaker one |
| 7 | Run independent cases, coefficient primes, or ordering experiments in separate bounded GAP processes | Use multiple cores for independent work | Resource limits per process, isolated KBMAG temporary files, deterministic provenance, no races in the greedy elimination state |
| 8 | Cross-check small finite groups using HAP resolutions or other independent homology methods; investigate arithmetic decompositions where applicable | Independent answers can distinguish loose bounds from true dimensions; structure may avoid hard generic completion | Confirm package applicability, finiteness/subgroup hypotheses, coefficients, and maps before interpreting agreement |
| 9 | Build a theorem-backed arithmetic presentation generator for further primes, with symbolic consistency tests | Avoid manual expansion of long relation families | Verify theorem hypotheses and recover existing stored cases up to certified transformations; resolve G11 first |

Within a fixed run, the greedy decisions depend on earlier removals; naive
parallel deletion can discard mutually dependent generators. Parallelize
independent runs first. Similarly, finite-quotient experiments and bounded
nilpotent approximations may be exploratory tools, but are not automatically
certificates of vanishing or equality for the original group.

The immediate research milestone is a versioned, certified reproduction of
one arithmetic case with its intended presentation, not simply a larger
equation cap. The new test suite and bounded runner provide a baseline for
reviewing those subsequent changes without rewriting the historical record.

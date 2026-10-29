# Case-5 identification: provenance and mathematical impact

**Verified verdict:** the stored `Free5/R5` presentation defines C5. The
finite-matrix interpretation of its `SL_2Z_5` label is incorrect, and the
archived H1 row at characteristic 5 is incorrect under that interpretation.
The arithmetic input `G5=F5/k5` is a different presentation.

**Uploaded-version verdict:** Roberts **2009.04069v1**, Section 4 and
Tables 1–2 (pp. 10–11), contains the same numerical rows and explicitly says
unmarked H2 entries are exact dimensions. Thus its characteristic-5 finite
SL(2,Z5) entries are affected, rather than merely potentially loose bounds.
Anton **0804.3553v1** proves an arithmetic result using a different, explicitly
printed presentation; Roberts **0901.2610v3** likewise uses separate arithmetic
examples. This finite identification error is absent from those cited proof
paths. Their expensive reductions have not been independently rerun here.
See [the versioned paper audit](PAPER-AUDIT.md) for page-level evidence and
separate issues requiring reproduction checks. No verdict about unexamined
versions or a complete validation of every theorem is implied.

No existing presentation, original algorithm, notebook, HTML, result image,
or archived baseline measurement is changed by this investigation.

## 1. Trace through the repository

The decisive current source is [Library-of-groups.g](../Library-of-groups.g),
lines 315–318:

```gap
#SL_2(Z_5)
Free5:=FreeGroup(2);;a5:=Free5.1;;b5:=Free5.2;;
R5:=[(a5*b5)^2*a5^-3, a5^3*b5^-1];
SL_2Z_5:=Free5/R5;
```

| Event | Evidence | What it establishes |
| --- | --- | --- |
| 2020-09-09: supplied R20 v1 header date | [Section 4 and Tables 1–2, pp.10–11](https://arxiv.org/pdf/2009.04069v1#page=11) | Matching finite case-5 numeric rows and an explicit exactness convention already appear in this supplied version; the exact two-word presentation is not printed there |
| 2020-11-29: first README | [`f828374`](https://github.com/jd-roberts/generators-group-homology/commit/f828374140c6239e1a4516dfdde4214985b9a2c3) | A generic attribution of the SL presentation to Anton; no per-example source or equation number |
| 2020-11-29: first library import | [`b01c24f`](https://github.com/jd-roberts/generators-group-homology/blob/b01c24f8cda53b1935f64434f7f16ac35641da56/Library%20of%20groups#L315-L318) | Both the label and exactly the relators above already appear in `Library of groups` |
| 2021-03-09: library rename | [`5507525`](https://github.com/jd-roberts/generators-group-homology/commit/5507525f21fd2232e251abee5fe767282f47ab27) | Rename only; zero content changes |
| 2021-03-09: README expansion | [`30b14bf`](https://github.com/jd-roberts/generators-group-homology/commit/30b14bf2f2a22620bb005abb75ad797297362494) | Adds the two Roberts paper links; does not identify which paper supplies this finite example |
| 2021-03-11: label updates | [`3ec9d4a`](https://github.com/jd-roberts/generators-group-homology/commit/3ec9d4ae34d49be098822efa3429a823ec6fe2a0) | Edits other ring labels and a printed banner; does not change `R5` |
| 2021-04-07: table-image upload | [`1e47cd9`](https://github.com/jd-roberts/generators-group-homology/commit/1e47cd99bb8a8883c2d68e77d8c98552eb21f0a0) | Adds `Capture.JPG` and `Capture2.JPG`; provides no generating script, paper-page attribution, or experiment log |
| Original research tip `f684175` | [fixed source](https://github.com/jd-roberts/generators-group-homology/blob/f684175285d780752f56d1baf6d0bf5f7d87ef33/Library-of-groups.g#L315-L318) | Same finite case-5 presentation remains in the source audited by this PR |

The history examined includes all locally available refs. `git log --follow`
and the initial blob show the presentation entered the available history in
this form. There is no tracked change from a different final exponent to
`b5^-1`. Its origin **before the first import** is not established. A plausible
typographical repair is not evidence of the author's intended input and is
not applied here.

Current documentation provides limited additional provenance:

- [README.md](../README.md), lines 4–5, and the first markdown cell of
  [the notebook](../finitely-presented-groups.ipynb) link the same three papers
  without assigning this example to a specific statement or presentation.
- The notebook's only executable cell exports HTML. It is not a homology
  transcript and contains no executable `R5` computation.
- [undergrad-research/projects.md](../undergrad-research/projects.md), lines
  5–10, describes vector spaces and upper bounds and embeds
  [Capture2.JPG](../undergrad-research/Capture2.JPG). The image has no recoverable
  driver or attribution to a particular paper page in the checkout. The uploaded
  Roberts 2020 v1 now identifies matching tables on p. 11.
- [Algorithms.g](../Algorithms.g), lines 45–54 and 138–151, accepts a free
  group and relator list as arguments. It never selects `R5` or `SL_2Z_5`
  internally. No original checked-in homology driver links this input to a
  particular published calculation.

## 2. What the presentation proves

Write `a,b` for the images of `a5,b5`. The relators give

```
(ab)^2 = a^3,       b = a^3.
```

Substitution gives `a^8=a^3`, so `a^5=1`, and the whole group is generated
by `a`. Conversely, in C5 let `a` be a generator and `b=a^3`; both relators
hold. The maps in both directions show that the group is **exactly C5**, not
just a quotient of C5 or a group with the same abelianization.

Consequently, with trivial coefficients,

```
H1(C5; Z) = Z/5,       H2(C5; Z) = 0,
dim H1(C5; F_q) = dim H2(C5; F_q) = 1 if q=5, and 0 otherwise.
```

The last statement follows directly from the standard two-periodic cyclic
resolution: after tensoring with F_q, its differentials alternate between
zero and multiplication by 5. The universal coefficient theorem gives the
same result from the integral homology. It is not inferred from the name
assigned to the group by GAP.

For comparison, the genuine finite matrix group `SL(2,F5)` has order
`5*(5^2-1)=120`: there are 24 possible nonzero first columns and five choices
of second column giving determinant one. Its abelianization is trivial. An
elementary proof uses `h=diag(2,2^-1)` and upper unipotents `u(t)`: the
commutator `h*u(t)*h^-1*u(t)^-1` is `u(3t)`. Thus all upper unipotents, and
their lower-unipotent conjugates, are commutators. They generate SL(2,F5).
This proves perfectness independently of the repository's algorithms.

A separate bounded GAP-core check gives:

```
Size(SL(2,5))                       = 120
AbelianInvariants(SL(2,5))          = []
AbelianInvariantsMultiplier(SL(2,5))= []
```

The multiplier operation computes the abelian invariants of integral H2.
Its definition and Schur-cover method are documented in GAP 4.14's installed
`lib/schur.gd`, lines 93–134, and `lib/schur.gi`, lines 284–285; see also the
[GAP source](https://github.com/gap-system/gap/blob/v4.14.0/lib/schur.gd).
The zero integral H1 and H2 imply zero H1 and H2 over **every prime field**
by the universal coefficient theorem. Perfectness alone would not establish
the H2 claim; the independent multiplier calculation supplies that additional
information. This is a computational check, not a newly constructed formal
certificate for the Schur-cover algorithm.

[tests/identification-impact.g](../tests/identification-impact.g) checks the
stored group and the genuine matrix group without KBMAG. It completed under
a five-second limit in 0.718523 recorded wall seconds on GAP 4.14.0. Its
[raw evidence](evidence/identification-impact.txt) and
[resource/source record](evidence/identification-impact.json) are retained.

## 3. Which repository conclusions are affected?

The case-5 rows of `Capture2.JPG`, at coefficient primes 2,3,5,7, display
`[0,0,1,0]` for both H1 and H2. These match C5, as the checked-in presentation
predicts. Numerical agreement does **not** recover a missing execution log:
it establishes consistency, not proof of which historic commands were run.

| Claim or artifact | Consequence of the identification issue |
| --- | --- |
| H1 row interpreted as SL(2,F5) | The characteristic-5 value 1 is incorrect; the genuine group has value 0. The other displayed zeros agree independently. |
| H2 row interpreted as an exact dimension or nonvanishing statement for SL(2,F5) | The characteristic-5 value 1 is incorrect; the genuine group has value 0. |
| H2 value 1 interpreted only as an upper bound for SL(2,F5) | `dim <= 1` happens to be true, but the C5 computation does not establish it for a different group. It is not sharp. The project text describes bounds, but the uploaded 2020 v1 explicitly treats the unmarked entry as exact; that exact claim is incorrect under the finite-matrix interpretation. |
| The archived row interpreted as results for the stored `Free5/R5` | Values are correct for C5; its interpretation must be stated explicitly. |
| The new baseline under legacy runner key `SL2F5` | Remains a valid C5 baseline, explicitly labelled as such. It is not a positive control for the genuine SL(2,F5). |
| Other rows or generic homology algorithms | No numerical error in those follows logically from this identification issue. Their own inputs and mathematical assumptions still need validation. |
| Arithmetic case `G5=F5/k5` and the other Anton-labelled cases | No direct code dependency on `Free5/R5` is present. The uploaded arithmetic proofs likewise use separate inputs; the finite table defect does not enter their cited proof paths. Full experiment transcripts remain unavailable. |

Thus this is more than harmless renaming **if the row is asserted for the
finite matrix group**. It is also insufficient evidence to declare an
arithmetic theorem false. A generic algorithm can be correct while a user
supplies or labels the wrong presentation.

## 4. Finite matrices and the arithmetic target are different objects

| Object | Meaning | Repository evidence |
| --- | --- | --- |
| C5 | Cyclic group of order 5 | `Free5/R5`, library lines 315–318 |
| SL(2,F5) | Determinant-one matrices over `Z/5Z`, order 120 | GAP's independent `SL(2,5)` construction; not the stored finite case-5 presentation |
| SL(2,Z) | Integral determinant-one matrices, infinite | Separate `S/rels` input, library lines 295–298 |
| Intended arithmetic family | Groups of the form `SL(2,Z[zeta_p,1/p])`, with cyclotomic elements and p inverted | Arithmetic blocks `F3/k3`, `F5/k5`, `F7/k7`, `F11/k11`, the Anton link, and the motivating expression in `Capture.JPG`; Anton v1, Notation 3.4, Theorem 6.2 and Section 7: the presented group is SE2, with an additional identification step to SL2 |

For example, [the arithmetic case-5 block](../Library-of-groups.g), lines
40–82, has eleven free generators and 39 defining relators; the finite
case-5 block has two generators and two relators. The objects and globals
`F5`, `k5`, `G5` are distinct from `Free5`, `R5`, `SL_2Z_5`, even where GAP
prints similar default generator names. Later defining the latter does not
replace `G5`.

For odd p, a primitive 2p-th root `eta` with `eta^p=-1` can be chosen as
`eta=-zeta_p`, so `Z[eta]=Z[zeta_p]`. This explains the relation between the
cyclotomic notation and the radical in `Capture.JPG`; an arbitrary root of
`X^p+1` must not be substituted without its primitivity conditions.

These characteristic-zero arithmetic groups are infinite: the upper
unipotent matrices with integral entries already give infinitely many
elements. Inverting p also matters. There is no unital ring map from
`Z[zeta_p,1/p]` to F_p, since the unit p would map to zero. Thus the finite
SL(2,F5) example is not an automatic reduction modulo 5 of the arithmetic
p=5 ring. Any comparison via a residue field, quotient, subgroup or homology
map needs its own hypotheses; homology cannot be transferred simply because
both labels contain 5.

The coefficient prime q is another parameter. The generic code accepts q
independently of the presentation-family index p; the motivating pictured
problem uses matching coefficients F_p. Testing q=11 on a fixed finite group
does not construct the arithmetic family member indexed by p=11.

## 5. Uploaded-paper audit completed within stated limits

The three supplied versions have now been read. The
[paper audit](PAPER-AUDIT.md) records source hashes and exact locations:

- Roberts 2020 v1, Section 4 and Tables 1–2, pp. 10–11: the finite row and
  its equality interpretation are present. The source of the exact two-word
  `Free5/R5` presentation before the Git import remains unestablished; matching
  table values do not recover an original execution transcript.
- Anton 2008 v1, Theorem 1.1 and Corollary 7.5: arithmetic prime-5 vanishing,
  using the eleven-generator presentation and Lemma 7.4. Its 39 relators
  match the stored arithmetic `k5` literally. No finite two-generator C5
  input is used in this proof path.
- Roberts 2009 v3, Examples 4.1–4.4: the finite control is the symmetric
  group on five letters, followed by arithmetic cases at primes 3,5,7;
  there is no finite SL(2,F5) example or the 2020 table in this version.
- Roberts 2020 v1, Section 3.1: the arithmetic prime-7 generator calculation
  is separate from Section 4's finite table, but the six displayed abelian
  images on p. 10 have a distinct printed-data inconsistency. The
  [reexamination](PRIME7-PROOF-REEXAMINATION.md) verifies rank six for the
  literal auxiliary words and distinguishes this from the still-unresolved
  identity reductions and explicit homology representatives. The intended
  spanning argument does not require independent homology classes.

The subsequent [presentation certificates](PRIME7-PRESENTATION-CERTIFICATES.md)
now verify the maps in both directions, distinguish the b1 and b0 source-word
conventions by exact normal-closure certificates, and provide separate valid
kernel words under the b0 interpretation. The expensive spanning premise
remains unverified; the earlier b1-interpreted corrected list is not valid.

The source review identifies a concrete error in the uploaded 2020 finite
example table and traces separate arithmetic proof inputs. It does not
independently replay multi-day rewriting runs or establish completeness of
2020's printed generator list. Those are research-validation tasks, not
reasons to edit or replace the archived presentations silently.

[The prioritized optimization plan](OPTIMIZATION-PLAN.md) now includes Anton's
fixed-quotient batch certificate and source-backed parameter settings. No
performance optimization or original mathematical source is changed here.

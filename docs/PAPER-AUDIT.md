# Uploaded-paper audit: affected claims and arithmetic dependencies

This review reads the exact three PDFs supplied in the chat. It completes
the previously blocked source comparison; it does **not** independently rerun
the multi-hour/day arithmetic reductions, repair a presentation, or alter an
original research result. Statements about errors below concern the supplied
versions, not unexamined later arXiv or journal versions.

## Sources and reproducibility

| Short name | Supplied version and header date | Pages | Main locations checked |
| --- | --- | --- | --- |
| A08 | Anton, [0804.3553v1](https://arxiv.org/pdf/0804.3553v1), 22 Apr 2008 | 23 | Notation 3.4, Theorem 6.2, Section 7, Lemma 7.4, Corollary 7.5 |
| R09 | Roberts, [0901.2610v3](https://arxiv.org/pdf/0901.2610v3), 30 Sep 2009 | 12 | Algorithms 5–7; Examples 4.1–4.4; Section 5; Appendix A |
| R20 | Roberts, [2009.04069v1](https://arxiv.org/pdf/2009.04069v1), 9 Sep 2020 | 13 | Sections 2, 3.1, 4; Proposition 3.2; Tables 1–2 |

Full PDF SHA-256 hashes, sizes and page counts are recorded in
[paper-sources.json](evidence/paper-sources.json). Page numbers below are
printed/PDF page numbers, which coincide in these copies. Text was extracted
with `pdftotext -layout`; the critical R20 p.10–11 and A08 p.13 displays were
also rendered and visually checked. Full copyrighted PDFs are not added to
the repository. Instructions or executable material in them were treated as
source content, not authority to run arbitrary commands.

## 1. The finite case-5 issue does affect R20's exact table claims

R20 Section 4, pp.10–11, says the tables give results of the earlier
algorithms. It explicitly distinguishes marked upper bounds from unmarked
entries: for the latter, “the exact dimension was found.” On p.11, both
Tables 1 and 2 give the row labelled SL2(Z5) as

```
coefficient prime:       2  3  5  7
H1 row:                 0  0  1  0
H2 row:                 0  0  1  0
```

The characteristic-5 H2 entry is **unmarked**. Thus the supplied paper does
make an exact-dimension claim here; the earlier possibility that it might
mean only a loose upper bound is resolved for R20 v1. These rows and the
other table entries match the repository's `Capture2.JPG`. This establishes
matching table content, not how the image was generated or which input files
were used before the repository import.

The erroneous numeric row is therefore visible in the supplied R20 version
dated September 2020, before the first available library import in November
2020. The exact two-word presentation is first established by that Git import;
the supplied paper does not establish where those words originated earlier.

Under the finite-field meaning `Z5=Z/5Z`, both characteristic-5 entries are
incorrect: the genuine SL(2,F5) has H1=H2=0 with F5 coefficients. The
[identification report](PRESENTATION-PROVENANCE.md) gives the C5 presentation
proof, an elementary perfectness argument for the matrix group, and an
independent GAP-core Schur-multiplier check. A mere bound `dim H2 <= 1`
would be true but loose; R20's prose does not present this entry that way.

The stored `Free5/R5` instead defines C5, whose two rows really are
`[0,0,1,0]`. This is a numerical and mathematical explanation of the issue,
not a recovered historical execution transcript. R20 says group code is
given below, but the supplied 13-page copy does not supply the finite
case-5 GAP definition. We therefore cannot trace the exact `b5^-1` text to
an earlier source than its first Git import. No guessed replacement is made.

## 2. The arithmetic proof paths use different inputs

### A08: the prime-5 theorem has an explicit eleven-generator proof

Notation 3.4 (p.7) fixes a regular odd prime `ell=2r+1`, a primitive ell-th
root `xi`, and `R=Z[1/ell,xi]`. These are characteristic-zero arithmetic
rings, not residue fields. Theorem 1.1 (p.2) asserts

```
H2(SL2(Z[1/5,xi5]); F5) = 0.
```

Theorem 6.2 (p.13) actually presents **SE2**, defined by generators D(u),
E(x) and relations (6.1). Relations (6.2)–(6.3), p.12, introduce z, ui, a,
b and the auxiliary bt,w. Section 7 (p.17) gives the homomorphism to SL2
by explicit diagonal/elementary matrices. The closing paragraph on p.22
invokes a separate result: this map is an isomorphism for a Euclidean ring,
and the relevant ring is Euclidean at ell=5. Corollary 7.5 then gives the
SL2 vanishing statement.

Therefore Theorem 6.2 must not be cited as an unconditional identification
of every group produced from the relation template with SL2 over every
prime's ring. The SE2-to-SL2 step and its hypotheses are part of the argument.

Most decisively for the case-5 investigation, A08 pp.20–21 print an
**eleven-generator, 39-relator** input. Its 39 relators agree literally with
the repository's arithmetic `F5/k5`, after assigning the same free generators.
They are unrelated to the finite two-generator `Free5/R5` definition.

Lemma 7.4 (p.21) chooses these relator indices:

```
e = k{[5,6,15,16,17,30,31,32,33,34,37]}
```

It forms one quotient `F/[F,K]K^5<e>` and reports that all 28 complementary
relators reduce to the identity there. This proves e spans `K/[F,K]K^5`.
The next page checks that its abelian image spans an 11-dimensional space.
The middle term has dimension at most 11, the image has dimension 11, so
the kernel is zero. Perfectness (Lemma 7.2, p.18) handles the coefficient
issue. Corollary 7.5 uses the ring identification to conclude the SL2 result.

The finite two-generator case-5 example is not used in that displayed proof path. The
specific finite-table identification error therefore does not undermine
this cited arithmetic proof. This is a dependency/source conclusion; the
28 expensive positive reductions have **not** been independently replayed.

### R09: a symmetric control and separate arithmetic examples

R09 Section 4 uses these examples (pp.8–9):

| Example | Group and coefficient | Reported result |
| --- | --- | --- |
| 4.1 | Symmetric group Sigma5, coefficient F2 | dimension 2 |
| 4.2 | SL2(Z[1/3,zeta3]), coefficient F3 | dimension 0 |
| 4.3 | SL2(Z[1/5,zeta5]), coefficient F5 in context | dimension 0 |
| 4.4 | SL2(Z[1/7,zeta7]), coefficient F7 | upper bound 6 |

The finite control is **Sigma5**, not SL(2,F5). Both have order 120, but
they are different groups: Sigma5 has abelianization C2, while SL(2,F5)
is perfect. The supplied R09 version contains neither R20's finite table
nor the two-relator `Free5/R5` example.

Section 5, p.9, reports approximately 50 ms, six hours, two days, and five
days for Examples 4.1–4.4, respectively. These are author-reported historic
times, not measurements of this environment. Nonconfluence is explicitly
acknowledged for the arithmetic examples; positive identity reductions can
still support upper bounds or vanishing. A nonidentity reduction without
confluence remains inconclusive.

The prime-5 arithmetic result is thus a separate example, not a deduction
from the finite case-5 table. The reviewed sources give no dependency path
from that finite misidentification to the R09 prime-3/5 arithmetic vanishing
statements or its prime-7 upper bound. This does not validate every printed
formula or recover the original run inputs.

### R20: the arithmetic discussion is separate from Section 4's table

R20 Section 2 (pp.2–5) discusses rings `Z[zeta_p,1/p]` and references the
earlier arithmetic results. Section 3.1 (pp.7–10) treats the arithmetic
prime-7 case and references R09's bound 6. The finite table is presented
afterwards, in Section 4, as database examples. The text does not use the
finite SL2(Z5) table row to prove the arithmetic assertions.

That separation settles the narrow dependency question. It does not certify
the entire R20 generator argument: the independent printed-data problem
below prevents treating its listed generators as a validated shortcut.

## 3. Bounded checks actually performed

[tests/paper-provenance.g](../tests/paper-provenance.g) uses GAP core only,
without an arithmetic completion. It checks:

- All 39 A08 prime-5 words match `k5` exactly.
- Of the 21 A08 prime-3 words, 18 match literally. The other three differ
  by commutator convention. For `g=x^-1*y^-1*x*y`, the explicit free-word
  identity `(xy)*g*(xy)^-1=xyx^-1y^-1` checks their conjugacy. Thus they
  generate the same normal relations; no word problem is being approximated.
- The eleven e-indices and 28 n-indices in A08 Lemma 7.4 partition all 39
  words. The e exponent matrix has rank 11 modulo 5, and `G5` is perfect.
  This reproduces the cheap linear portion, **not** the missing 28 reduction
  certificates establishing that e spans the relation quotient.
- GAP's independent Sigma5 has integral H1=C2 and Schur multiplier C2,
  corroborating R09's mod-2 H2 dimension 2 by UCT. This uses GAP's group,
  not a replay of the paper's specified KBMAG input.
- The printed R20 p.10 images have formal rank 3, as explained below.
- Stored `G11` is not perfect, contradicting identification with the SE2
  of A08 Lemma 7.2. A source correction is required before using it as that
  group; no correction is guessed or applied.

The reference words are isolated in
[a comparison fixture](../tests/fixtures/anton-v1-relators.g), transcribed
from the supplied PDF. The [readable output](evidence/paper-source-checks.txt) and
[source/resource record with exact stdout](evidence/paper-source-checks.json) record a normal
completion in 1.041523 wall seconds under a five-second limit on GAP 4.14.0.
This is neither an arithmetic H2 rerun nor an implemented optimization.

## 4. Separate reproduction issues that must remain visible

### R20 prime 7: auxiliary images versus spanning homology classes

**Latest result:** the [presentation certificates](PRIME7-PRESENTATION-CERTIFICATES.md)
verify the Proposition 3.2 isomorphism, classify all twelve words, and show
that `f7=b1` gives four nonmembers of the relation subgroup. Five previously
corrected words are also nonmembers. All twelve words have positive
membership certificates under `f7=b0=z^-3*b1*z^3`, yielding separate valid
corrected classes; their spanning property remains unverified. The source
coordinate distinction is essential when reading the earlier analysis below.

The author's clarification and a more detailed
[proof reexamination](PRIME7-PROOF-REEXAMINATION.md) supersede the earlier
assessment of this point. R09 proves only an upper bound six; R20 seeks
six spanning classes, without claiming their independence or nontriviality.
The six-dimensional space named on R20 p.10 is the auxiliary B, not H2.

The p.10 images `f1^3, f7^-1, f2^-1, f1*f2, f1, f1^-1` belong to the
**last six auxiliary elements** of the twelve-word list, not the proposed
homology generators. Their displayed rank is at most three. That alone
does not disprove spanning: dependencies among their lifts might vanish
in A or already lie in the span of the proposed kernel elements.

Crucially, a new direct exponent check of the literal last-six words on
pp.9–10 gives **rank six**, with determinant 6 modulo 7. Thus the actual
auxiliary words support the needed basis property; the rank-three
reduction display does not accurately represent their abelian images.
This resolves the auxiliary-rank question left open by the earlier audit.

A separate necessary cycle check remains: the first literal word
`f1*f5*f1*f5^-1` has exponent image `2*f1`, not zero. The final printed
list likewise starts `z*a*z*a^-1`, nonzero in the free mod-7 abelianization.
The asserted identity reductions and the explicit representatives therefore
need clarification or an explicit missing change of generators.

If the twelve words span A as reported, their independent last-six images
allow one to subtract auxiliary combinations from the first six words,
producing six spanning kernel elements. This requires no independence of
those kernel elements, but does not identify them with the unadjusted final
printed list. See the reexamination for the exact argument, source passages
and bounded checks. No arithmetic spanning certificate has been rerun;
neither the 2009 bound nor the intended spanning method is refuted here.

The subsequent [explicit correction calculation](PRIME7-CORRECTED-REPRESENTATIVES.md)
constructs six words by subtracting auxiliary combinations, verifies all
their mod-7 exponent sums directly, and proves conditional spanning. It
also verifies that all six final printed words literally match the first
six source words under the named-generator convention; that renaming alone
does not explain the discrepancy. The twelve-word certificate remains unrun.

### Reduced arithmetic inputs differ across source descriptions

R09 p.10 reports a reduction from 14 generators/64 relators to 6/34 for
prime 7. R20 Proposition 3.2 (pp.8–9) supplies forward generator expressions
and a 6-generator/32-relator presentation. Neither reduced presentation is
an input fixture in the original repository. Their equivalence, mappings,
ordering and chosen subsets must be established before comparing runtimes.

R09's iteration pairs (p.9–10) are `e<=16,d<=10`, `e<=13,d<=7`, and
`e<=12,d<=6`. Their offset is six, consistent with a six-generator perfect
presentation. The current raw 14-generator perfect presentation has offset
14 under the stated formula. The text does not supply a full execution
transcript resolving those inputs, so silently treating the reported e-values
as raw-`F7/k7` counts would be incorrect.

### Effective options have a traceable source

A08 pp.20–21 use `maxeqns=500000`, **`tidyint=1000`**, and `confnum=100`.
R09 Appendix A p.11 instead prints **`tindyint=100`**, the ignored spelling
also present in the repository. Thus this defect is already visible in the
uploaded algorithm appendix. A source-backed parameter comparison should
include A08's actual settings; no field is changed in this PR. The sources
cite GAP 4.4.10, but do not provide a reproducible pinned KBMAG build or
complete machine/run image.

## 5. Conclusions for continued research

The finite case-5 misidentification affects exact entries in the supplied
R20 table. It is not an input to the reviewed A08/R09 arithmetic proofs.
Those proofs provide concrete distinct relators and, for prime 5, a batch
spanning certificate to reproduce. Their expensive positive reductions
remain computationally unverified in this environment.

Before optimization, quarantine the nonperfect stored G11 identification
and clarify R20 p.10's explicit representatives as detailed in the
[prime-7 reexamination](PRIME7-PROOF-REEXAMINATION.md). Preserve the old tables and
candidate words as evidence, and record clarifications separately. The
[updated optimization plan](OPTIMIZATION-PLAN.md) prioritizes reproducing a
fixed-quotient certificate on small cases before any authorized arithmetic
pilot, with explicit group maps, bounds, proof status and resource limits.

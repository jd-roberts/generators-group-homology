# Prime-7 proof reexamination: spanning and auxiliary images

This note clarifies the earlier [paper audit](PAPER-AUDIT.md) following the
author's explanation of the intended result. It examines the uploaded
[Roberts 2020 v1](https://arxiv.org/pdf/2009.04069v1), Section 3, pp.6–10,
and [Roberts 2009 v3](https://arxiv.org/pdf/0901.2610v3), Example 4.4 and
Section 5, pp.9–10. PDF hashes remain in
[the source manifest](evidence/paper-sources.json). It changes no published
claim, original presentation, algorithm, or archived result.

The subsequent [explicit correction calculation](PRIME7-CORRECTED-REPRESENTATIVES.md)
now supplies the coefficient matrix, six specified corrected words, their
direct exponent verification, and the conditional spanning proof. It does
not independently establish the twelve-word spanning certificate.

## What is and is not claimed

The 2009 result is `dim H2(G;F7) <= 6`, not equality. The 2020 goal is six
explicit **spanning classes**. Neither their linear independence nor their
nontriviality is required. The sentence on R20 p.10, “the possibility still
exists that any, or all, of these may be trivial in H2,” makes this explicit.
My earlier criticism should have identified the auxiliary elements and
separated their basis assertion from the homology spanning assertion.

The six-dimensional space mentioned immediately after the reduction display
on p.10 is **B**, not H2. A basis of B can be used to extract a spanning
set of the kernel without obtaining a basis or dimension of that kernel.

## Identify the elements and the proof's structure

Use R20 Section 3, p.6, with the prime set to 7:

```
A = N/(N^7 [F,N]),   B = F/(N^7 [F,F]),   i*: A -> B.
```

In the perfect-group situation under discussion, B is six-dimensional over
F7, i* is onto, and `ker(i*) = H2(G;F7)`. Equivalently, this is the mod-7
five-term exact sequence, with the free group having zero H2 and the target
group having zero H1. Perfectness also makes the displayed B equal to
`F/(F^7 [F,F])`: the relator exponent lattice is the whole free abelian
lattice. These are assertions about the auxiliary quotient, not the
dimension of H2.

Number the twelve words printed across pp.9–10 as r1,...,r12, in their
printed order. Their exact literal transcription is isolated in
[this source fixture](../tests/fixtures/roberts-v1-prime7-words.g).
The paper reports that they span A via FindBasis; this expensive assertion
has **not** been independently rerun.

Let ci = ri for i=1,...,6 and dj = r(6+j) for j=1,...,6. The p.10 reduction
display asserts that the ci have zero image, followed by these images:

| Auxiliary element | Displayed image in B |
| --- | --- |
| d1 = r7 | f1^3 |
| d2 = r8 | f7^-1 |
| d3 = r9 | f2^-1 |
| d4 = r10 | f1*f2 |
| d5 = r11 | f1 |
| d6 = r12 | f1^-1 |

These are the six elements implicated in my rank observation. They are
**auxiliary images of the last six relation-module generators**, not the
six proposed homology generators. The proposed homology classes are the
first six, identified by the preceding six identity entries and the later
six-word list in z,u1,u2,u3,a,b1 notation.

The intended linear argument is sound: if the twelve span A, the ci lie
in ker(i*), and the images of the dj are independent and span im(i*),
then every kernel element is a linear combination of the ci. Indeed,
applying i* to a combination of the ci and dj forces every dj coefficient
to vanish. Nothing forces the remaining six ci to be independent in A.
Relations among the ci can make any or all of them trivial.

## What the rank-three observation does establish

In additive notation the *displayed* six images are

```
3x, -z, -y, x+y, x, -x,  where x=[f1], y=[f2], z=[f7].
```

They have rank at most three in any abelian target. Their formal coordinate
rank over F7 is exactly three. The dependencies include

```
i*(d1 - 3d5) = 0,
i*(d4 - d5 + d3) = 0,
i*(d6 + d5) = 0.
```

These formulas do **not** prove three new independent homology classes.
The combinations may vanish in A or already lie in the span of the ci.
Consequently, auxiliary dependence alone does **not** disprove that the
ci span H2. It prevents the particular basis argument from proving that
conclusion unless those extra kernel combinations are accounted for.
The earlier upper bound six does not by itself supply that missing step.

Moreover, if all twelve images were exactly as displayed, their total rank
would be at most three, inconsistent with their spanning A and i* being
onto the asserted six-dimensional B. This is an inconsistency among the
printed auxiliary data, not a claim that H2 has dimension six.

## New direct check: the literal auxiliary words actually have rank six

There is a stronger and more useful check than reading the reduction list:
compute exponent sums of the twelve literal words before any rewriting.
Use the six free coordinates `(f1,f2,f3,f4,f5,f7)`; no f6 occurs in the
printed list. Reducing the last six exponent vectors modulo seven gives

```
r7:   1 2 0 0 5 6
r8:   0 0 0 0 0 6
r9:   5 0 0 0 5 0
r10:  0 0 0 4 4 0
r11:  4 0 3 4 4 0
r12:  5 3 3 3 4 0
```

This matrix has determinant **6 modulo 7** and rank **6**. Thus the
literal auxiliary words DO support the required independence in B under
the stated six-free-generator interpretation. The displayed rank-three
list is incompatible with these actual exponent images; my earlier
report did not perform this comparison and left the auxiliary-basis issue
unnecessarily unresolved. A change of basis in B cannot change rank six
to rank three.

There is a separate discrepancy in the claimed zero images of the first
six words. Their exponent rows modulo seven are

```
r1:  2 0 0 0 0 0
r2:  0 0 0 0 0 0
r3:  0 2 0 0 0 0
r4:  0 0 0 0 6 3
r5:  5 0 2 0 5 6
r6:  1 0 0 2 5 6
```

In particular, r1 is `f1*f5*f1*f5^-1`, with image `2[f1]`, not zero.
The final list on p.10 likewise starts with `z*a*z*a^-1`, whose z
exponent is two. By Proposition 3.2, p.8, z is a free generator of F.
There is a natural map

```
F/([F,F]N^7) -> F/([F,F]F^7) = (F7)^6.
```

Every seventh power has exponent sums divisible by seven, so this map
exists regardless of the perfectness assumption. The first printed word
has nonzero image in its target and therefore cannot be in ker(i*) as
written. This is a necessary cycle check, not an independence test.
It does not rule out an intended corrected representative or a missing
change of relation-module generators. Such a change needs to be specified;
it cannot be inferred from the claimed zero reduction.

## What survives, and exactly what needs clarification

Given the paper's assertion that the twelve words span A, the verified
rank-six auxiliary matrix allows the ordinary construction to proceed:
subtract from each ci the unique linear combination of dj with the same
abelian image. The resulting six elements are in ker(i*) and span it.
This argument allows relations among the six resulting kernel elements;
it proves neither independence nor nontriviality. It supports the intended
method and the existence of a six-element spanning list, conditional on
the reported FindBasis spanning certificate.

It does **not** identify these corrected elements with the six literal
words printed as the final answer. The exact remaining issue is the
consistency of the displayed reductions and the explicit representatives,
or a missing change of generators that explains them. The rank discrepancy
alone does not invalidate the intended spanning method, and there is no
challenge here to the 2009 upper bound or an alleged 2020 claim of exact
dimension six. No such exact-dimension claim is the point of this argument.

[tests/prime7-proof-check.g](../tests/prime7-proof-check.g) checks the source
exponent matrices, auxiliary dependencies and linear subtraction identity
in **0.834453 seconds** under a five-second limit on GAP 4.14.0; see
[exact output and hashes](evidence/prime7-proof-check.json). It loads no
KBMAG, performs no arithmetic completion, does not verify that the twelve
span A, and supplies no replacement published homology representatives.

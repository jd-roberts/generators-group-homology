# Explicit prime-7 kernel representatives from the twelve printed words

**Membership update:** the subsequent
[presentation certificates](PRIME7-PRESENTATION-CERTIFICATES.md) prove that
five of the six words below are outside the reduced normal relation
subgroup under this note's `f7=b1` convention. They do not define homology
classes under that convention. Preserve this calculation as a verified
free-word calculation, not as a valid spanning list. The follow-up gives
separate, positively certified variants using `f7=b0=z^-3*b1*z^3`;
their spanning property remains conditional.

This calculation uses the twelve literal words across pp.9–10 of the
uploaded [Roberts 2020 v1](https://arxiv.org/pdf/2009.04069v1#page=9),
without changing the source words, presentations, papers or original
algorithms. It continues the [proof reexamination](PRIME7-PROOF-REEXAMINATION.md).
No Knuth–Bendix computation is performed.

**Unconditional:** the free words below, their matrices, the correction
identity, and their zero exponent sums modulo seven are directly verified.
**Conditional:** identifying them as six spanning classes for the intended
arithmetic group's H2 uses the paper's unverified certificate that the twelve
literal words belong to and span its relation module, together with the
intended presentation identification. Exponent sums alone do not establish
normal-closure membership or that a list spans a relation module.

## Coordinates and matrices

Set `(f1,f2,f3,f4,f5,f7) = (z,u1,u2,u3,a,b1)` and number the twelve words
in their printed order as r1,...,r12. Set ci=ri and dj=r(6+j) for i,j=1,...,6.
The independent transcription of the paper's final named list equals
`[c1,...,c6]` literally under this convention. This fixes the convention
without purporting to recover historical GAP object numbering. In the
repository's original **14-generator** free group, b1 is **F7.8**, whereas
F7.7 is b0; the source label f7 must not be interpreted as that original index.

Use row vectors throughout, in coordinate order `(z,u1,u2,u3,a,b1)`.
The auxiliary exponent matrix D over F7 is

```
1 2 0 0 5 6
0 0 0 0 0 6
5 0 0 0 5 0
0 0 0 4 4 0
4 0 3 4 4 0
5 3 3 3 4 0
```

Its determinant is 6 in F7. Its inverse is

```
5 2 5 5 1 6
0 0 6 3 2 5
5 2 5 0 6 6
5 2 2 0 1 6
2 5 5 2 6 1
0 6 0 0 0 0
```

The first-six image matrix P and the unique coefficient matrix C=P D^-1 are

```
P:                    C:
2 0 0 0 0 0           3 4 3 3 2 5
0 0 0 0 0 0           0 0 0 0 0 0
0 2 0 0 0 0           0 0 5 6 4 3
0 0 0 0 6 3           5 6 2 5 1 6
5 0 2 0 5 6           3 5 4 0 5 5
1 0 0 2 5 6           4 4 6 1 5 2
```

Thus `image(ci) = sum_j C[i,j] image(dj)`; the checked identity is **C D=P**.
Choose the following integer lifts S of C, with entries in [-3,3]:

```
 3 -3  3  3  2 -2
 0  0  0  0  0  0
 0  0 -2 -1 -3  3
-2 -1  2 -2  1 -1
 3 -2 -3  0 -2 -2
-3 -3 -1  1 -2  2
```

## Explicit corrected words

Define `hi = ci d1^(-S[i,1]) ... d6^(-S[i,6])`, with factors in exactly
this order. In full, using the explicitly defined source words below:

```
h1 = c1*d1^-3*d2^3*d3^-3*d4^-3*d5^-2*d6^2
h2 = c2
h3 = c3*d3^2*d4*d5^3*d6^-3
h4 = c4*d1^2*d2*d3^-2*d4^2*d5^-1*d6
h5 = c5*d1^-3*d2^2*d3^3*d5^2*d6^2
h6 = c6*d1^3*d2^3*d3*d4^-1*d5^2*d6^-2
```

The ci,dj definitions at the end of this document make these explicit words
in the named free generators, with only multiplication, inverses and integer
powers. The [expanded GAP artifact](evidence/prime7-corrected-words.g) also
supplies all six without ci/dj abbreviations or parenthesized product powers.
Its function accepts the original 14-generator free group in repository
order and uses only positions 1,2,3,4,5,8. The lift is literal inclusion of
these six generators; the check does not independently certify a Tietze
isomorphism or its induced relation-module map.

Changing S by multiples of seven does not change the class in A, since
seventh powers of elements of N vanish there. Changing the order of the dj
factors also does not change that class: `[N,N]` lies in `[F,N]`. These
observations concern classes, not equality of the resulting free words.

## Direct exponent verification

Actual **integer** exponent sums, computed from the constructed words, are

| Word | z | u1 | u2 | u3 | a | b1 | Freely reduced length |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| h1 | -35 | 0 | 0 | 21 | 21 | -42 | 465 |
| h2 | 0 | 0 | 0 | 0 | 0 | 0 | 4 |
| h3 | 21 | -7 | 0 | -21 | -7 | 14 | 374 |
| h4 | -21 | 7 | 0 | 0 | -7 | -21 | 254 |
| h5 | 49 | 0 | 14 | 0 | -14 | 7 | 374 |
| h6 | 14 | 0 | 0 | -7 | -7 | -21 | 379 |

Every entry is divisible by seven. The other eight exponent coordinates
in the original 14-generator free group are identically zero. Both the
GAP word calculation and an independent Python token count of the expanded
words check this. Nonzero multiples of seven are intentional: these are
mod-7 representatives, not asserted integral Hopf cycles in `[F,F]`.

## Conditional spanning proof

Let F be the six-generator free group, N the intended normal relation
subgroup, and `A=N/(N^7[F,N])`. The standard mod-7 five-term sequence gives

```
0 -> H2(F/N;F7) -> A -> V -> H1(F/N;F7) -> 0,
V = F/(F^7[F,F]) = (F7)^6.
```

Here H2(F;F7)=0 because F is free. For the perfect target group, V also
agrees with the paper's `B=F/(N^7[F,F])`; working with V states the
mod-7 exponent calculation without needing an additional computation of B.

**Assume the reported source certificate:** the twelve ri are elements
of N whose classes span A, for the presentation of the intended group.
Then each hi is in N, and `P-CD=0` shows its class is in the kernel of
`A -> V`, hence in H2. The replacement of ci by hi is invertible on
generating lists: in A,

```
[ci] = [hi] + sum_j C[i,j] [dj].
```

Consequently `[h1],...,[h6],[d1],...,[d6]` still span A. If x is in the
kernel, express it as `sum_i alpha_i[hi] + sum_j beta_j[dj]`. Applying
the exponent map yields `beta D=0`. Invertibility of D forces beta=0,
so x is a linear combination of the hi. This proves the requested
**conditional spanning**, without any independence assumption on the hi.
All six may be zero. There is no lower bound, exact dimension-six claim,
new nonvanishing result, or replay of the source certificate here.

## Comparison with the six printed words

The final list on R20 p.10 is exactly c1,...,c6 below, not hi. Only c2 has
zero exponent vector mod seven and only h2 equals its corresponding
printed word in the free group. The other five printed words have nonzero
image in V; assuming their membership in N, this also distinguishes them
from the hi in A. Equality in the quotient group F/N would be irrelevant:
all words in N are already trivial there.

Several straightforward explanations can be tested or ruled out:

- **Renaming:** the evident f-label-to-name substitution reproduces all six
  printed words exactly; it does not introduce the missing correction.
- **Free-generator substitution:** a valid free-basis change induces an
  invertible matrix on V. It cannot turn a nonzero exponent vector into
  zero or the displayed rank-three auxiliary list into rank six. This
  includes permutations, generator inversions, and conjugating generators.
  Replacing b0 by its conjugate expression in b1 from Proposition 3.2
  likewise cannot fix the first word's nonzero z image.
- **Omitted inverse signs:** changing one of the two z occurrences in c1
  to z^-1 would fix that word's exponent test; a similar change works for
  c3's repeated u1. This is only an illustration, not a recovered typo or
  a spanning proof. It cannot explain all six: c4 contains three b1 letters,
  and assigning each an exponent +1 or -1 always gives b1-exponent
  +/-1 or +/-3, never zero modulo seven. Corrections beyond such sign
  changes are necessary. Moreover, c1,...,c6 occur consistently in both
  the twelve-word display and the final named list.
- **Change of relation-module generators:** subtracting auxiliary
  combinations, as above, does explain algebraically how to obtain a
  spanning kernel list. It is a change of the generating list in A, not
  a mere renaming of the generators of F. There is no source evidence
  that this specific calculation was the historical missing step.

Thus no tested straightforward transcription or free-generator substitution
explains the entire discrepancy. Arbitrary transcription errors, different
unrecorded input or a missing relation-module basis change cannot be ruled
out. The expanded representatives here are a specified correction
construction, not a reconstruction of what was originally computed.

## Verification and reproduction

From the repository root, with GAP configured:

```sh
python3 scripts/verify-prime7-corrections.py --gap /path/to/gap
```

The runner enforces a five-second timeout, rejects GAP errors even if GAP
exits with status zero, checks all exported words, and independently counts
their integer exponents. To record evidence, add
`--output /path/to/evidence.json`. The committed
[evidence](evidence/prime7-correction.json) records **0.757234 seconds**,
GAP 4.14.0, the exact output, matrices, words, and input hashes.
Neither this runner nor its GAP script loads KBMAG or constructs a
rewriting system. No inference about a failed or incomplete completion is
made; no such completion is attempted.

## Literal named source-word definitions

These are the twelve source words under the explicit naming convention
above, not shortened using the group's defining relators. Free reduction
alone is used in constructing the expanded hi artifact.

```
c1 = z*a*z*a^-1
c2 = u1*u2*u1^-1*u2^-1
c3 = u1*a*u1*a^-1
c4 = b1*a^-1*b1*a^-1*b1*a
c5 = u2*b1*z^-2*b1*z*b1^-2*a^-1*u2*z^-1*a^-1*b1^-1
c6 = u3*b1*z^2*b1^-2*z^2*b1*a^-1*z^-2*u3*z^-1*a^-1*b1^-1
d1 = u1*b1*z*a^-1*z^-2*a*b1^-2*z^3*b1*a^-1*u1*z^-1*a^-1*b1^-1
d2 = z^2*b1^-7*z^-1*u2^-1*z^-1*u3^-1*u1^-1*z^-2*b1^-1*z^2*u1*u2*u3
d3 = b1*z*b1*z^2*b1*z*b1*z^2*b1*z^3*b1*z^3*b1*z*a^-1*z^-1*a^-1
d4 = b1*z^2*b1^-1*z^-1*u3^-1*z^-1*a^-1*b1*z^2*b1^-1*u3^-1*z^-2*a^-1*b1*z^2*b1^-1*u3^-1*z^-2*a^-1
d5 = z^-1*b1^-1*z*b1*z*b1*z*b1^-1*u3^-1*a^-1*u2*z*b1^-1*z*b1*z^2*b1^-1*z^-1*b1*z^-1*u3^-1*a^-1*u2*z^-1*b1^-1*z*b1*z^2*b1^-1*z^-1*b1*z^-1*u3^-1*a^-1*u2
d6 = b1*z^-2*b1*z*b1^-1*z^2*b1*z^2*b1^-1*z*b1^-1*z*a^-1*z^-2*u1*u2*u3*b1*z^-2*b1*z*b1^-1*z^2*b1*z^2*b1^-1*z*b1^-1*a^-1*z^-3*u1*u2*u3*b1*z^-2*b1*z*b1^-1*z^2*b1*z^2*b1^-1*z*b1^-1*a^-1*z^-3*u1*u2*u3
```

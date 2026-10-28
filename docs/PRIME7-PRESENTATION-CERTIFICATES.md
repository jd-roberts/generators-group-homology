# Prime-7 presentation maps, membership certificates, and valid kernel words

This completes the small algebraic verification requested for Proposition 3.2
of the uploaded [Roberts 2020 v1](https://arxiv.org/pdf/2009.04069v1#page=8).
It changes no original paper, presentation or algorithm and performs no
Knuth–Bendix completion or expensive relation-module spanning calculation.

**Principal correction to the preceding work:** under the earlier convention
`f7=b1`, four of the twelve source words and five of the previously corrected
words are provably **outside** the reduced normal relation subgroup. Those
five corrected words do not define homology classes. Zero exponent sums did
not establish the missing membership hypothesis. The archived calculation
remains valid as a free-word calculation; its homology interpretation fails
under that convention.

There is also a constructive outcome. Both presentation maps are now
certified by explicit products of conjugates. Under the alternative
`f7=b0=z^-3*b1*z^3`, all twelve words have positive membership certificates.
Applying that substitution to the earlier corrected words gives **six new,
legitimate mod-7 classes**, with membership and zero exponent sums verified.
Their spanning property remains unverified.

## 1. Exact inputs and reconstruction

[The new source fixture](../tests/fixtures/roberts-v1-proposition32.g) gives
all **32 literal relators in published order** on the six free generators
`z,u1,u2,u3,a,b1`, followed by the fourteen generator images printed in
Proposition 3.2. The first printed line contains two relators, numbered 1
and 2. Relators 1–21 are on p.8; 22–32 continue on p.9. No reduced or
conjecturally corrected presentation is substituted for this fixture.

Transcription was checked against rendered PDF pages and enlarged crops.
In particular, the small inverse signs and powers in relators 18,26,27,30
were resolved from those crops, not inferred from a desired group image.
The [source manifest](evidence/paper-sources.json) identifies the exact PDF
bytes. The original group used for the comparison is precisely `F7/k7` in
[Library-of-groups.g](../Library-of-groups.g): fourteen generators and 64
relators in the stored order. The paper's symbolic fourteen-generator
relation families are not a recovered historical execution transcript.

The [word export](evidence/prime7-presentation-words.json) encodes every
relator and target as a signed integer letter list. Positive i means the
ith free generator; negative i its inverse. This is a redundant,
independently checkable export, not a new defining presentation. The GAP
export regenerates it from the source fixture and original library before
any certificate is accepted.

## 2. Explicit maps and a certified isomorphism of presented groups

Write H=F14/N64 for the stored presentation and Q=F6/N32 for the literal
Proposition 3.2 presentation. The forward free-group map phi fixes
z,u1,u2,u3,a,b1 and has the remaining images

```
b  -> z^-3*b1*z^3*a^-1
b0 -> z^-3*b1*z^3
b2 -> z^3*b1*z^-3
b3 -> z^-1*b1*z
b4 -> z^2*b1*z^-2
b5 -> z^-2*b1*z^2
b6 -> z*b1*z^-1
w  -> z^-2*u1*z^-1*u2*u3
```

The reverse free-group map psi sends `(z,u1,u2,u3,a,b1)` to the original
free generators in positions **1,2,3,4,5,8**, respectively. Its validity
is **not** assumed from those names. The certificate archive proves:

| Required assertion | Exact products verified |
| --- | ---: |
| phi(original relator) belongs to N32 | all 64 |
| psi(reduced relator) belongs to N64 | all 32 |
| `x * psi(phi(x))^-1` belongs to N64 | all 14 original generators |
| `y * phi(psi(y))^-1` is the identity free word | all 6 reduced generators |

Thus both maps descend, and their induced homomorphisms on H and Q are
mutual inverses. This is a finite algebraic certificate of the claimed
**isomorphism of these two presented groups**, independent of any homology
spanning computation. The checks also justify transferring homology classes
by the induced maps. They do not assert that the two relation modules
N64/[F14,N64]N64^7 and N32/[F6,N32]N32^7 are isomorphic; changing the number
of free generators does not generally preserve the whole relation module.

An identification of the original presented group with a particular
arithmetic SL2 still uses the appropriate external presentation theorem
and its hypotheses. The certificate here establishes the presentation
comparison; it does not establish such a ring/group identification from
matching names or a finite matrix image.

## 3. What constitutes a rigorous membership certificate here

The compressed [certificate archive](evidence/prime7-normal-closure-certificates.json.gz)
contains exact products of the form

```
W = product_j q_j * R[index_j]^(sign_j) * q_j^-1,
sign_j in {1,-1}.
```

The conjugators are explicit free words, indexed in a shared word pool.
Relator indices are one-based in the specified original/reduced fixture;
conjugator pool indices are zero-based. For each target, the independent
Python verifier multiplies the entire product and freely cancels inverse
letters, requiring exact equality with W. There is no word-problem oracle,
confluence assumption, floating-point computation or GAP group-equality
heuristic in that replay. This is a rigorous finite normal-closure witness.
For example, the first, second and third named source words are literally
reduced relators R9, R3 and R5.

Certificates were found using the defining relations, cyclic word
identities, collection with the commuting diagonal generators and conjugated
b-generators, and bounded word searches. Centrality of a^2, used for some
reverse certificates, follows from a^4 and b^3=a^2 together with the
specified generator definitions. Discovery heuristics are not trusted by
the verifier: only the final products are replayed. No Knuth–Bendix system
was constructed. Individual searches were capped at at most three seconds
and 6,000 states; an unsuccessful search was not treated as nonmembership.

To display an actual product, for example the sixth source word:

```sh
python3 scripts/verify-prime7-presentation.py --gap gap --show-certificate twelve:6
```

Other groups include `forward_relators`, `backward_relators`, `composites`,
`b0_twelve` and `b0_corrected`. For example, `backward_relators:17` prints
the product expressing the reverse image of reduced relator 17 in the
original 64 relators. Gzip is only lossless storage; the data contain no
executable proof-search code.

## 4. All twelve words: the naming convention changes membership

Keep the numbering r1,...,r12 of the literal source fixture and the
convention previously used: `(f1,f2,f3,f4,f5,f7)=(z,u1,u2,u3,a,b1)`.
The outcome is now complete:

| Words | Membership in N32 under f7=b1 | Certificate |
| --- | --- | --- |
| r1,r2,r3,r5,r6,r7,r8,r9 | Yes | explicit products of conjugates of R1,...,R32 |
| r4,r10,r11,r12 | No | exact finite matrix images below |

For the negative certificates, work in SL(2,F29), with the following
six generator matrices (entries reduced modulo 29):

```
z  = [25  0]   u1 = [24  0]   u2 = [ 3  0]
     [ 0  7]        [ 0 23]        [ 0 10]

u3 = [ 5  0]   a  = [ 0  1]   b1 = [28  7]
     [ 0  6]        [28  0]        [ 0 28]
```

These arise from xi=7, of order seven in F29, using Anton's diagonal
`D(x)=diag(x^-1,x)` and elementary `E(x)=[[x,1],[-1,0]]` expressions.
Their role here requires only exact matrix arithmetic: **all 32 reduced
relators evaluate to the identity**. The verifier additionally checks all
64 original relators and the forward generator images in the same matrix
assignment. Consequently this assignment defines homomorphisms out of
both presented groups, consistent with phi. The four word images are

```
r4  -> [19 10; 19 7]
r10 -> [19  2;  8 7]
r11 -> [19 20; 24 7]
r12 -> [19 25; 25 7]
```

None is the identity. Since N32 lies in the kernel of this matrix
homomorphism, those four words cannot lie in N32. This is a rigorous
**nonmembership certificate**, not merely computational evidence or an
incomplete rewriting result. By contrast, an identity matrix image alone
would be only a necessary condition for membership, never a positive proof.

## 5. Consequence for the previously corrected words

The previous six words h1,...,h6 are preserved in their
[original calculation artifact](evidence/prime7-corrected-words.g).
Under the same f7=b1 convention, their matrix images are

```
h1 -> [24 20;  1 19]
h2 -> identity
h3 -> [14 10;  7  3]
h4 -> [12 26; 14 28]
h5 -> [ 5 15; 26 26]
h6 -> [10 12;  4  2]
```

Thus h1,h3,h4,h5,h6 are outside N32, despite having zero exponent sums
modulo seven. They are not elements of the intended relation module and
cannot be interpreted as classes in H2. The second word is the relator
R3 and does define a class. Whether that class is zero is not decided here.
The previous conditional spanning argument was algebraically correct,
but its membership premise is now disproved for this particular list.
It must not be advertised as an unresolved but still plausible certificate
for the same f7=b1 words.

## 6. A separate, positively certified b0 variant

Let tau be the free-group automorphism fixing z,u1,u2,u3,a and sending

```
b1 -> z^-3*b1*z^3.
```

Its inverse sends b1 to `z^3*b1*z^-3`. This is an alternative interpretation
of the source symbol f7 as **b0**, as prescribed by Proposition 3.2, not
an alteration of the source words. The original fourteen-generator
library indeed has b0 in position 7 and b1 in position 8. This supports
a possible coordinate explanation but does not recover the historical
GAP objects or prove what the author intended.

Tau is not asserted to preserve N32 and is not being used as a self-map
of Q or of its homology. It selects a different list of source words in
the fixed presentation. Its being a free-group automorphism does not
itself prove membership; the separate positive certificates do that.

All **twelve** tau(ri) have positive N32 membership certificates, including
explicit products for the four formerly nonmember words. Their identity
matrix images are additional checks, not the basis for claiming membership.

Define new words `ki=tau(hi)`. They are distinct from the archived hi.
The archive supplies six positive membership products for the ki, and
[the new expanded artifact](evidence/prime7-b0-corrected-words.g) gives
explicit words in the original free generators by the verified psi map.
The word lengths in F6 are 657,4,492,374,518,537. Because tau is the identity
on abelianization, the exponent matrix D, correction matrix C and signed
coefficient matrix in the [earlier calculation](PRIME7-CORRECTED-REPRESENTATIVES.md)
are unchanged. In particular, every ki has zero exponent sums modulo seven.
This is checked directly on the words and on all fourteen coordinates of
psi(ki), not just inferred from the matrices.

Let A=N32/(N32^7[F6,N32]) and V=F6/(F6^7[F6,F6]). Each ki is now
**unconditionally a verified element of N32** whose image in V is zero.
The mod-7 five-term exact sequence for the free presentation identifies
`ker(A -> V)` with H2(Q;F7). Hence the ki legitimately represent classes,
possibly zero. The certified psi and phi transfer those classes between
H2(Q;F7) and H2(H;F7). This uses neither independence nor a spanning
assumption.

The b0 substitution resolves normal-closure membership but does **not**
resolve the paper's asserted zero images of the first six words: tau acts
as the identity on abelianization. The additional kernel correction is
still necessary. The apparent naming issue and the missing correction
must therefore be distinguished.

## 7. Exactly what remains conditional

No proof is supplied that the twelve tau(ri) span A. If that statement
is certified, the earlier split-kernel argument applies unchanged:
`ki=tau(ci) - sum_j C[i,j] tau(dj)` in A; the auxiliary image matrix D
is invertible, so the six ki span ker(A->V). This is the precise remaining
computational premise for **spanning** of the new valid list.

It is not enough to cite an unspecified old successful run. Its actual
presentation, coordinate maps, relator list and candidate list need to
match this b0 interpretation, or new certificates need to establish the
same spanning statement. The source assertion for the b1-interpreted
literal words cannot supply it, because four words are nonmembers.
The unavailable historical execution data remain a provenance gap.

There is no claim of independence, nontriviality, exact dimension six,
a new lower bound, or a new arithmetic homology theorem. The original
2009 upper bound six is not refuted. Identifying the original presentation
with the intended arithmetic matrix group remains a separate source-theorem
step beyond the presentation isomorphism certified here.

## 8. Reproduction and resource limits

```sh
python3 scripts/verify-prime7-presentation.py --gap /path/to/gap
```

The GAP phase has a five-second timeout. The combined verification has a
ten-second limit checked during certificate replay. The committed
[evidence](evidence/prime7-presentation-verification.json) records the measured
runtime, exact generator/word matrices, all certificate counts and hashes.
The recorded complete verification took **1.186891 seconds**.
There are 136 checked products comprising 67,461 conjugate factors, with
no proof search during replay. The script separately regenerates the source
word arrays, verifies substitutions and composites, and checks the new
expanded-word artifact. Every original research artifact remains unchanged.

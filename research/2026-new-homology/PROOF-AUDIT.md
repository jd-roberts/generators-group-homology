# Adversarial proof audit of the localization note

29 October 2026. Audited version: `LOCALIZATION-NOTE.md` at commit
`c6fc9dd095067204abf4515ab99214a488c7187e`.

Write $K=\mathbb Q(\zeta_7)$, $A=\mathbb Z[1/7,\zeta_7]$,
$B=A[1/2]$, and $k=\mathbb F_7$. Homology has trivial coefficients.
The audit concerns mathematical validity, not publication priority. It is a fresh
analysis of the arguments by the research agent; it is not an external referee's
endorsement. Precise source locations below refer to the linked versions.

## Verdicts

| Assertion | Verdict | Qualification or correction |
|---|---|---|
| Lemma 1, unique root-group splitting | Valid | The proof uses a central coefficient kernel of exponent p. A statement for arbitrary central kernels would be false. |
| Lemma 2, $t_R(a,1-a)=0$ when $1/p\in R$ | Valid | The rank-one Weyl relation really follows from uniqueness. The proof below supplies the parameter change omitted from the note. No universal-central-extension assertion for the ring is required. |
| The whole toral image over A is zero | Valid | Uses the standard full S-unit description, the six exact relations, and a separate argument for the cyclic coefficient contribution. |
| Integral order-seven residue classes and splitting over B | Valid | Order seven alone would not guarantee survival mod seven. The residue retraction supplies that missing justification explicitly. |
| The whole toral image over B has dimension two | Valid | The thirteen independent Steinberg relations are sufficient; an exhaustive S-unit search is unnecessary. |
| Localization exactness and dimension $2+\operatorname{rank}j_*$ | Valid | Integral perfectness removes the group-homology Tor terms. Tensoring is used only on the right. |
| $\operatorname{im}j_* = \ker(H_2(\mathrm{SL}_2(B);k)\to K_2(B)/7)$ | Valid | This is the quotient $K_2(B)/7$, not K-theory with coefficients. The stable tame map is an isomorphism mod seven. |
| Toral generation of all target H₂, or stabilization injectivity | Unproved | Neither follows from Lemma 2, elementary generation, or the unit condition. |
| Bound five from killing the second candidate | Conditional | Requires a certified spanning assertion for the six candidates. The unconditional published upper bound remains six. |

No substantive counterexample to Lemma 2 was found: its proof closes. Several
stronger inferences fail, including under surprisingly similar hypotheses; see
Section 5. The original note should be read with the proof expansions and scope
corrections here. A full explicit bar 3-chain is still not supplied.

## 1. The critical issue: does a central extension satisfy the Steinberg relations?

Fix a commutative unital ring R, an odd prime p with $1/p\in R$, and an
**arbitrary** central extension

$$
1\longrightarrow C\longrightarrow E\xrightarrow{q}\mathrm{SL}_2(R)
\longrightarrow1,\qquad C=(\mathbb F_p,+).
$$

This is the appropriate adversarial test. Checking one familiar Steinberg
extension, or checking symbols only after stabilization, would not suffice.

### 1.1 Why the root restrictions split, and why uniqueness matters

Let V be abelian with multiplication by p bijective. In a central extension of V
by C, the inverse image of V has class at most two. Its commutator induces a
bilinear pairing $\beta:V\times V\to C$. Thus

$$
\beta(v,w)=\beta(p(v/p),w)=p\beta(v/p,w)=0.
$$

The inverse image is therefore abelian. If y lifts v/p, define $s(v)=y^p$.
This is independent of y, lifts v, and is a homomorphism because the inverse
image is abelian. The difference of any two splittings is a homomorphism
$V\to C$, which vanishes by p-divisibility. This proves existence and
uniqueness without assuming that V is free, finitely generated, or a vector
space. In fact oddness is not needed for this particular argument.

Apply this to the two root subgroups $U_{ij}\cong(R,+)$. Multiplication by p
is bijective on R, so we obtain homomorphisms $X_{ij}:R\to E$. In particular,

$$
X_{ij}(r)X_{ij}(s)=X_{ij}(r+s),\qquad X_{ij}(r)^{-1}=X_{ij}(-r).
\tag{A1}
$$

Existence of some splittings would not be enough. Uniqueness is what rules out
a central error in conjugation.

### 1.2 The exact second defining relation

Hutchinson [H, Section 3.1, PDF p.5] defines $\mathrm{St}(2,R)$ by additivity
and the following relation, for each ordered pair $i\ne j$:

$$
w_{ij}(u)x_{ij}(t)w_{ij}(-u)=x_{ji}(-u^{-2}t),\qquad u\in R^\times.
\tag{A2}
$$

Here $w_{ij}(u)=x_{ij}(u)x_{ji}(-u^{-1})x_{ij}(u)$. There is no omitted
rank-three commutator relation to check in rank one.

In E define the corresponding word W. Equation (A1) gives directly

$$
W_{ij}(u)^{-1}=X_{ij}(-u)X_{ji}(u^{-1})X_{ij}(-u)=W_{ij}(-u).
$$

Matrix multiplication, independently of any Steinberg-group theorem, gives

$$
w_{12}(u)=\begin{pmatrix}0&u\\-u^{-1}&0\end{pmatrix},\qquad
w_{12}(u)E_{12}(t)w_{12}(u)^{-1}=E_{21}(-u^{-2}t).
$$

Interchanging the two indices gives the same formula for the other ordered
pair. Now the function

$$
s\longmapsto W_{ij}(u)X_{ij}(-u^2s)W_{ij}(u)^{-1}
$$

is a homomorphic section over $U_{ji}$: its projection is exactly
$E_{ji}(s)$. By uniqueness it equals $X_{ji}(s)$. Substituting
$s=-u^{-2}t$ proves (A2) **in E**, without a central discrepancy.

Thus all defining relations hold and there is a homomorphism
$\mathrm{St}(2,R)\to E$ over the elementary subgroup of $\mathrm{SL}_2(R)$.
Surjectivity onto the whole arithmetic group is unnecessary for this step.
Nor does this make the full kernel $K_2(2,R)$ central, symbol-generated, or
isomorphic to $H_2$. Those are different assertions.

### 1.3 Exactly which published symbol relations are used

In this rank-one group put $h(u)=w_{12}(u)w_{12}(-1)$ and
$c(u,v)=h(u)h(v)h(uv)^{-1}$. The precise relations needed are

$$
c(u,1)=1,\qquad c(u,v)=c(u,(1-u)v)\quad
(u,1-u,v\in R^\times).
\tag{A3}
$$

These are [H, Proposition 3.5(1),(5), PDF p.7], stated for **commutative
rings**. They are identities in the presented Steinberg group, rather than
only in stable Milnor K-theory. The enlarged PDF was inspected: (5) has the
factor $(1-u)v$, and the proposition has no field hypothesis. The note's
application is therefore supported by the actual statement.

Taking $v=1$, first with $u=a$, then with $u=1-a$, gives

$$
c(a,1-a)=1=c(1-a,a).
$$

Consequently $h(a)h(1-a)=h(a(1-a))=h(1-a)h(a)$. Their images in E commute.
These images project to $D(a),D(1-a)$. Every other choice of lifts differs
by central elements, so its commutator is also trivial. This last argument
avoids any tacit rearrangement of noncentral factors in a commutator formula.

### 1.4 Why this proves the unstable homology assertion

Given a section of E, its extension cocycle f evaluates on the toral cycle as

$$
f(D(a),D(b))-f(D(b),D(a)).
$$

For commuting matrices this is precisely the commutator of their lifts,
interpreted in C. Section 1.3 makes it zero for $b=1-a$ in **every** central
extension by C. Such extensions classify $H^2(\mathrm{SL}_2(R);k)$.
The cochain complex over k is the linear dual of the chain complex over k;
over a field its cohomology is the full linear dual of homology, including
in infinite dimension. Therefore these evaluations separate $H_2(-;k)$.
The toral cycle is zero in unstable homology itself.

This supplies a valid proof of Lemma 2. It does not infer unstable vanishing
from stable vanishing. Perfectness, homological stability, and identification
of the ring Steinberg group with a universal central extension were not used.
The indispensable inputs are the coefficient-specific root splitting and the
published rank-one identities (A3).

## 2. Audit of the toral calculations and the integral splitting

Let $U_R=R^\times$, embedded diagonally. The pairing t is bilinear and
alternating. This follows either from $H_2(U_R;\mathbb Z)=\bigwedge^2U_R$
or from the bar identity (4) of the note. It is bilinearity of **toral
commutators**, not an assumption that every rank-one symbol is bilinear.

For A, [Anton, Section 4.2, equation (4.5)] gives
$U_A\cong C_{14}\times\mathbb Z^3$ with generators $-\zeta,u,v,w$.
The note's six rows have determinant $-300\equiv1\pmod7$. By Lemma 2 their
images vanish, so the entire exterior part vanishes. In particular the
specified row combination gives $t_A(u,v)=0$.

There is an additional coefficient issue: $H_2(U_A;k)$ is not just the six
exterior directions. The UCT quotient is $H_1(U_A;\mathbb Z)[7]\cong k$.
One may realize it by the inclusion of the actual torsion subgroup $C_{14}$.
On $H_2(C_{14};k)$, the integral Bockstein is an isomorphism onto
$H_1(C_{14};\mathbb Z)[7]$, so inversion acts by $-1$. The Weyl matrix
inverts $U_A$ and is inner in the ambient group. It acts trivially on ambient
homology, so the image of this one-dimensional summand equals its negative
and vanishes. This argument uses a functorial torsion-subgroup inclusion,
not a presumed natural splitting of UCT for all abelian groups.

For B the exact valuation sequence is split by the two principal prime
elements, giving $U_B\cong C_{14}\times\mathbb Z^5$. There are fifteen
exterior directions and again one cyclic coefficient direction. Lemma 2
kills the thirteen independent certified rows. The cyclic direction is killed
as above. Thus $\dim T_B\le2$; the lower bound comes from the following
independent residue argument.

The factorization of $\Phi_7\bmod2$, irreducibility of its cubics, and
the identities $\pi_1\pi_2=2\zeta^3$,
$\pi_2=\zeta^3\overline{\pi_1}$ give
$(\pi_i)=\mathfrak q_i$ and $v_{\mathfrak q_j}(\pi_i)=\delta_{ij}$.
The residue fields have eight elements, and the reduction of $\zeta$ has
order seven in each. These establish that the tame residues below really
are generators, rather than merely nonzero-looking formal expressions.

For $e_i=t_B^{\mathbb Z}(\zeta,\pi_i)$, bilinearity gives $7e_i=0$.
Its stable image, checked after inclusion in K, is
$\{\zeta,\pi_i\}-\{\pi_i,\zeta\}=2\{\zeta,\pi_i\}$.
Here [H, Corollary 4.2 and Section 3.3] fixes the factor two, and stable
localization injects $K_2(B)$ into $K_2(K)$. With the tame convention in
[H, Theorem 5.17], the residue vectors are $(-2,0)$ and $(0,-2)$.
Therefore the map $s:(C_7)^2\to H_2(\mathrm{SL}_2(B);\mathbb Z)$ taking
the standard generators to $3e_1,3e_2$ satisfies $\delta s=1$.

This proves integral independence, order exactly seven, and splitting.
**Correction to an implicit shortcut:** an element of order seven can be
zero modulo seven, as the element 7 in $\mathbb Z/49$ shows. Here the
retraction $\delta s=1$ proves survival on tensoring. It follows that
$T_B=\langle\bar e_1,\bar e_2\rangle$, and its intersection with the
localization image is zero. The Galois identities in the note then give the
claimed equivariant splitting; they do not use six-class spanning.

The existing checker was replayed, without modifying it or rerunning the
discovery search. It confirms all nineteen polynomial identities, the two
ranks, the selected-cycle row combination, the residue matrix, and the
prime/Galois identities. These are finite arithmetic certificates. Sections
1–2 above explain the additional mathematical implications that a checker
cannot establish by itself. No explicit Steinberg bar filling was extracted.

## 3. Localization, perfectness, and change of coefficients

The applicable published theorem is [H, Theorem 5.17], followed by Corollary
5.20. Its hypotheses are a global-field S-integer ring, all infinite places
in S, $|S|\ge2$, a nonzero prime $\mathfrak q$ with a principal power
$\mathfrak q^m=xR$, and a unit $\lambda$ with $\lambda^2-1$ also a
unit **in the initial ring**. Its conclusion has no initial zero, and its
boundary is stable tame residue. It is not a general localization theorem
for arbitrary Dedekind domains.

Here S has three complex places and the prime above seven. At both
localization steps $\lambda=\zeta$ works, since $1-\zeta^2$ has norm
seven. The prime powers can be taken with $m=1,x=\pi_i$. Elementary
generation follows from [H, Proposition 2.2(1)]; perfectness follows directly
from the upper and lower root commutator identities with denominators
$\lambda^2-1$ and $\lambda^{-2}-1$, respectively. Thus both H₁ groups
vanish integrally. We obtain

$$
H_2(\mathrm{SL}_2(A);\mathbb Z)\longrightarrow
H_2(\mathrm{SL}_2(B);\mathbb Z)\xrightarrow{\delta_{\mathbb Z}}(C_7)^2
\longrightarrow0.
\tag{A4}
$$

Natural UCT gives

$$
0\to H_2(G;\mathbb Z)/7\to H_2(G;k)\to H_1(G;\mathbb Z)[7]\to0.
$$

For these two ambient groups the last term is zero. Tensoring (A4), a
right-exact operation, therefore gives exactly the mod-seven sequence in the
note. There is no assertion of injectivity of its first arrow. In particular
$\dim H_2(\mathrm{SL}_2(B);k)=2+\operatorname{rank}j_*$.
The interval 2–8 uses the published bound as an input; it is not an
independent re-verification of the historical computation.

The explicit splitting from Section 2 strengthens (A4) to a direct sum and
therefore avoids any residual tensor-injectivity issue for its right summand.
It says nothing about injectivity of the source localization map.

## 4. Stable K-theory: which group, which hypotheses?

The class-number argument is valid: the Minkowski bound is less than five,
and there are no prime ideals of norm two, three, or four. Thus
$\mathrm{Pic}(A)=\mathrm{Pic}(B)=0$.

The exact comparison being used is Tate's theorem as formulated in [W,
Theorem 4, printed p.145]. For a number-field S-integer ring with $1/7$,

$$
K_2(R)/7\simeq H^2_{\mathrm{et}}(R,\mu_7^{\otimes2}).
$$

The presence of the chosen primitive seventh root identifies the twist with
$\mu_7$. Kummer's sequence then gives

$$
0\to\mathrm{Pic}(R)/7\to K_2(R)/7\to\mathrm{Br}(R)[7]\to0.
\tag{A5}
$$

The twist identification depends on the root choice; dimensions and the
tame calculation are unaffected. With no real places, the Brauer invariant
sequence [W, (5.6)] is the kernel of the sum of invariants over the inverted
finite places. A has one such place and B three. Consequently

$$
K_2(A)/7=0,\qquad \dim_k K_2(B)/7=2.
$$

For an independent check on the comparison with tame residue, stable
localization for these regular dimension-one rings gives

$$
0\to K_2(A)\to K_2(B)\xrightarrow{\tau}(C_7)^2\to0.
\tag{A6}
$$

This is the usual stable tame-kernel sequence, also recorded in [H,
Section 5.6]; finite residue fields have $K_2=0$. Tensoring (A6) and using
$K_2(A)/7=0$ proves $\tau\bmod7$ is an isomorphism. No left-exactness
of tensor is assumed. The compatibility in [H, Theorem 5.17] now proves

$$
\ker\big(s_B:H_2(\mathrm{SL}_2(B);k)\to K_2(B)/7\big)
=\ker\delta=\operatorname{im}j_*.
\tag{A7}
$$

The map $s_B$ here is induced from **integral** stabilization using
perfectness and UCT. It is not defined by identifying its target with
$K_2(B;\mathbb Z/7)$. The latter has the coefficient exact sequence

$$
0\to K_2(B)/7\to K_2(B;\mathbb Z/7)\to K_1(B)[7]\to0,
$$

and its right term is nonzero: the determinant and unit inclusion exhibit
$\mu_7\subset K_1(B)[7]$. Suppressing that term would be an error.
The note does not make that identification, but the distinction should
remain explicit in subsequent work.

The surviving unstable issue is real even though the field has no real
embeddings. [H, Lemmas 6.1 and 6.8] identify the integral comparison for B
as a surjection to $K_2(B)$, with kernel $\mathcal K_{S_B}$. They do not
make that kernel vanish. One must also not replace its mod-seven analogue
by $\mathcal K_{S_B}/7$ without considering the Tor boundary for this
short exact sequence. Equation (A7) does not require that replacement.

## 5. Attempts to break overgeneralized statements

**Dropping the root hypothesis.** A central extension of an arbitrary
abelian group by $C_p$ need not split: $C_{p^2}\to C_p$ is an example.
Replacing the coefficient kernel by an arbitrary abelian group is also
invalid, even for a uniquely p-divisible quotient. The rational Heisenberg
group of triples $(x,y,z)$, with multiplication
$(x,y,z)(x',y',z')=(x+x',y+y',z+z'+xy')$, is a central extension of
$\mathbb Q^2$ by $\mathbb Q$. The commutator of lifts of $(1,0)$ and
$(0,1)$ is $(0,0,1)$, independent of the lifts, so it cannot split.
These examples explain why the proof must retain its coefficient and
root-divisibility hypotheses; they do not contradict Lemmas 1–2.

**Dropping the initial-ring unit condition in localization.** [H, Remark
5.18] gives the explicit failure for $\mathbb Z[1/3]\to\mathbb Z[1/6]$.
The congruence-subgroup H₁ term cannot be replaced by $\mathbb F_2^\times$,
despite the existence of suitable units after localization. Remark 5.19
also explains why arbitrary Dedekind domains have a Milnor–Witt, rather
than merely a multiplicative-residue-field, obstruction.

**Root splittings do not imply toral generation or injectivity.** Consider
$R=\mathbb Z[1/42]$ with coefficients k. It has $1/7$, $1/2$,
elementary generation, perfectness, and a unit $\lambda=2$ with
$\lambda^2-1=3$ invertible. Nevertheless [H, Theorem 6.12] gives

$$
H_2(\mathrm{SL}_2(R);\mathbb Z)\cong\mathbb Z\oplus C_2\oplus C_6,
\qquad H_2(\mathrm{SL}_2(R);k)\cong k.
$$

Every toral class has zero free component. Indeed the injective field
comparison of [H, Theorem 6.10 and Lemma 6.11] sends it to $c(a^2,b)$,
by Corollary 4.2. Its real quadratic-form component is zero because
$a^2$ is a square; [H, Lemma 6.3] detects the free component by this real
component. Its integral toral image is therefore contained in the torsion
subgroup, which has no seven-primary part. Also $R^\times$ has no
seven-torsion, so no cyclic coefficient class has been missed. Thus its
whole mod-seven diagonal-torus image is zero while its H₂ is nonzero.
Stable $K_2(R)$ is finite with no seven-primary part, so its mod-seven
stabilization also fails injectivity.

This is an actual counterexample to the proposed *general shortcut*, not to
the desired assertion for B. The real-place summand distinguishes it from
B, but the example shows exactly why the unique-root-lift argument alone
cannot prove generation.

**Infinite units and elementary generation do not ensure a symbol
presentation.** Chen–You [CY, Theorem 1(a)] supply S-integer examples not
universal for $\mathrm{GE}_2$. Taking $p=7,n=2$ gives the ring of integers
of $\mathbb Q(\sqrt{-14})$, localized at seven, which has infinite units
and $1/7$, but whose rank-one $K_2$ is not generated by symbols. This
does not directly compute its H₂; it refutes treating symbol generation
as an automatic consequence of arithmetic elementary generation.

## 6. What the strongest applicable comparison actually leaves missing

With the preceding audit complete, the theorem search can be assessed
without presuming injectivity. The strongest general **published**
S-integer comparison located is [H, Theorem 6.10], together with Lemmas
6.1 and 6.8. It gives stabilization for all sufficiently enlarged S. Its
proof starts with the finitely generated kernel $\mathcal K_S$, uses the
filtered colimit to kill its generators at some finite enlargement, and
then propagates vanishing to larger sets. It supplies no effective assertion
that the required enlargement is contained in $\{\mathfrak q_1,\mathfrak
q_2\}$. The precise missing assertion for B is the absence of its
mod-seven comparison kernel; restating the existence theorem with B in
place of the unspecified enlargement would be circular.

The recent preprint [APRV, Theorem 3.13 and Remark 3.14] retains an
existential $S_0$. In this field its residue-field-$\mathbb F_2$ set is
empty, and containing that set is not a sufficient theorem hypothesis.
Its unusual definition of a “totally imaginary” S-integer ring on PDF p.4
excludes only the case with no finite inverted places and all infinite
places complex. Thus B is not excluded by that definition; this resolves
a possible reading objection but does not provide a stability threshold.
This work is a 2026 preprint, not a published theorem being invoked to
settle our example.

There is also a more precise alternative to assuming a symbol presentation.
Mirzaii–Torres Pérez [MT, Section 5, equation (5.2)] give, for a commutative
ring R with 2 invertible, an exact sequence

$$
H_2(P_R;\mathbb Z)\longrightarrow H_2(E_2(R);\mathbb Z)
\longrightarrow\mathcal I^2(R)\longrightarrow0,
\tag{A8}
$$

where $P_R$ is the upper triangular subgroup. Here $\mathcal I^2$
denotes **their** $I^2$, defined as a spectral-sequence kernel, to avoid
confusing it with the usual square of a Witt-ring fundamental ideal.
Explicitly start with the exact complex
$0\to Z_1Y\to Y_1\to Y_0\to\mathbb Z\to0$ of elementary unimodular
configurations. Put
$\mathcal{GW}(R)=H_0(E_2(R),Z_1Y)$, and let
$\mathcal I(R)$ be the kernel of its edge map to $\mathbb Z$.
Then $\mathcal I^2(R)=\ker(d^2_{2,0})$ on $\mathcal I(R)$, as defined
in [MT, Sections 3 and 5]. Over nonlocal rings this definition retains
information not present in the Witt theory of the fraction field.

For our B, (A8) gives the following useful, but not yet evaluated,
obstruction:

$$
H_2(\mathrm{SL}_2(B);k)/T_B\ \cong\ \mathcal I^2(B)/7.
\tag{A9}
$$

Here are the coefficient details. The additive group of B is torsion-free,
and $H_q(B^+;\mathbb Z)=\bigwedge^q B^+$, obtained by filtered colimits
from finitely generated free abelian subgroups. For $q>0$, multiplication
by seven on these exterior powers is bijective: exterior powers commute
with localization, and $B^+$ is already a $\mathbb Z[1/7]$-module. They have no seven-torsion. UCT therefore gives
$H_q(B^+;k)=0$ for every positive q. The split extension
$B^+\to P_B\to U_B$ has, by its homology spectral sequence,
$H_2(P_B;k)\cong H_2(U_B;k)$. Thus the integral left arrow in (A8),
after tensoring, has image contained in $T_B$. Conversely all exterior
toral cycles come from integral $H_2(P_B;\mathbb Z)$; the only additional
cyclic mod-seven toral class has zero ambient image by Section 2.
The image is exactly $T_B$. Perfectness identifies the middle tensor
term with ambient mod-seven H₂, proving (A9) by right exactness.

Consequently the exact missing lemma for this route is

$$
\boxed{\mathcal I^2(B)/7=0.}
\tag{A10}
$$

This is equivalent to toral generation here, and by (A7) and the proved
toral splitting, equivalent to stabilization injectivity. Equation (A9) is
a deduction from the cited spectral sequence, not a vanishing result or a
novelty claim. It does not provide an easier computation automatically.

[MT, Remark 5.4] is the closest generation statement located. It assumes
R **semilocal**, 2 invertible, and residue fields larger than four, and
includes corrected symbol cycles in addition to toral and root cycles.
B has infinitely many maximal ideals and is not semilocal. Its large
residue fields do not substitute for that hypothesis. Moreover even that
generation statement is not a claim of generation by toral cycles alone.
Their Lemma 5.1 and Theorem 2.5 expose a further obstruction involving
$H_1(Y_\bullet(B^2))_{E_2(B)}$, with
$H_1(Y_\bullet(B^2))\cong(K_2(2,B)/C(2,B))^{ab}$.
Neither its vanishing nor universality for $\mathrm{GE}_2$ has been
proved for B in this project. Field Milnor–Witt comparison cannot erase
this configuration-space obstruction over the ring.

For clarity, because $\lambda^2-1$ is a unit, the additive coinvariants
$B_{U_B}$ in [MT] vanish. Their Lemma 5.1 therefore reads

$$
\overline I^{\,2}(B)\longrightarrow\mathcal I^2(B)
\longrightarrow Q_B\longrightarrow0,\qquad
Q_B=H_1(Y_\bullet(B^2))_{E_2(B)}.
$$

Here $\overline I^{\,2}$ is the formal unit square-class ideal in that
paper, not the field's Witt ideal. Right exactness modulo seven gives a
concrete two-part sufficient criterion for (A10): the formal-unit image
must vanish modulo seven, and $Q_B/7$ must vanish. Proving only the latter
would leave the former uncontrolled.

**Recommended next proof attempt:** analyze these two terms in [MT, (5.1)],
starting with the formal unit square-class relations, and determine exactly
what remains in $Q_B/7$. This is a specific theoretical obstruction test,
before any new computation or claim that all classes are toral. It may
fail; if it does, its failure identifies the part that a proof using
individual presentation classes must address. No vanishing assumption for
(A10), no new candidate calculation, and no general rewriting development
are implicit in this recommendation.

## 7. Scope, corrections, and sources

The main homological conclusions of the audited note survive. Necessary
clarifications are: make the parameter-adjusted uniqueness argument in
Section 1 explicit; use the residue retraction to justify mod-seven
survival; distinguish quotient K₂ from K-theory with coefficients; and
retain the cyclic torus coefficient summand until the Weyl argument kills
it. The conditional candidate bound, absence of an explicit filling, and
unknown rank remain unchanged. “No decisive structural reduction” in the
earlier note can now be refined to the unevaluated obstruction (A9).

The unit-action statements in Section 7 of the original note also pass this
audit at the stated theoretical level. Squares act by inner automorphisms,
since $\operatorname{diag}(v^2,1)=vI\,D(v)$. The unit square-class group of
A is $(C_2)^4$, and Maschke's theorem applies over k because $7\nmid16$.
In the determinant split extension for $\mathrm{GL}_2(A)$, perfectness
removes the degree-one kernel row; the section protects the base row and
kills the possible differential into degree-two coinvariants. This gives
the stated degree-two direct sum with $H_2(U_A;k)$, which has dimension
seven. It does not evaluate the coinvariants or identify the action of
units with the different Galois action.

No counterexample search in groups, completion, new software, or substantial
computation was performed. The only calculation replay was the existing
finite arithmetic checker. Main, original data, original algorithms,
published papers, and the verification branch were not changed. This audit
does not recertify any six-class spanning assertion or establish priority
for the specialized toral conclusions.

Sources were read as mathematical statements, not just search snippets.
Enlarged local PDF renderings were inspected for [H] pp.5,7,21 and [APRV]
p.4; [W] p.145 and [MT] Section 5 were also checked against their PDFs.
The original Tate article was not successfully retrieved, so the exact
version used is explicitly Weibel's published formulation. The linked
arXiv versions of [MT] and [APRV] are preprints; a journal publication for
[MT] was not independently established during this audit, so the earlier
note's unqualified “published 2026” is not relied on.

- **[H]** Kevin Hutchinson, *The second homology of SL₂ of S-integers*,
  J. Number Theory **159** (2016), 223–272,
  [DOI](https://doi.org/10.1016/j.jnt.2015.07.022),
  [author version](https://arxiv.org/abs/1412.0953v3).
  Proposition 2.2; Section 3.1; Proposition 3.5(1),(5); Corollary 4.2;
  Theorem 5.17; Remarks 5.18–5.19; Corollary 5.20; Lemmas 6.1,6.3,6.8;
  Theorems 6.10,6.12. PDF page numbers above are those of this author version.
- **[W]** Charles Weibel, *Algebraic K-Theory of Rings of Integers in Local
  and Global Fields*, Handbook of K-Theory (2005), 139–190,
  [PDF](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/weibel-ints.pdf).
  Theorem 4, equation (5.6), Example 5, printed p.145.
- **[Anton]** Marian F. Anton, *Homological symbols and the Quillen
  conjecture*, J. Pure Appl. Algebra **213** (2009), 440–453,
  [author version](https://arxiv.org/abs/0804.3553v1), Section 4.2, (4.5).
- **[CY]** Sheng Chen and Hong You, *Subrings in imaginary quadratic fields
  which are not universal for GE₂*, Acta Arith. **107** (2003), 299–305,
  [published PDF](https://www.impan.pl/shop/en/publication/transaction/download/product/81929).
  Theorem 1 and Section 2. The specialization above has
  $d=-7(7^2+1)=-350$, defining the field $\mathbb Q(\sqrt{-14})$.
- **[MT]** Behrooz Mirzaii and Elvis Torres Pérez, *The low dimensional
  homology groups of the elementary group of degree two*,
  [arXiv:2407.17632v3](https://arxiv.org/abs/2407.17632v3),
  1 November 2025 revision. Sections 3,5, equations (5.1),(5.2), Lemma 5.1,
  Remark 5.4 and Theorem 2.5. Preprint numbering used throughout.
- **[APRV]** Pedro H. Amorim, Isadora V. Picinini, Bruno R. Ramos, Thiago
  Verissimo, *The Schur multiplier of SL₂ and Dedekind zeta-functions over
  S-integers*, [arXiv:2609.28677v2](https://arxiv.org/abs/2609.28677v2),
  2 October 2026. Definition on p.4; Theorem 3.13; Remark 3.14. Preprint.

Targeted literature searches through 29 October 2026 located no theorem
certifying (A10) for this B. This is a statement of the search's outcome,
not a proof of novelty or a claim of exhaustive coverage.

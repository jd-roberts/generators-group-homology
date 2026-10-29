# R7=a^4: fixed plan prepared before the one authorized search

This file fixes the mathematical inputs, ordering and budgets **before launch**.
The static preparation is in
`benchmarks/results/prime7-a4-1-2026-10-28/preparation/`.
No arithmetic word search was used for that inspection. The experiment result
will be recorded separately; this plan is not a claim of success.

## Mathematical analysis

F has ordered generators z,u1,u2,u3,a,b1. The unchanged quotient has 236 rows:
192 commutators [x_i,R_j], 32 powers R_j^7 and the twelve b0-interpreted
candidates Q225,...,Q236. The static inventory records every literal word,
label, exponent vector, a-letter count and cyclic power decomposition.
143 rows contain a. The only row conjugate in the free group to a pure a-power
is **Q199=a^28**. It does not imply a^4=1: a generator of C28 is a counterexample
to that inference (not an image of the full Q).

The candidate a-exponent sums are
`0,0,0,-1,-2,-2,-2,0,-2,-3,-3,-3`. Their six-coordinate exponent matrix has
rank six over F7. In abelianization modulo seven, the target image 4a equals
three times the Q228 image plus twice the Q232 image. This is a **necessary
abelian condition**, not a word certificate; a and b1 cannot be commuted or
other letters discarded on that basis.

The existing occurrence/identity rows M,Z have combined rank 17. The target
e7 is outside their span. In fact their seventh coordinates all vanish:
the dual vector e7 annihilates these *known rows*. This is a statement about
the available finite certificate system, not a homomorphism out of Q, lower
bound, or mathematical obstruction. No linear dependence has been disproved.

There is useful stronger structure. Set t=a^2, c=z^-3*b1*z^3 and b=c*a^-1.
The candidate S=Q228 is exactly b^3*t. It gives

    C(t,c)=C(t,b)=(b^-3*S*b^3)*(b^-2*S^-1*b^2),
    C(t,g)=t*g*t^-1*g^-1.

Thus t commutes with c without assuming a^4=1. For an inversion word
r=u*a*u*a^-1, the free identity

    C(t,u)=r^-1*(u*a)*r*(u*a)^-1

gives two-factor certificates for u=z,u1 using Q225,Q227. Even when r is
only central, a second free identity gives

    C(t,u)=u*[u,r]*u^-1 * (u*a)*[a,r]*(u*a)^-1.

Use Q75,Q139 for u2 and Q100,Q132 for u3. Finally b1=z^3*c*z^-3, so
`C(t,v*w)=C(t,v)*v*C(t,w)*v^-1` supplies a fourteen-factor certificate
for C(t,b1). Together with the free C(t,a)=1, this establishes **a^2 central
in Q**, via original-Q products. Twenty signed commutation equations
`t^s*g^e = g^e*t^s` will be compiled with explicit products in the experiment.
They are not unchecked rewriting assumptions or new defining relators.

Centrality makes a^4 a central element of order dividing seven; it does not
kill it. We still need a certified a^(4m) with 7 not dividing m, or a direct
a^4 certificate. The mixed cubic Q228, seven-b-factor Q233, unit/b candidates
Q229–Q231 and Q234–Q236, and unit/b commutator/power rows are possible bridges.
They involve noncommuting words. The existing power recognizer cannot turn
their exponent sums into pure a powers. This justifies a bounded completion
fallback after the structured phase, without claiming it will work.

## Fixed input and search sequence

The input set is **all original 236 Q rows**, frozen from blueprint SHA256
`d33076b1c1b20c9950349645e77c0dbcebe9c8e326ba77dd041b6b696b134a60`.
No raw R7 or other unproved Rj may be inserted. The only search target is R7.

1. Start one five-second alarm and monotonic deadline covering all discovery,
   lemma compilation, indexing/seeding, completion and result checkpointing.
2. Run the existing power compiler for at most one second on its fixed
   20-row view: Q199; Q225–Q236; Q7,Q39,Q71,Q103,Q167,Q132,Q139.
   Its existing limits remain 128 equations, word 128, 2,000 factors and
   2,000 counted operations. Map every proof back to its original Q index.
   Record its a^4 answer. On a checked success, stop the experiment.
3. Otherwise create one counted completion system for the remaining shared
   time. First seed both signs of the five already certified words
   R3,R5,R9,R12,R15, with their original-Q products. Next seed the twenty
   signed a^2-centrality equations above. Next use any checked *derived*
   power-stage equations (Euclid or inversion/centrality origins only).
4. Feed each Q row once as Q_i=1, in the **frozen plan order**: all twelve
   candidates, then Q199, then all remaining rows by (length,index). Do not
   enumerate every cyclic split at initialization. Check the target after
   each seed/input; a certified success stops discovery immediately.
5. If inputs finish and the target remains unresolved, process the one
   completion queue. The existing strictly decreasing shortlex equation
   operations and proof constructors are retained. Count separately:
   rule-pair jobs queued/processed; offsets examined; compatible overlap
   placements; placements submitted as equations; oversized placements.
   On any hard budget exception, preserve proofs and stop; no restart.

This differs from the earlier generic cyclic-seeding constructor specifically
to avoid spending the rule budget before the mixed input rows can be read.
It is a fixed seeding strategy, not an unrestricted new completion algorithm.
There is no BFS and no target-state queue.

## Limits, acceptance and fail-closed gates

Hard OS caps: 512 MiB AS, six CPU seconds, ten external wall seconds,
8 MiB per output file. Read back inherited AS/CPU/FSIZE before discovery.
One shared search alarm: five seconds, never reset. Completion: at most
256 retained rules including cancellation rules; at most 4,000 cumulative
queued rule-pair jobs; word/overlap length 512; at most 2,000 proof factors
and 2,000 reduction steps per call. Overlap placements are counted separately,
not mislabeled as rule-pair jobs. No automatic retries or cap increases.

Before launch: repeat all eight resource probes, existing certificate suite,
new formal-identity/counter tests and parent/subclass comparisons on the ten
small fixtures. Abort on failure. An exclusive attempt marker consumes the
one authorization even if a launch fails. Preserve frozen inputs, plan,
source snapshots/hashes, raw JSONL, proofs, accounting, CPU/wall/RSS and
termination. Stream rule certificates so completed records survive a later
resource termination.

The independent checker imports no search or algebra compiler. It rebuilds
the 236 rows and checks every emitted equation and positive target by free
cancellation. A partial trace accepts only complete checked records. A
nonidentity result or budget stop is unresolved. New a^2-centrality products
are auxiliary identities, not assertions that any additional original Rj
has been killed.

Only if R7 is certified, append its unit row to the verified M,Z system and
independently check new row-combination witnesses for every original target
that follows. Without that certificate, neither e7 nor conditional witnesses
may be counted as established. An emitted equation literally equal to another original target may be
classified during certificate replay; no extra goal search is performed.
No other arithmetic target search is authorized.

# R7=a^4: mathematical analysis and the one bounded experiment

**R7 remains unresolved.** The single authorized experiment stopped while
seeding its inputs, before processing any critical-pair jobs. It exceeded the
predeclared 2,000-factor bound on an accumulated proof while simplifying
Q217=R25^7. This is an initialization/proof-representation limit, not a
mathematical obstruction or a completed test of the full quotient.

There is a certified structural consequence: **a^2 is central in the original
fixed quotient Q**. Twenty signed commutation equations have independently
verified products in the original Q relators. They do not establish a^4=1.
No new original defining relator was certified; the total remains five of 32.

## 1. Exact input inspection and the missing mathematical step

The unchanged input is the 236-row quotient from
[the earlier criterion](PRIME7-SPANNING-CERTIFICATE-PLAN.md):
192 commutators [x_i,R_j], 32 seventh powers, and the twelve b0-interpreted
candidate words Q225–Q236. R7 is a^4, Q199 is a^28. No raw R7 was inserted
as an input equation. Every literal word, label, a-occurrence count,
abelian exponent vector and certified cyclic-power decomposition is in the
[static inventory](../benchmarks/results/prime7-a4-1-2026-10-28/preparation/analysis.json).
The static inspection did not invoke a word-problem search.

143 rows contain a. **Only Q199 is conjugate, as a free word, to a pure
power of a.** Thus immediate common-root Euclid has only the exponent 28;
it cannot produce exponent four. A cyclic group of order 28 demonstrates
why neither that power relation nor centrality suffices. This group is
not asserted to satisfy all 236 Q relations or to obstruct their consequence.

The candidate a-exponent sums are

    0,0,0,-1,-2,-2,-2,0,-2,-3,-3,-3.

Their full exponent matrix has rank six over F7. In particular the abelian
image of a^4 is `3*image(Q228)+2*image(Q232)` modulo seven. This necessary
condition says nothing about the noncommuting factors that separate these
actual words. Replacing them by their a-exponent sums would be unsound.

The existing verified occurrence and identity matrices M,Z have rank 17
when stacked. Their seventh column is zero, so e7 is outside their row span.
The dual vector e7 annihilates **these available rows** and has value one on
the target coordinate. It is not a homomorphism out of Q or a nonmembership
obstruction: new identities among the original relators may change the
certificate row space. The old five unit-vector witnesses remain valid.

The interactions most relevant to a are:

| Original Q rows | Role |
| --- | --- |
| Q199 | a^28; necessary power information only |
| Q7,Q39,Q71,Q103,Q167 | centrality of a^4 under z,u1,u2,u3,b1 |
| Q225,Q227 | inversion words for z and u1 under a |
| Q228 | mixed cubic involving c=z^-3*b1*z^3 and a |
| Q75,Q139 and Q100,Q132 | centrality of the u2/u3 inversion defects |
| Q229–Q231 | mixed unit/b/a candidate relations |
| Q232 | sevenfold b-power/unit-conjugation candidate; useful abelian necessary condition |
| Q233 | seven b-factors and two a^-1 factors |
| Q234–Q236 | further cubic mixed candidates |
| Q217–Q224 | seventh powers of the longer mixed relators R25–R32 |

No inversion of a or independent pure a^(4m), with 7 not dividing m, was
identified in the literal inputs. A proof must obtain such a power from
noncommuting relations, or produce a direct a^4 identity. Merely centralizing
a^4, projecting away other generators, or counting a letters cannot do that.

## 2. A verified structural lemma: a^2 centralizes every generator

Use the standard commutator word `C(t,g)=t*g*t^-1*g^-1`, distinct from GAP's
`[x,y]=x^-1*y^-1*x*y`. Put

    t=a^2, c=z^-3*b1*z^3, b=c*a^-1, S=Q228=b^3*t.

Free cancellation verifies

    C(t,c)=C(t,b)
          =(b^-3*S*b^3)*(b^-2*S^-1*b^2).                  (1)

Thus c commutes with t, without assuming R7. For an inversion word
`r=u*a*u*a^-1`, two further free identities are

    C(t,u)=r^-1*(u*a)*r*(u*a)^-1,                        (2)
    C(t,u)=u*[u,r]*u^-1 * (u*a)*[a,r]*(u*a)^-1.          (3)

Equation (2) uses two copies of r, with opposite signs; apply it to the
actual candidate rows Q225,Q227 for z,u1. Equation (3) uses commutator
relations even if r itself has not been killed: Q75,Q139 give the u2 product,
and Q100,Q132 give u3. No raw R4 or R11 is imported as a relation.

Finally b1=z^3*c*z^-3. Applying

    C(t,v*w)=C(t,v) * v*C(t,w)*v^-1

and the inverse version to (1)–(2) gives a fourteen-factor original-Q product
for C(t,b1). The products for z,u1,u2,u3 each have two factors; C(t,a) is freely
trivial. The compiler derives both signs of t and of each non-a generator,
with the conjugators needed for negative signs. All twenty resulting
equations `t^s*g^e=g^e*t^s` were checked by an independent free-cancellation
checker, both as formal identities and against the actual original Q words.

The exact signed products are in
[preflight-centrality.json](../benchmarks/results/prime7-a4-1-2026-10-28/preflight-centrality.json),
and in the streamed experiment trace. This is an unconditional, certificate-
backed assertion about this fixed presented quotient. It does not depend on
the historical spanning assertion, an arithmetic matrix identification, or
confluence of rewriting. We make no claim that this structural lemma is new
to the literature or supplies a new homology theorem.

It follows that a^4 is central and its order divides seven. **A nontrivial
central element of order seven is still possible on this information alone.**
The missing step remains the same word identity as before.

## 3. Fixed plan, gates and exact execution

The [plan](PRIME7-A4-EXPERIMENT-PLAN.md) and its machine-readable
[plan.json](../benchmarks/results/prime7-a4-1-2026-10-28/preparation/plan.json)
were prepared and hashed before launch. The input blueprint SHA256 is
`d33076b1c1b20c9950349645e77c0dbcebe9c8e326ba77dd041b6b696b134a60`.
The experiment used one fixed 236-row input, not a changing FindBasis quotient.

The discovery sequence was:

1. Existing power compiler, at most one second, on the fixed 20-row view
   containing all twelve candidates, Q199, the five nonempty a^4 centrality
   rows and Q132,Q139. Proof indices were mapped back to original Q indices.
2. On no success, one completion system for the remainder of the shared time.
   Seed both signs of R3,R5,R9,R12,R15 using existing verified products, then
   the twenty signed centrality equations (1)–(3). Only checked genuinely
   derived power equations could become further seeds.
3. Seed each original Q row as Q_i=1, first all twelve candidates, then Q199,
   then remaining rows ordered by (length,index). Do not enumerate all cyclic
   splits during initialization. Check only the a^4 target after each step.
4. Process the counted critical-pair queue only after input seeding finishes.

All eight OS safety probes passed, including deliberate memory, CPU, wall and
output exhaustion and escaped-session descendant cleanup. Eleven existing
verification commands and three constrained small workers passed. Previous
completion/power/control/pilot certificate replays and their evidence manifests
passed unchanged. New tests checked every formal signed centrality identity,
rejected a deleted factor, compared the counted subclass with the unmodified
parent on ten small fixtures, and verified exactly four overlap placements
from a single toy rule-pair job. Final tested-source hashes matched at launch.
An earlier small-only infrastructure record is retained separately; its source
hash predates the additional interrupted-placement accounting field. The
**final-infrastructure** record was the launch gate.

The attempt was reserved once with an exclusive marker. No restart, larger
budget, second arithmetic target or follow-up search was launched.

| Setting | Fixed limit |
| --- | ---: |
| Shared search wall, all stages | 5 s |
| Hard address space / CPU / external wall | 512 MiB / 6 s / 10 s |
| Hard size of each output file | 8 MiB |
| Retained completion rules, including cancellation | 256 |
| Cumulative queued rule-pair jobs | 4,000 |
| Completion word/overlap length | 512 |
| Factors in an accumulated proof / reduction steps per call | 2,000 / 2,000 |
| BFS index / target-state queue | not used |

The 2,000-factor bound was an **additional conservative bound chosen in the
pre-launch plan**, not a limit imposed by the user's OS/time budget. It is
the bound that stopped this experiment. It was not raised when reached.
The worker asserted literal inherited AS/CPU/FSIZE values before discovery.
A single five-second alarm covered construction, seeding, completion and
checkpoint emission. Output rules were streamed with products referencing
the original Q rows.

## 4. Recorded result and independent verification

| Measurement | Recorded result |
| --- | ---: |
| R7=a^4 | unresolved / factor_limit |
| Power equations / counted operations | 20 / 1,285 |
| Power-stage answer / truncations | no applicable certified power / none |
| Power-stage result elapsed | 0.005396356 s |
| Original input rows completed | 228 of 236 |
| First unfinished row | Q217=R25^7, length 161 |
| Retained completion rules, all verified | 233 |
| Signed auxiliary equations, all verified | 20 |
| Largest stored rule proof | 267 factors |
| Queued / processed rule-pair jobs | 4,000 / 0 |
| Offsets examined / compatible overlap placements | 0 / 0 |
| Submitted overlap equations / oversized placements | 0 / 0 |
| Largest equation presented before stop | length 161 |
| Shared search wall | 0.851466411 s |
| Supervised worker wall | 1.031097 s |
| Worker CPU user / system | 0.984814 / 0.035252 s |
| Peak worker RSS | 15,728 KiB |
| Stdout / stderr | 194,135 / 0 bytes |
| Process return / termination / cleanup | 0 / completed / verified |

All twenty power-stage equations were input power normalizations; no new
Euclidean or inversion/centrality power was found. Its target output was
unresolved. A certificate-only cyclic-reduction audit of all 233 retained
equations likewise finds only the pure a-power a^28 (rule 51), even allowing
free conjugation. No second recorded exponent is available for a post-run
Bezout certificate. There were no additional pure a powers to combine with a^28.

The completion retained twelve cancellation rules, ten signed existing
certificates, twenty centrality equations and 191 equations from input
seeding. Q217 failed while building/simplifying an equation, before it was
accepted. The remaining input rows were exactly Q217,...,Q224. The streamed
trace contains no rejected oversized proof, so its exact attempted factor
count and individual rewrite path are **not recorded**. A reduction can
accumulate more than 2,000 factors even though each stored rule uses at most
267. The flat representation concatenates a rule's expanded product for
every application; it does not share repeated subproofs. The fourteen-factor
b1 centrality certificate is a plausible contributor, but no per-rule cost
profile was recorded, and we did not rerun the simplification to infer one.

The rule-pair queue cap was also marked as reached while seeding. It limits
which future jobs are retained; **no queued job was processed** because the
proof cap stopped the run first. Zero overlap placements is the actual
separately measured count, not a substitution of the 4,000 rule-pair count.
The existing completion core's effectiveness on this full input therefore
has not been tested beyond initialization. The five-second allowance, memory,
CPU, output size, word-length cap and 256-rule cap were not the terminating
limits. Remaining time was not used for another attempt.

[The independent checker](../scripts/check-a4-experiment.py) imports no search
or algebra compiler. It reconstructs the fixed Q, verifies all twenty power
normalizations, all twenty auxiliary equations and all 233 retained completion
rules directly by free cancellation, checks orientation and index/limit
accounting, and verifies existing positive products. It also classifies any
streamed equation literally equal to an original target; no new such target
was present. No additional goal search occurs during that classification.
The final [certificate-only replay](../scripts/replay-a4-record.py) also
checks static power decompositions, linear witnesses, gates, plan and source
snapshots. Raw logs, exact input, certificates and resource measurements are
in [the experiment directory](../benchmarks/results/prime7-a4-1-2026-10-28/).

## 5. Consequences and next research decision

R7 was **not certified**. No additional original relator follows from new
verified unit rows, since none was obtained. The independently checked linear
rank remains 17, with certified originals **R3,R5,R9,R12,R15**. The unresolved
originals are

    1,2,4,6,7,8,10,11,13,14,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32.

If e7 alone is eventually added, its new seventh coordinate cannot by itself
make another individual e_j belong to the existing row span: all old rows
have zero seventh coordinate. This conditional observation is not counted
as a result of the present experiment. The six corrected b0 classes retain
their membership/kernel status; spanning remains conditional on a proof that
the twelve words span A. No nonmembership, lower bound, independence,
nontriviality, exact H2 dimension or new arithmetic homology theorem is claimed.

The **mathematical obstacle** is still a missing identity coupling the mixed
b/unit relations to the central element a^4. Centrality and a^28 do not supply
that identity, and the old linear witnesses contain no R7 coordinate.
The **observed algorithmic obstacle** is earlier: expanded proof accumulation
stops input initialization before the proposed completion can investigate it.
Neither the toy successes nor this unfinished initialization justify a claim
that the true word problem is inaccessible or that generic completion fails.

**Single recommended next experiment, not executed:** keep R7 as the target
and run a bounded completion-only continuation from the saved 233 independently
checked rules. Load the eight remaining Q217–Q224 words as **unsimplified,
one-factor rules Q_i -> 1**, without repeating the input normalization that
hit the proof cap. Their lengths are at most 462, so they fit the existing
512-word bound; 233+8=241 rules fit the existing 256-rule ceiling. These raw
rules have immediate original-Q certificates, with no accumulated reduction
proof needed for loading. All original input constraints remain available.

Freeze an explicit selection/order of at most 4,000 rule-pair jobs from this
checkpoint, including relevant jobs involving the long-power rules; do not
silently let queue truncation exclude every late-added rule. Retain the same
5-second, 512 MiB and other bounds and count overlap placements. This would
finally test whether certified critical equations can supply a missing a
power. Every checkpoint and raw rule has an original-Q product. Any incomplete
result still remains unresolved. This proposed continuation needs separate
authorization and a checked checkpoint loader/job selection, not another
general rewriting engine; neither was implemented or run here.

A pivot to proof-producing KBMAG is premature on this evidence: no critical
work was reached, so its search performance has not been compared. If actual
critical processing then demonstrates a C-level rewriting need, KBMAG with
shared proof provenance and an independent verifier is justified. If flat
proof storage continues to dominate, a checked shared proof DAG may address
that representation issue. Neither infrastructure project should displace
the immediate milestone of one new verified original target.

## 6. Reproduction and preservation

Replay only, **without arithmetic discovery**:

```sh
python3 scripts/replay-a4-record.py \
  --base benchmarks/results/prime7-a4-1-2026-10-28
python3 scripts/check-relation-span-certificate.py \
  benchmarks/results/prime7-a4-1-2026-10-28/verified-products.json
```

The one authorized search has been consumed; do not relaunch its controller
or treat a new output directory as permission for another search. The frozen
pre-launch plan and source snapshots remain unchanged. All original GAP
algorithms, presentations, publications, historical results and prior
certificates are preserved. Only new experiments, tests, evidence and
research documentation are committed on codex-development; main is untouched.

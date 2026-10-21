# A quick, verifiable baseline before expensive research runs

The current task excludes full Anton-family computations: some original
runs took days. `Algorithms.g`, `Library-of-groups.g`, and the original
notebook, HTML, and result images remain unchanged. No algorithmic speedup
is claimed by this benchmark infrastructure.

## Which inputs are inexpensive?

Use toy cyclic/product groups in `tests/smoke.g`, first-homology calculations
from the stored presentations, and three explicitly checked small finite
presentations. The legacy runner keys are names, not mathematical proofs:

| Runner key | Verified stored group | Order | Identification status |
| --- | --- | --- | --- |
| SL2F2 | SL(2,2), isomorphic to S3 | 6 | GAP verifies a bijective isomorphism to the matrix group |
| SL2F3 | SL(2,3) | 24 | GAP verifies a bijective isomorphism to the matrix group |
| SL2F5 | C5 | 5 | **Confirmed label defect:** not SL(2,5), which has order 120 and trivial abelianization |

For the last case the stored relators say `(ab)^2=a^3` and `a^3=b`.
Substitution gives `a^8=a^3`, hence `a^5=1`; conversely a generator of C5,
with `b=a^3`, satisfies both relators. This proves the identification without
relying only on matching invariants. GAP also checks it is cyclic of order 5.
The original presentation and archived values are preserved for investigation.
Reproducing its values verifies C5 computations, not results for SL(2,5).
The affected input is `Free5/R5`; the arithmetic case `G5` uses the distinct
presentation `F5/k5`.
The [provenance and impact report](PRESENTATION-PROVENANCE.md) traces the Git
history and distinguishes an incorrect equality from a merely loose upper
bound. Its paper-specific dependency verdict remains pending source access.

`G3/G5/G7/G11` are the arithmetic-family labels; the digit in a label and the
coefficient prime are different inputs. These cases, and the infinite-group
table cases, are excluded from end-to-end H2 runs in the quick harness.
The stored G11 presentation still requires its own source/provenance audit.

## Environment and quick checks

The prepared environment has GAP 4.14.0 and compiled KBMAG 1.6.1 (commit
`82d1c1bea633485d2415df73b6d93ddddb97f721`). GAP's core handles the other
operations; no HAP or extra package is needed for the present algorithms.
Python 3's standard library supports the Linux benchmark harness. `strace`
is optional for process traces. GNU time was installed locally as an optional
helper, but this harness uses Linux `wait4` directly and does not require it.
See [the dependency guide](REPRODUCING.md) for GAP/KBMAG installation details.

In the prepared cloud environment:

```sh
export PATH=/workspace/.local/bin:$PATH
cd /workspace/generators-group-homology
timeout --kill-after=2 5 gap -q -b --quitonbreak tests/smoke.g
timeout --kill-after=2 5 gap -q -b --quitonbreak tests/historical-h1.g
timeout --kill-after=2 5 gap -q -b --quitonbreak tests/presentation-sanity.g
python -m unittest discover -s tests -p 'test_benchmark.py' -v
```

The first file has 16 known-answer smoke checks. The second reproduces all
36 archived H1 entries for the **stored presentations**, with no assertion
that every archived group label is correct. The third verifies the finite
identifications above and preserves the known case-5 mismatch explicitly.
Python tests exercise subprocess failure, timeout/descendant cleanup, and
the guard preventing accidental expensive H2 execution.

## Recorded results and runtimes

The committed evidence is in [the baseline data directory](../benchmarks/results/2026-10-21/README.md):
78 invocations from source commit `86a99c67d612e2664657778a94b027376da3fec7`, all normally completed within
the five-second per-invocation limits. These comprise 36 uninstrumented
small H2 replays, 18 diagnostic H2 runs, and 24 cheap component runs. No
unexpected solver errors, timeouts, or nonconfluent systems occurred in this
recorded batch. Intentional failure/timeout fixtures are separate harness tests.

All 16 smoke checks, 36 historical H1 comparisons, presentation sanity checks,
and six Python harness tests pass. Exact raw outputs, all individual recorded
durations, CPU/RSS observations, profiles, and traces are archived. Times below
are rounded medians of three fresh processes, including GAP startup. Linux
process polling adds up to roughly 50 ms of observation latency; GAP stage
times have millisecond granularity, so zero does not mean no work. The machine
exposes five CPUs, a four-CPU quota, and 32 GiB memory. These are cloud
measurements, not portable performance guarantees or evidence of small speedups.

| Stored case | Coefficient prime | H2 result for stored group | Median wall seconds | Observed wall range, seconds |
| --- | --- | --- | --- | --- |
| SL2F2 | 2 | 1 | 0.720 | 0.669–0.771 |
| SL2F2 | 3 | 0 | 0.718 | 0.718–0.721 |
| SL2F2 | 5 | 0 | 0.720 | 0.719–0.723 |
| SL2F2 | 7 | 0 | 0.721 | 0.720–0.725 |
| SL2F3 | 2 | 0 | 0.719 | 0.719–0.773 |
| SL2F3 | 3 | 1 | 0.772 | 0.772–0.774 |
| SL2F3 | 5 | 0 | 0.772 | 0.772–0.874 |
| SL2F3 | 7 | 0 | 0.771 | 0.721–0.821 |
| SL2F5 | 2 | 0 | 0.824 | 0.773–0.825 |
| SL2F5 | 3 | 0 | 0.822 | 0.774–0.828 |
| SL2F5 | 5 | 1 | 0.928 | 0.825–0.931 |
| SL2F5 | 7 | 0 | 0.773 | 0.719–0.825 |

The positive bounds are 1 and the corresponding Tor term is also 1, giving
a matching lower bound by the universal coefficient theorem. The zero bounds
are exact by nonnegativity. Thus these pin down H2 dimensions for the **stored
groups**, with the case-5 identification caveat above. At coefficient primes
11 and 13 all six additional small-case results are zero; their group orders
are coprime to those primes, consistent with the independent finite-group
transfer argument. This extends coefficient checks only, not the arithmetic
family of presentations.

The 18 separate diagnostic runs observe 42 confluent systems, zero
nonconfluent systems, and 42 traced `kbprog` processes exiting with status 0.
For example, `SL2F3` at coefficient 3 has two external exec-to-exit intervals
of 0.004953 and 0.005327 seconds; GAP profiles the unchanged H2 call at 4 ms
of GAP CPU. These are different measurements, not times to add or substitute
for each other. They show the small case is quick, not where a day-scale
arithmetic run spends its time. No internal-C hotspot profile was collected.

### Arithmetic components, without completion

Each component suite has three repeats per stored case. The scalar values
are `a=Tor`, `b` and `c` from the original H2 formula. The survivor count `e`
is **not computed**, so the displayed expression is a formula, not an H2 answer.

| Stored case / coefficient | a,b,c | Formula still requiring e | Median CPU ms for a,b,c |
| --- | --- | --- | --- |
| G3 / 3 | 0, 0, 8 | e − 8 | 0, 1, 1 |
| G5 / 5 | 0, 0, 11 | e − 11 | 1, 1, 1 |
| G7 / 7 | 0, 0, 14 | e − 14 | 1, 2, 3 |
| G11 / 11 | 0, 0, 19 | e − 19 | 2, 7, 8 |

| Stored case | First-test relations / word length | Median CPU ms: relation lists / quotient / constructor / serialization | Median full invocation wall seconds |
| --- | --- | --- | --- |
| G3 | 209 / 2541 | 0 / 0 / 2 / 3 | 0.719 |
| G5 | 506 / 7999 | 1 / 0 / 6 / 11 | 0.773 |
| G7 | 1023 / 19031 | 2 / 0 / 11 / 28 | 0.824 |
| G11 | 2705 / 90577 | 4 / 0 / 38 / 110 | 0.924 |

This establishes that these particular scalar and first-input setup stages
are inexpensive on this machine. Static analysis identifies repeated
Knuth–Bendix completion and potential equation/overlap growth as the expensive
research targets, but the day-scale completion itself was deliberately not
profiled or run. No overall speedup percentage can be inferred from these
component measurements.

## Measured-run commands

Each output directory must be new. All examples below use short per-process
timeouts and write outside the checkout. The harness serializes jobs within
each suite; run suites sequentially when comparing timings.

```sh
# Three replays of each of 12 inexpensive historical H2 inputs.
python benchmarks/run.py --suite small --repeat 3 --timeout 5 \
  --output /tmp/homology-small

# Separate diagnostic runs: GAP profiling, KBMAG confluence messages, and
# exec-to-exit intervals for external C programs. These add overhead.
python benchmarks/run.py --suite small --diagnostics --trace --timeout 5 \
  --output /tmp/homology-diagnostics

# Additional COEFFICIENT primes for the same small stored groups.
python benchmarks/run.py --suite extra-primes --diagnostics --trace --timeout 5 \
  --output /tmp/homology-extra-coefficients

# Cheap scalar stages on the arithmetic presentations, including G11 as stored.
python benchmarks/run.py --suite arithmetic-components --task abelian \
  --repeat 3 --timeout 5 --output /tmp/homology-abelian

# Construct and serialize only the FIRST candidate's rewriting input.
# No MakeConfluent, KnuthBendix, FindBasis, or H2 call is executed.
python benchmarks/run.py --suite arithmetic-components --task construction \
  --repeat 3 --timeout 5 --output /tmp/homology-construction
```

Use `--gap /absolute/path/to/gap` or `GAP_BIN` when needed. `--case` and
`--prime` select one input instead of a suite. The H2 whitelist is enforced
in both Python and the GAP test driver; the legacy shell runner has the same
restriction. Each invocation is capped at 30 seconds, defaults to five,
and records a timeout as **unfinished**, never as a dimension or failure of
a mathematical conjecture. The larger equation-cap variant remains available
only on the small whitelist for testing that execution path.

## What the measurements mean

Each suite stores its arguments, source hashes, source snapshots, versions,
platform/resource limits, per-run raw output, and JSON results. A trace, when
requested, records process creation, executable names, waits, and exits.
The GAP profiler changes no function definitions or mathematical options.
Setting `InfoRWS=1` exposes completion status and changes diagnostic verbosity;
diagnostic runs must not be treated as uninstrumented timing samples.

- Wall time includes fresh GAP startup; very small calls are dominated by it.
- `wait4` CPU covers the command and waited-for descendants. A Linux child
  subreaper adopts and reaps orphaned descendants after termination, so killed
  KBMAG children do not continue running or remain unreaped by the harness.
- Reported `ru_maxrss` is a maximum resident-set measure, not a sum of all
  concurrent memory. Sampled group RSS may count shared pages multiple times.
- Process sampling occurs about every 50 ms and can miss short-lived children.
- GAP function profile times are CPU milliseconds for GAP code, not elapsed
  external KBMAG time. Nested self/child rows must not be added together.
- `strace` exec-to-exit intervals include scheduling and I/O and add overhead;
  they are not a profile of internal C functions or of overlap generation.
- `null` confluence counts mean diagnostics were not requested; they do not
  mean that no system completed. An explicit nonconfluent result would still
  be incomplete evidence for a nonidentity test, not a negative theorem result.

All current H2 calls use every defining relator as the initial candidate list.
This preserves the spanning assumption needed for a sound upper bound. For
the three small stored groups, the positive bounds can also be matched by
the Tor lower bound from H1; zero bounds are exact by nonnegativity. This
does not provide explicit H2 cycles or independently checked proof certificates.

## Expensive cases: current boundary

The original repository contains no full arithmetic H2 experiment transcript,
candidate-order record, saved rewriting systems, or runtime/version log. The
earlier brief timeout probes are documented as such in the older review.
After the clarification about day-scale computations, the broader sweep was
cancelled before it returned a completed result. It is not part of this
baseline. No full arithmetic completion is attempted for this task.

Only scalar algebra and first-candidate input construction are benchmarked
for the arithmetic presentations. They give no arithmetic H2 dimension or
bound: the survivor count remains uncomputed. The G11 provenance issue also
prevents identifying its stored output with the intended arithmetic group.

## Efficiency work to propose separately

The [prioritized optimization plan](OPTIMIZATION-PLAN.md) develops explicit
small-test gates, including early stopping when upper and lower homology
bounds meet and sufficient linear certificates before word completion.

Static analysis locates the repeated completion calls in `FindBasis` and
`Reduce_Word`. Each candidate rebuilds a quotient and invokes KBMAG again.
Large derived presentations and overlap growth, rather than the cheap scalar
formula alone, are the main targets for investigation. Small-group profiles
cannot establish the distribution of time in a multi-day run, and no such
distribution or speedup factor is asserted here.
KBMAG was already compiled with `-O2 -g`; compiler tuning alone is not an
established route to eliminating the day-scale search cost.

1. Record effective options, confluence and candidate-level resources before
   tuning. The existing `tindyint` spelling is ignored by KBMAG; a separate
   change to `tidyint` needs controlled comparison, as it can help or hurt.
2. Benchmark certified Tietze elimination of the explicit `b_i` and `w`
   definitions in G3/G5/G7. For G7, eliminating those eight definitions would
   reduce 14 generators/64 relators to 6/56 before further simplification.
   The first-test relation count would drop from 1023 to 447. This is a
   **symbolic input-count estimate**, not a measured runtime improvement;
   substituted word lengths can grow. Do not apply it to G11 without its
   missing-definition/provenance issue being resolved.
3. Cache prime-independent exponent/Smith data and static relation inputs.
   This reduces overhead, but millisecond-scale scalar work alone cannot
   explain or remove days of completion time.
4. Benchmark candidate/generator order and supported completion parameters
   with fixed resource limits and soundness checks. A different heuristic
   trajectory can change completion drastically; increasing caps alone is
   not a demonstrated solution.
5. Investigate reuse only with explicit relation support. Successive candidate
   tests remove and add relations; rules from a stronger quotient are not
   valid automatically in a weaker one. A single shared completed system
   is not a drop-in optimization. A fixed central-extension completion plus
   vector-space calculations is a research experiment that may itself be
   much harder than the smaller quotients.
6. Parallelize independent parameter/case trials first. Greedy eliminations
   within one `FindBasis` call are dependent, so concurrent deletion decisions
   need a proof before they can be combined.

These preserve the intended mathematical approach only when their equivalence
maps, candidate coverage and reduction soundness are established. None is
implemented in `Algorithms.g` here. Adding coefficient primes to a fixed small
group is already possible; reaching new arithmetic-family primes also requires
a verified presentation generator and theorem hypotheses. Small-case success
does not establish feasibility or novelty for those new arithmetic groups.

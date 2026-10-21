# Dependencies and reproducing computations

Run commands from the repository root. Use the existing checkout on the
development branch; `main` and the original research artifacts are unchanged.

## Runtime and installation

| Component | Role | Status in this review |
| --- | --- | --- |
| GAP | Free/fp groups, abelian invariants, Tietze operations, p-adic valuations | GAP 4.14.0 tested; original runtime version not recorded |
| KBMAG | External Knuth–Bendix executables and GAP interface | KBMAG 1.6.1, upstream commit `82d1c1bea633485d2415df73b6d93ddddb97f721` tested |
| C compiler and make | Compile KBMAG's external programs | Required for a source installation, not every run |
| Bash, GNU coreutils `timeout`, Git | Bounded runner and source provenance | Tested on Debian 13, x86_64 |
| GNU time | Optional precise wall-time / maximum-resident-set log | Set `TIME_BIN` for a nonstandard path; otherwise the runner reports approximate elapsed seconds and unavailable memory |
| GAPDoc | GAP help/documentation infrastructure | Installed, version 1.6.7; no other GAP package required by KBMAG's package metadata |
| Python/Jupyter/nbconvert | Optional regeneration of the introductory notebook's HTML | Not needed for mathematical computations; regeneration not run |
| HAP and other homology packages | Potential independent validation | Optional future work, not installed or used by the algorithms |

`LoadPackage("kbmag")` is the only explicit package dependency in
`Algorithms.g`. `PadicValuation`, `AbelianInvariants`, `PresentationViaCosetTable`,
and the simplification routines used here come from GAP core. KBMAG's metadata
requires GAP >= 4.7 and lists no other needed GAP packages; that is a package
minimum, not evidence that this project was tested across all such releases.
Loading GAP code alone is insufficient: KBMAG's compiled `kbprog` and related
executables must exist and be runnable in GAP's package-program directory.

For a new installation, use a GAP distribution with KBMAG included and built,
or install GAP and follow the [KBMAG installation instructions](https://github.com/gap-packages/kbmag#installation).
In the installed KBMAG source directory the build is:

```sh
./configure /path/to/gap-root
make -j2
```

Keep package signature, checksum, and TLS verification enabled. The original
repository has no installer, dependency lockfile, CI workflow, or version pins.
For this review the cloud setup installed Debian's GAP 4.14.0-3 packages under
`/workspace/.local/gap`, verified through signed Debian package indexes, and
built the pinned KBMAG commit there. No administrator privileges were needed.
The cloud environment's saved installation instructions reproduce that setup;
its helper script is also retained at `/workspace/.setup/install-homology.sh`.
Those absolute paths describe this prepared environment, not requirements of
the research code or files distributed by this repository.

In this cloud environment:

```sh
export PATH=/workspace/.local/bin:$PATH
cd /workspace/generators-group-homology
```

The wrapper sets the relocated GAP library and shared-library paths. In other
environments use the normal installed `gap`. No database, web server, API key,
or network service is required for computations once dependencies are installed.

## Fast validation

```sh
gap -q -b --quitonbreak tests/smoke.g
gap -q -b --quitonbreak tests/historical-h1.g
```

The smoke file performs 16 checks: free versus torsion contributions in
`C9 x Z`, valuations versus dimensions, identity and nonidentity reductions,
the relation quotient for `C3`, H2 over two coefficient primes, the large
variant on a tiny input, `C2 x C2`, and both presentation helpers. Known H2
values come from cyclic-group homology and the product/UCT formulas, not
snapshots copied from this implementation. The second test compares all 36
H1 entries in `undergrad-research/Capture2.JPG` against literal expected values.
These tests fail with GAP errors; `--quitonbreak` propagates failures to the
shell rather than leaving an interactive break loop.

They validate a small baseline; they do not certify all rewriting runs,
arithmetic presentation identities, or the historical H2 table.

## Inventory and original evidence

| Artifact | What it supplies | What it does not supply |
| --- | --- | --- |
| `Algorithms.g` | Generic routines and larger equation-cap variants | Driver scripts, saved systems, per-run parameters or logs |
| `Library-of-groups.g` | Presentations, sample finite groups, and a `G7` commutator list | Calls of the homology routines or certificates for candidate subsets |
| `undergrad-research/Capture2.JPG` | H1 and H2 tables for nine groups at coefficient primes 2,3,5,7 | Machine-readable inputs, runtimes, versions, candidate order, or confluence status |
| `undergrad-research/Capture.JPG` | The arithmetic H2 expression motivating the project | A numerical result or runnable experiment |
| Notebook and HTML | Introductory exposition and GAP session examples | Homology experiment notebooks; the only notebook code cell invokes HTML export |
| Original README | Links to the Anton and Roberts papers | Complete experimental transcripts |

Exact historical execution cannot be recovered solely from this checkout.
In particular, a table's sharper bound may have used a different presentation,
a certified smaller spanning list, a different candidate order, or more
completion time. Do not infer any of these undocumented choices as fact.
The runner below is an explicit reconstruction using the checked-in words
and **all** defining relators, rather than a recovered author script.

## Selecting a presentation

| Runner key | Free group / relator list | Library group |
| --- | --- | --- |
| `G3`, `G5`, `G7`, `G11` | `F3/k3`, `F5/k5`, `F7/k7`, `F11/k11` | Arithmetic cases labeled by presentation prime; see G11 caveat below |
| `GL2Z` | `Free6`, `R6` | `GL_2Z` |
| `SL2Z` | `S`, `rels` | `SL2` or `SL_2` |
| `SL2F2` | `Free0`, `R0` | `SL_2Z_2` |
| `SL2F3` | `Free3`, `R3` | `SL_2Z_3` |
| `SL2F5` | `Free5`, `R5` | `SL_2Z_5` |
| `SL2Zi` | `Free8`, `R8` | `SL_2Zi` |
| `SL2w` | `Free1`, `R1` | `SL_2w` (the printed banner incorrectly says `SL_2Zw`) |
| `SL2Zneg5` | `Free9`, `R9` | `SL_2Zneg5` |
| `PSL2Z` | `Free7`, `R7` | `PSL_2Z` |

`A5` and `S5` are permutation groups; obtain inputs with
`P := PresentationOfFiniteGroup(A5);` and use `P[2]`, `P[3]`.
For the fp simplification helper instead use fields 3 and 4, and retain its
field-1 isomorphism. Simplified presentations change experimental provenance.

## Bounded H2 reconstruction

```sh
# Historical table example: coefficient field F3, presentation SL_2(F3).
bash scripts/reproduce-h2.sh SL2F3 3 120

# Arithmetic family label and coefficient prime are separate inputs.
bash scripts/reproduce-h2.sh G3 3 120

# Explicitly select the existing large equation-cap variant.
bash scripts/reproduce-h2.sh SL2F3 3 120 large
```

Set `GAP_BIN=/absolute/path/to/gap` if needed. `PRIME` must be a prime;
GAP checks primality. `SECONDS` limits each complete GAP invocation, including
startup. A run gets a unique directory under `${TMPDIR:-/tmp}` containing:

- `metadata.txt`: source commit, original code/presentation object hashes,
  working-tree status, case, prime, mode, time limit, and UTC timestamp.
- `output.log`: library banner, GAP/KBMAG versions, presentation sizes,
  abelianization, upper bound, surviving words, and candidate reductions.
- `resources.txt`: elapsed wall time and maximum resident set reported by
  GNU time for the invocation and waited-for children; this is not a sum
  of simultaneous process memory usage. Without GNU time, it records elapsed
  whole seconds and explicitly marks memory as unavailable.
- `exit-status.txt`: preserved command status; 0 means normal completion,
  124 means timeout, and other nonzero statuses indicate failure or termination.

The limit sends TERM and escalates to KILL after five further seconds if
needed. An externally killed command can report a signal-derived status.
Logs remain outside the checkout; retain them with experiment records before
temporary storage is cleared. GAP's printed `Runtime()` is not a reliable
measure of external KBMAG CPU time; use the wall-time record for comparisons.
Completion does not certify confluence: the original routine hides it.

For manual use, the corresponding unchanged call is:

```gap
Read("Algorithms.g");;
Read("Library-of-groups.g");;
answer := SecondHomologyCoefficients(Free3,R3,3,R3);
# [remaining relation words, upper bound, reductions in initial order]
```

Using `S=L` ensures the initial candidate images span the relation quotient.
Do not replace the last argument by an arbitrary short list or the library's
global `comm` without establishing the spanning requirement.

To reconstruct all second-table inputs (potentially expensive):

```sh
for name in GL2Z SL2Z SL2F2 SL2F3 SL2F5 SL2Zi SL2w SL2Zneg5 PSL2Z; do
  for prime in 2 3 5 7; do
    if bash scripts/reproduce-h2.sh "$name" "$prime" 120; then
      :
    else
      status=$?
      echo "Unfinished/failed: $name at $prime, status $status" >&2
    fi
  done
done
```

This 120-second matrix is an instruction, not a claim that all runs completed.
The measured shorter audit is recorded in [the review](RESEARCH-REVIEW.md).

## Protecting the research record

Keep the original `.g` files, notebook, HTML, and images unchanged. Save new
logs separately with input words and version information. A new smaller
upper bound is a new observation, not permission to replace the historical
table. Timeouts, nonconfluent outcomes, exceptions, and normal completions
must be reported separately. Full arithmetic H2 reproduction remains open,
and `G11` needs presentation provenance review before interpreting it as the
intended arithmetic group.

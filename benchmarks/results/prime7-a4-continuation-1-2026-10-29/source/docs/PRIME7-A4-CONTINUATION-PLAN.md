# One R7 checkpoint continuation: frozen before launch

Sole target: original R7=a^4. Base: commit 515b306, original 236-row fixed Q.
The saved 233 rules are preserved verbatim. Q217–Q224 are added as raw rules
Q_i -> empty, with singleton products Q_i in their **original** indices.
There are 241 rules. No raw R7 is added. No input normalization is performed.

The loader is verified in both directions: 241 rule products in original Q,
and 236 products of loaded-rule discrepancies for the original Q words.
The latter reconstruct known seeding identities, not new goal searches.
The largest reverse product has 44 factors. Independent free cancellation
establishes equality of the two normal closures in the SAME free group.
A load-only engine roundtrip checks the actual installed rules and job order
against those verified arrays, without calling arithmetic completion.

Exact input and schedule: `benchmarks/results/prime7-a4-continuation-1-2026-10-29/preparation/`.
There are exactly 4,000 distinct unordered rule-pair jobs; rule IDs are zero-based.
The first eight jobs are (22,233),(23,234),(23,235),(29,236),(32,237),(36,238),
(24,239),(22,240). Thus each new long-power rule has a job at the start.
Partners are chosen by static left-side compatibility, preferring non-cancellation
rules, shorter left sides, more a letters, then rule ID. No critical equation
is generated or normalized during schedule preparation.

Additional long-power jobs are selected round-robin, with up to 64 distinct
compatible checkpoint partners per long row. After the first eight jobs,
these are interleaved with target-letter/short-length-prioritized matched
checkpoint pairs; remaining slots are filled from that checkpoint list.
Q217–Q224 occur in respectively **58,34,35,37,23,22,52,64** selected jobs
(325 of the 4,000 jobs). The complete ordered list and selection description
are frozen in schedule.json and hashed before launch. No jobs involving new
rules are added: new certified equations can simplify subsequent frozen jobs,
but the fixed list is incomplete and cannot establish nonmembership.

Discovery: one engine, one shared five-second alarm and deadline. Loading the
verified rules, installing the queue, initial a^4 reduction, all critical jobs,
checkpoints and final target reduction share that budget. Critical pair jobs
started/completed, offsets tested, compatible overlap placements, submitted
critical equations and oversized placements are reported separately.

Limits: hard AS 512 MiB, CPU 6 s, external wall 10 s, output per file 8 MiB;
completion rules 256; cumulative queued jobs 4,000; word/overlap 512; proof
factors 2,000; reduction steps per call 2,000. No increased cap, fresh input
normalization, another target, retry or follow-up experiment is allowed.
Literal AS/CPU/FSIZE limits are checked by the worker before discovery.

Before launch: repeat eight OS safety probes, the existing certificate suite,
saved-checkpoint replay, bidirectional coverage, actual loader roundtrip,
small x^2/x^3 certified completion, and adversarial loader/certificate tests.
Abort on failure. An exclusive marker consumes the single authorization before
launch, even on process failure. Stream every new rule and per-job accounting.
An independent checker, importing no discovery code, checks every new product
against the original 236 Q rows and any a^4 certificate. A partial or nonconfluent
computation is unresolved, not a mathematical obstruction.

After this one experiment: **stop developing verification machinery**. Preserve
the outputs, write the concise Track A assessment, commit and update draft PR #2.
No subsequent experiment is authorized by this plan.

# MOC proof workflow

## A. Mathematics and Lean source

Work on mathematical reasoning, literature, and Lean source under `Lean/`. The
unrestricted target is `MOC.MOCIsTrue` in `Lean/MOC/Claim.lean`. Report a
restricted result by its actual statement. The unrestricted result requires a
proof of that exact target with no extra premises, admissions, or project axioms.

The same rules apply to delegated proof agents. Do not invoke Lean, Lake, build
scripts, automated repair agents, Git, or publication commands. Do not start,
stop, restart, or flush workers. Read their reports and fix the Lean source.

When a coherent change is ready for the build and publication queue, write a
uniquely named `.txt` note under `Lean/.lake/worker/intents/`. Write it after the
source edits. The first line is the commit subject. List exactly the intended
repository-relative file paths, one per subsequent line. Save through a
temporary filename in that directory and rename it to `.txt` when complete.
For example:

```text
lean: prove the complementary minor identity
Lean/MOC/Example.lean
Lean/MOC.lean
```

The default state directory is `Lean/.lake/worker/`. Use the operator's
`MOC_LEAN_WORKER_STATE` when provided. Monitor these files directly:

- `status.json` reports the latest stable draft build and links its full log.
- `candidate.json` reports the audited publication candidate and its diagnostics.
- `committed/*/receipt.json` records completed commits and their build receipts.

Match the report to the source digest or handoff under review. On a failure,
read the recorded diagnostics and log, fix the sources, and write a fresh
handoff for the corrected change. A draft build can include unlisted work.

## B. Build and diagnostics

`Code/lean-build.sh` is the operator-run build worker. It coalesces edits,
audits immutable snapshots using at most four CPUs, and shares one result per
source digest between draft and publication checks. It reads the filesystem
and writes reports. Candidates require a passing Lean build and axiom audit.

## C. Commit and publication

`Code/lean-publish.sh` is the operator-run publication worker. It exports a
base for B and consumes only B's verified receipts. It compares the receipt
with the exact proposed tree and uses A's commit subject. It authors commits
as `ascendnooshpere` and publishes fast-forward batches to
`origin/moc-verified`. It never compiles.

An operator manages workers through `Code/lean-workflow.sh`. After upgrading
the workflow, an operator must replace older workers to load the new
handoff protocol.

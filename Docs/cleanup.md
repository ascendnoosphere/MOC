# Historical folder organization

This record describes the larger source collection before the present checkout. For the current directories and runnable commands see the [repository guide](../README.md) and [reproduction guide](reproduction.md).

The earlier collection was organized by purpose:

| Path | Role |
| --- | --- |
| `docs/` | Mathematical writing, literature, and subject indexes |
| `code/` | Python sources, utilities, tests, and the local Lean project |
| `data/` | Exact inputs, retained figures, and `layout.json` |
| `archive/` | Frozen handoffs, an older export, and historical build records |
| `build/` | Disposable local run output and new exports |

## Latest cleanup

The user approved removing regenerable builds and caches. The disk-cleanup
baseline was about 5.86 GB across 37,522 files; the organized working folder is
about 540 MB across 1,681 files, roughly 91% smaller. Archive contents count as
compressed files rather than expanded trees.

- Removed the downloaded Lean/Mathlib environment, installer download, compiled
  Lean modules, and Python bytecode caches. All 45 local Lean sources and the
  pinned toolchain/Lake configuration remain.
- Preserved the mixed historical build records in
  `archive/legacy-build.tar.gz` before clearing `build/`. The snapshot contains
  3,631 files, including unique scratch code, derivations, and earlier numerical
  inputs. Its original file paths and sizes were checked before removal.
- Moved `contextdex/`, the previous `moc-results.zip`, the generation protocol,
  and `stream.txt` out of the root and into labeled archive subfolders. Frozen
  snapshots and exports retain their bytes and internal manifests.
- Added subject and code indexes. Existing paths under `docs/`, `code/`, and
  `data/` remain stable; the launcher map and historical aliases are unchanged.
- Replaced repetitive pessimistic framing in prominent project notes with
  result-first prose and specific remaining obligations. Hypotheses, theorem
  status, equations, and useful counterexamples to proposed bridges are retained.
- Corrected the old single-file Lean description to document the actual local
  project, its ten default targets, additional modules, and external source.
- Directed new package exports to `build/exports/` and added ignore rules for
  Lean artifacts, local caches, and private agent state.

## Preservation and checks

Source code, exact input data, original PDFs/text, and third-party LaTeX sources
were checked byte-for-byte during disk cleanup. Edited research notes were
compared against their pre-edit text to preserve mathematical expressions.
The original PDF/text manifest still covers 77 original paths as 59 distinct
PDFs, totaling 4,287 pages, with separate descriptions for three textless diagrams.

The seven launcher tests pass. The 734-record source map still resolves to
existing files and retained prerequisites. New navigation links and the
notes-and-data packaging command were checked. Research experiments and Lean
compilation were not rerun for this file cleanup.

Private harness state and hidden service directories were left untouched.
Unabridged originals remain separate from edited project prose. The earlier
curation and restoration history predates this cleanup; this pass preserves the
mathematical records present at its start.

## Keeping the layout tidy

Use [the archive guide](../archive/README.md) for historical inputs and
[the execution guide](reproduction.md) for new runs. Put new source in `code/`,
notes in `docs/`, persistent exact inputs in `data/`, and generated output in
`build/`. `./pack-results.sh` produces a current notes-and-data export without
repopulating the project root.

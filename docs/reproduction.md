# Running checks

## Why there is a launcher

The original research programs assume specific filenames, sibling certificate
files, cross-bundle imports, and sometimes absolute project paths. Moving them
without an adapter would silently break those assumptions. `code/run.py` uses
`data/layout.json` to copy **only retained content** into the expected temporary
layout, runs the selected source there, and removes the temporary directory.
Identical source copies are stored once in the curated tree; the map supplies
legacy aliases when needed. Authenticated helper sources are copied byte-for-byte.
Historical hard-coded project roots were replaced by `MOC_LEGACY_ROOT`, which the
launcher sets to that disposable directory.

`requires` entries in the layout are source generators run before a verifier;
their generated JSON/report files do not need to be checked in. Their exit codes
are checked before starting the dependent script. The timeout applies separately
to each prerequisite and the requested script. On a timeout or interrupt, the
launcher terminates the process group.

## Commands

```sh
python code/run.py --list
python code/run.py --timeout 900 research/verify_sinkhorn_reduction.py
python code/run.py --output build/sinkhorn research/test_exact_sinkhorn_verifier.py
python code/run.py theorems/profile_geometry/geometry_bell3n_fast.py -- 4
python -B -m unittest discover -s code/tests -v
```

Options for the launcher must precede the source name. An optional `--` after the
source name separates arguments for that source. Saved outputs contain only new
or modified workspace files. Saving inside the project is restricted to `build/`
to avoid overwriting curated sources or input certificates.

## Dependencies and interpretation

- Python 3.10+ on a POSIX system (process-group timeout handling uses Unix APIs).
  No solver is needed by the independent rational PSD replayer.
- Scientific programs additionally use NumPy, SciPy, SymPy, and Matplotlib.
  See `requirements.txt`; figure-producing code uses a noninteractive backend.
- The [Lean directory](../code/lean/README.md) contains 45 source files and a
  local Lake project pinned to Lean 4.19.0 and a specific Mathlib revision.
  Its ten default targets cover part of the source collection; additional
  modules have their own import chains. Downloaded dependencies and compiled
  artifacts are disposable and must be rebuilt after cleanup.
- `DimensionFourMiddleSector.lean` belongs to a separate upstream environment:
  it imports `MarcusDeOliveira.ProductTensor` and `.Full.DimensionThree` from
  [marcus-de-oliveira](https://github.com/djma/marcus-de-oliveira). Those imports
  are not supplied by the local Lake project. See the Lean guide for setup
  distinctions and recorded checking status.
- Some files are import-only algebra libraries and are intentionally absent from
  `--list`; executing such a file is not a meaningful verification test.
- Preserve assertion checks: the launcher rejects `-O`/`-OO` and clears inherited
  `PYTHONOPTIMIZE` for child processes.

A successful run checks the identity, family, or finite input declared by that
program. Numerical construction helpers produce candidates for their
corresponding exact verifiers.

## Standalone experiments and archived inputs

The launcher lists mapped historical entrypoints, not every source file. Later
experiments in `code/research/` use their own commands and may read prior
JSON/JSONL/NPZ records from `build/`. Those mixed historical records are preserved
in the [build snapshot](../archive/README.md); mapped launcher entrypoints do not
require restoring that snapshot. See the [code index](../code/README.md) for
standalone-script and optional-dependency guidance.

New output belongs in `build/`. `./pack-results.sh` creates a notes-and-data
export at `build/exports/moc-results.zip`, or at an explicitly supplied path.

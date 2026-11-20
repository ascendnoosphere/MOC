# Reproducing the research report

Run these commands from the repository root with Python 3.10 or later and assertions enabled. Keep `PYTHONOPTIMIZE` unset. Section 10 of [the report](MOC_progress.pdf) also gives commands from inside [Code/](../Code/).

## Python checks

The Hermitian certificate, boundary chain and spectral-neighborhood checks use the standard library.

```sh
python3 -B Code/moc4_hermitian_certificate.py
python3 -B Code/verify_cone82.py
python3 -B Code/verify_moc4_open_spectra.py
```

Install SymPy in the active Python environment for the remaining checks.

```sh
python3 -B Code/verify_rank_sum_six.py
python3 -B Code/verify_local_pole.py
python3 -B Code/verify_singleton_obstruction.py
python3 -B Code/spin/check_coverage.py
python3 -B Code/verify_regular_pencil.py
```

The spin-three-halves and non-spin symplectic certificates compile the C++ evaluator into a temporary directory. They need g++, OpenMP and GMP C++ development headers and libraries. The separate spin profile verifier also covers selected five-dimensional families.

```sh
OMP_NUM_THREADS=2 python3 -B Code/spin/verify_scalar.py
OMP_NUM_THREADS=2 python3 -B Code/verify_symplectic_case.py
python3 -B Code/spin/verify_spin_moc.py
```

## Independent facet enumeration and report build

Compile the C++17 audit with assertions enabled. It enumerates all 14-subsets and 13-subsets to recover 82 facets.

```sh
out=$(mktemp -d)
g++ -O3 -std=c++17 Code/audit_82_exact.cpp -o "$out/audit82"
"$out/audit82"
```

Build the [LaTeX source](MOC_progress.tex) with latexmk, pdfLaTeX and the packages imported by the report. The output directory keeps the checked-in PDF available for comparison.

```sh
out=$(mktemp -d)
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir="$out" Docs/MOC_progress.tex
```

Build the conic reduction with the same toolchain and a separate output directory.

```sh
out=$(mktemp -d)
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir="$out" Docs/Cases/Conics.tex
```

The [case report](Cases/Cases.pdf) compiles the index and the four Markdown proof files. From the repository root, run:

```sh
cd Docs/Cases
out=$(mktemp -d)
pandoc --from=markdown+tex_math_single_backslash --toc --pdf-engine=pdflatex \
  -V geometry:margin=0.85in -V fontsize=11pt -V papersize=letter \
  -M 'title=Determinant certificates and reductions in order four' \
  README.md Blocks.md Spectra.md Symplectic.md Regular.md -o "$out/Cases.pdf"
```

## Lean proofs

The pinned project under [Lean/](../Lean/README.md) checks the spectral formulation and several literature and repository results. Build it from the repository root with `cd Lean && lake build`.

## Historical reproduction instructions

Some research notes refer to a larger collection with a `code/run.py` launcher, `code/tests/`, scientific packages, a Lean project and archived build outputs. These paths describe that historical collection. The [layout map](../data/layout.json) records its file provenance. The commands above exercise the standalone sources distributed in this repository.

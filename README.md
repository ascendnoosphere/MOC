# Marcus–de Oliveira research continuation

Start with **MOC_progress.pdf**. It gives the statements, proofs and scope. MOC_progress.tex is its LaTeX source. The results are research arguments offered for independent verification.

| Result | Proof or verification |
| --- | --- |
| Shifted rank sum at most (n+2\) | Sections 2 and 3. `verify_rank_sum_six.py` checks a six-dimensional example. |
| One order-four spectrum on a circle or line | Sections 4–6. `MOC4_Hermitian_Proof.md` gives an alternative normalization. `moc4_hermitian_certificate.py` checks all mixed inequalities. |
| Complete list of 82 facets | `verify_cone82.py` with `cone82.json` checks the oriented boundary chain. Compiling `audit_82_exact.cpp` gives an independent exhaustive check. |
| Every relative eigenbasis in a specified neighborhood of complex spectral pairs | Section 7 and `moc4_open_spectra.md`. Run `verify_moc4_open_spectra.py`. |
| Central positive weights for bundles of matrix algebras | Section 7. |
| Spin-three-halves family, all spectra | Section 8 and `spin/PROOF.md`. Run `python verify_scalar.py` and `python check_coverage.py` from the `spin` directory. |
| A fixed spectrum pair where singleton-matched scalar weights are impossible | Section 9. Run `verify_singleton_obstruction.py` to check the exact separation and the three ordinary scalar weights. |
| Three-dimensional intersection with two distinct nonzero eigenvalues on one side, or with reciprocal values on a line and repeated endpoints | `MOC_Overlap_Three_Supplement.md`. The last section treats a separate comparison hull that includes zero. |
| Generalized circles on nested reducing subspaces | `local_pole_theorem.md` and `verify_local_pole.py`. The supplement uses the difference convention. |

Use Python 3.10 or later with assertions enabled. The one-sided certificate, boundary-chain verifier and spectral-neighborhood verifier use only the standard library. The other Python checks require SymPy. The spin verifier also requires a C++17 compiler, OpenMP and GMP. The exhaustive facet verifier can be built with `g++ -O3 -std=c++17 audit_82_exact.cpp -o audit82`, then run as `./audit82`. Section 10 of the report lists the primary sources.

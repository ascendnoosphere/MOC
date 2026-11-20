# Marcus–de Oliveira research continuation

Start with the [research report](Docs/MOC_progress.pdf) for the statements, proofs and scope of the results, or read its [LaTeX source](Docs/MOC_progress.tex). For the order-four case analysis and its higher-dimensional extensions, see the [case index](Docs/Cases/README.md) or the [compiled proofs](Docs/Cases/Cases.pdf).

From the repository root, run `python3 -B Code/verify_cone82.py` to check the 82-facet boundary certificate. The [reproduction guide](Docs/reproduction.md) gives the commands for every verifier and the report build. Use Python 3.10 or later with assertions enabled. The symbolic checks use SymPy. The spin certificate also uses a C++17 compiler with OpenMP and GMP.

| Result in the report | Proof or verification |
| --- | --- |
| Shifted rank sum at most \(n+2\) | Sections 2–3 and [six-dimensional example](Code/verify_rank_sum_six.py) |
| One order-four spectrum on a circle or line | Sections 4–6, [alternative normalization](Docs/MOC4_Hermitian_Proof.md) and [mixed inequalities](Code/moc4_hermitian_certificate.py) |
| Complete list of 82 facets | [Boundary-chain verifier](Code/verify_cone82.py), [certificate](data/cone82.json) and [independent exhaustive audit](Code/audit_82_exact.cpp) |
| All relative eigenbases in a specified neighborhood of complex spectral pairs | Section 7, [proof](Docs/moc4_open_spectra.md) and [verifier](Code/verify_moc4_open_spectra.py) |
| Central positive weights for bundles of matrix algebras | Section 7 |
| Spin-three-halves family, all spectra | Section 8 and [spin certificate](Docs/spin/PROOF.md) |
| Fixed spectra obstructing singleton-matched scalar weights | Section 9 and [exact separation and three-weight certificate](Code/verify_singleton_obstruction.py) |
| Three-dimensional intersection with two distinct nonzero eigenvalues on one side, or with reciprocal values on a line and repeated endpoints | [Overlap supplement](Docs/MOC_Overlap_Three_Supplement.md), including its separate comparison hull with zero |
| Generalized circles on nested reducing subspaces | [Local pole theorem](Docs/local_pole_theorem.md) and [verifier](Code/verify_local_pole.py). The supplement uses the difference convention. |

The [document index](Docs/README.md) covers the larger research collection. [Lean formalization](Lean/README.md) gives the build and literature coverage.

## Further order-four research

The latest checkpoint includes [two certified quaternionic families](Docs/Cases/QuaternionAttack.md), [the mixed-facet reduction and its obstruction](Docs/Cases/SimplexAttack.md), and [a spectral neighborhood uniform in the fourth eigenvalue](Docs/Cases/SpectralAttack.md). The [two-eigenvalue hull](Docs/Cases/ExtremaAttack.md), [pencil experiments](Docs/Cases/PencilAttack.md), [centrally symmetric pairs](Docs/Cases/PairedAttack.md), and [first-jet calculations](Docs/Cases/JetExperiments.md) record the remaining tests and the scope of the numerical evidence. Unrestricted order-four MOC remains unresolved in this work.

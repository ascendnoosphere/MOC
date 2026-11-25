# Research agenda: spectral certificates, transport cuts, and Cayley search

## Symbolic Lean result

`TransportGapCertificate.lean` proves `MOC.projected_partialMatchingGap_certificate`.
An identity on permutation gap labels transfers to an exact identity on
squared minors. A nonnegative minor functional then proves the directional
determinant bound. This accepts *signed atom coefficients*; the atom terms,
nested reduced costs, and crossed reduced costs can contribute to the same
functional without one joint law on the minor table.

`transportReducedCost_nonneg_and_zero` gives the finite flow verifier and its
equality criterion. A transport score is zero exactly when every positive
flow edge has zero reduced cost. The nested wrapper checks the costs only
at the two correct subset sizes. The crossed wrapper permits independent
row and column marks. The finite shadow method behind the nested and crossed
couplings is from Russell Lyons, *Determinantal probability measures*,
[DOI 10.1007/s10240-003-0016-0](https://doi.org/10.1007/s10240-003-0016-0).

The Lean file contains no finite-data verification, heuristic search, or
arithmetic check in place of a theorem. Verified on Lean 4.19 against
repository base `821d357`.

## Bounded experiments (not Lean proofs)

Python 3. Run `python experiments.py --verify-duals` for the fixed fixtures
and independent exact certificate replay, or `python experiments.py --lp`
to rerun the search, replace its four JSON certificate files, and replay
them. The script uses NumPy and SciPy; the exact reconstruction fallback
during LP discovery uses SymPy. Solver output alone never counts as a
certificate. Seeds: 2503 (transport), 190501 (square mixers), 190505
(three-frame scalar compression). The sparse search keeps box bounds only
in discovery, not in certified duals.

| Agenda | Check | Result |
|---|---|---|
| Cycle 01 Paths 03/05 | Exact six-label separation | Signed objective −226862720 before normalization. All 252 subset moments nonnegative; 0 of 100 crossed blocks failed, 4 of 80 adjacent nested blocks failed in each orientation. Not an actual unitary mixer. |
| Cycle 01 Paths 03/05 | Exact positive certificate repair | All 120 label identities replayed with the 39 declared event terms and the one declared nested Hall cut. The cut's neighbors were reconstructed. |
| Cycle 02 Paths 03/05 | Sparse combined-cut search at orders four and five | Exact unrestricted rational duals replayed in all 13 directions for one seeded order-four pair, all 14 for a seeded order-five pair, and all 16 for the Cycle 01 pair. Six cuts were discovered for the latter. These cover the full matching polygons for those three particular pairs. |
| Cycle 02 Paths 03/05 | Sparse combined-cut search at order six | Exact unrestricted rational duals replayed in 13 of 15 tested directions for one seeded pair. Directions `(-82212,-85908)` and `(23040,-131520)` yielded numerical closure only; neither is certified. No exact negative combined-transport functional was found in these runs. |
| Cycle 02 Paths 03/13 | Exact four-term coefficient obstruction | Reconstructed the 41-denominator orthogonal matrix from its Cayley generator, checked its two unitary identities, and replayed the 24 injection labels. The actual frame gives residual −47/1681. This rejects that common coefficient law, not scalar overlap-three or MOC. |
| Cycle 02 Paths 03/13 | Actual scalar Gaussian–Cayley search | Checked 18 exact tuples and 224 axis/facet directions for square orders 4, 5, 6. Included the agenda's fixed orthogonal mixer, dense complex Gaussian-rational Cayley mixers, repeated labels and near-zero sums. No exact positive excess. |
| Cycle 02 Paths 03/13 | Scalar reciprocal overlap-three | Checked both an unaugmented 3-by-4 frame pair and a zero-augmented 4-by-4 frame pair for generic, near-coincident, and repeated spectra. No exact positive excess in their respective 28 and 39 axis/facet directions. |

The exact JSON replay independently generates matching labels, minor-event
incidences, and Hall neighbors, then checks nonnegative coefficients and
coefficient identities with rational arithmetic. The raw discovery LP may use
floating point, bounded signed permutation variables and a cut-pass limit.
The data do not establish adequacy of the full cut cone, do not resolve
the reverse independence of the two local cut classes, and do not solve
scalar overlap-three. The cited experiment totals are new bounded replays,
not a rerun of the Cycle 02 historical 60-pair experiment.

Optional reverse-independence diagnostic: `python reverse_independence.py --n 4`
(or `--n 5`) checks crossed cuts of source-family size at most three,
after fixing the marked row and column by symmetry. It tested 132 distinct
nontrivial target rows at order four and 4,676 at order five, with six
nested-cut passes allowed per target. No exact separating functional was
found. This does not establish the reverse implication.

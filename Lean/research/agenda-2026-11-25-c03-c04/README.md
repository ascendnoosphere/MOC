# Cycle 03 and Cycle 04 experiment ledger

The two submitted agendas share 15 proof paths but change their order.
This ledger uses Cycle 04 numbering; C03 gives the corresponding Cycle 03
path. It reports new work and explicit unclosed gates. A repeated fixture
or a solver result is not a proof of the conjecture.

| C04 | C03 | Checked work or bounded experiment | Remaining gate |
| --- | --- | --- | --- |
| 01 Contact transfer | 01 | [Zero-safe contact derivative and both gauges](../../MOC/ContactDifferential.lean); [nearby distinct active values at the sharp count](../../MOC/SharpContactImaginaryShifts.lean). The previous gap-free affine isolation and varying-gap cover are already unconditional. | Relative dimension for general fixed-zero strata, and contact Jacobian at higher counts. No compactification is needed for the existing transfer. |
| 02 Phase and variance cuts | 02 | [Exact reconstructions](phase/README.md) for 8,401, 32,847, and 41,056 columns, plus a new exact adaptive square; [phase contraction](../../MOC/UnitaryPhaseCuts.lean), [signed covariance](../../MOC/RankOneVariance.lean). The old 39-term plus nested Hall repair passed independent replay. | A cone complete for all realizable terminal gaps is unproved. For this particular objective the existing Hall cut prevents any separator of the complete combined relaxation. |
| 03 Reciprocal overlap | 05 | [Joint label compression](../../MOC/FiniteFrameLabels.lean) preserves the full common compression with at most 4k² total labels (three [exact replay fixtures](frames/README.md)); after reduction the necessary square order is at most 4k²−k. Order 33 suffices for overlap three. Includes the optional zero convention. | The full inequality up to order 33 is not proved. |
| 04 Grouped pencil | 03 | [Exact two-pivot elimination](../../MOC/GroupedMomentElimination.lean); [replay](frames/README.md) includes fixed masses and the distinction from false conditional formulas. | Universal fixed-mass feasibility and the genuinely realizable two-entry pencil are open. |
| 05 Global orbit and flow | 04 | [Exact double-bracket score derivative](../../MOC/DoubleBracketScore.lean), related to [Brockett's flow](https://doi.org/10.1016/0024-3795(91)90021-N). | No logistic bound or forced actual orbit tie. Matching contact equality is not orbit stationarity. |
| 06 Terminal geometry | 06 | [Fully checked paired-block certificate](../../MOC/ZhengPairedContacts.lean) removes the paired T85 branch; support remains on the positive-height, eight-or-more-contact branch. The contact differential and distinct-active theorem constrain the candidate. | No complete terminal motif classification, and no resolution of the other cases in [Zheng's Proposition 4.4](https://doi.org/10.13140/RG.2.2.36790.25923). |
| 07 Flag transport and variance | 07 | [Threshold lattice argument](../../MOC/ThresholdVariance.lean), [actual integral rank-one lattice bound](../../MOC/RankOneLattice.lean), signed moment identities, and [bounded Cayley and all-prefix tests](transport/README.md), with exact and numerical results labelled separately. | The lattice conclusion is weaker than the genuine adjacent assignment-score gap; the separate relaxation gap fixture makes that difference explicit. No exact all-prefix LP certificate. |
| 08 Orthogonal/quaternion | 09 | [Order-five fixed-anchor obstruction](../../FixedAnchorOrderFiveObstruction.md) uses actual unitary row effects and a symbolic graph, rather than dimension count alone. Order-four paired certificate applies to every unitary. | The unrestricted anchor-varying order-five mixture is not refuted or proved. |
| 09 Möbius/disk/antipodal | 08 | [Pole-free three-point normalization](../../MOC/FractionalFiniteNormalization.lean) excludes every pole in a prescribed finite input set. [The reciprocal branch](../../GapFreeTerminalGeometry.md) still needs a support comparison. | Moving corank boundary, strict Schur margin, and generic positive-height witness remain open; the symbolic tests do not establish an angular bound. |
| 10 Hall and radial/tropical | 10 | Replayed the exact nested Hall repair in [phase replay](phase/README.md). [Frame/pencil/radial replay](frames/frame_pencil_radial_replay.py) checks assignment-dual radial estimates; [the unit-modulus rank-two chart](../../MOC/UnitModulusRankTwo.lean) forces at most two factors on one side. | No phase-sensitive tropical support comparison or arbitrary-order Hall cone completeness. |
| 11 Spinor and phase defect | 11 | [Signed covariance](../../MOC/RankOneVariance.lean) on rank-one costs; [Null-phase Gram jet](../../MOC/PhaseGramJet.lean) proves the quartic determinant coefficient from single swaps and its sign; the exact arbitrary-cost example is replayed separately. | The full passage to the centred signed fourth moment is not checked here. No phase integrability claim or uniform defect estimate. |
| 12 Harmonic marker and Fourier SOS | 12 | [Finite phase-loss Gram test](../../MOC/UnitaryPhaseCuts.lean) and the exact adaptive dictionary separation. For characters the finite Gram test is the finite analogue of the agenda's Toeplitz test. | No torus SOS completeness or lift from unrestricted signed measures to actual mixer data. |
| 13 Exact Cayley search | 13 | [72 exact scalar fixtures, 983 directions](transport/README.md), no violation, with zero/near-zero, repeated and near-antipodal spectra. | No exhaustive search in the continuous parameter family. |
| 14 Stable/mixed phases | 14 | [Closed-polydisc contraction](../../MOC/UnitaryPhaseCuts.lean), proved by a Gram determinant bound without positive signed weights. | Contractive is not stable; tensor rank-one evaluation does not give a full coefficient law. |
| 15 Transposition topology | 15 | Paired subgroup support certified directly, without a topological upper enclosure. [Contact graph certificates](../../MOC/ContactGraphCertificates.lean) check component boundary and the relative-contact graph statement separately from transposition ties. | No global transposition-graph connectivity or polygon upper enclosure is used. |

See the [contact and orbit scope note](../../ContactOrbitCoverage.md)
for the six related paths and their limits, and the [phase variance note](../../PhaseVarianceReplay.md) for the signed fourth-moment boundary.

The original named verifier and dual files were not attached; the checks
above reconstruct the stated finite dictionaries from their descriptions.
The large historical floating-point searches were not all rerun. The
remaining proof and experiment gates are recorded rather than treated
as finished. No counterexample to MOC or proof of unrestricted order-four
MOC follows from these results.

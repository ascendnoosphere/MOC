# Literature and proof scope

Use [the proof tree](ProofTree.md) for the current Lean routes. The sources
below are references for those routes. A published theorem or a preprint is
not an imported axiom. A statement counts as verified here only when a
linked Lean declaration proves it.

| Primary source | Result or technique | Use in this repository |
| --- | --- | --- |
| D. Zheng, *The Marcus–de Oliveira conjecture for n = 4*, [preprint DOI](https://doi.org/10.13140/RG.2.2.36790.25923) | Theorem 3.6 moves a violating order-four profile to one with at least six contact labels. The proposed closing argument uses a classification of contact sets. | [Contact transfer on an affine curve](MOC/AffineContactCurve.lean) keeps the complex determinant gap fixed and uses connectedness plus a cofinite coordinate image. [Curve selection](MOC/FiniteCurveAtPinnedPrime.lean) and the [global reduction](MOC/GlobalContactSlice.lean) construct and use a slice at every strict witness, including zero matching products. The repository does not count the preprint's order-four conclusion as a Lean proof. |
| B. Howard, J. Millson, A. Snowden and R. Vakil, *The equations for the moduli space of n points on the line*, [DOI](https://doi.org/10.1215/00127094-2008-063) | Projective configuration charts and invariant relations. | [Anchored matching coordinates](MOC/Source.lean) give an explicit rank-one kernel chart. No invariant-ring presentation is assumed in the Lean transfer. |
| J. K. Merikoski and A. Virtanen, *Some notes on de Oliveira's determinantal conjecture*, [DOI](https://doi.org/10.1016/0024-3795(89)90709-X) | Subset-image and squared-minor conditions for common weights. | [Signed moments](MOC/Weights.lean) and the [order-five objective formula](MOC/OrderFivePairCost.lean) support certificates for a chosen spectral objective. They do not assert a positive law for every objective at once. |
| S. W. Drury, *OMC for Householder reflections*, [DOI](https://doi.org/10.1016/S0024-3795(99)00173-1) | MOC for Householder mixers; failure of the stronger common compound law in order five. | [Order-five obstruction](MOC/OrderFiveCommonLawObstruction.lean) proves the distinction by bounding the number of moved labels. The example is not a counterexample to MOC. |
| S. W. Drury, *The external vertices conjecture in case n = 4*, [DOI](https://doi.org/10.13001/1081-3810.1131) | Normalized external subset certificates in order four. | [Radial certificate theorem](MOC/RadialExternalCertificates.lean) proves the exact geometric consequence in any order when such certificates are supplied. The segment from zero to the determinant meets the matching hull. The determinant can still lie beyond the hull. |
| Y. N. Shitov, *A further sufficient condition for the determinantal conjecture*, [English edition DOI](https://doi.org/10.4213/im9292e) | One real spectrum and at most three nonreal entries in the other spectrum. | [Real-pivot reduction](MOC/FiveNonreal.lean). This result is not a claim for two arbitrary complex spectra. |
| J. I. Mulero-Martínez, *A variational framework for determinantal inequalities of normal matrices: Successes and obstructions*, [DOI](https://doi.org/10.1016/j.laa.2026.03.019) | Support-function proofs in structured cases and an example of a nonmonomial maximizer. | Compare the [stationary witness reduction](MOC/OrderFourIndependent.lean). Do not infer that all support maximizers are monomial from stationarity alone. |
| R. Lyons, *Determinantal probability measures*, [DOI](https://doi.org/10.1007/s10240-003-0016-0), [author manuscript](https://rdlyons.pages.iu.edu/pdf/bases.pdf) | Projection determinantal measures and stochastic domination for nested subspaces. | [Full flag law](MOC/FullFlagLaw.lean) glues checked adjacent couplings to realize all squared-minor marginals along one flag. No common law across all flags is claimed. |
| A. Kovacec, *A large polygonal region contained in a simply connected Marcus de Oliveira region*, [DMUC Preprint 26-11 v2, 4 Nov 2026](https://www.mat.uc.pt/preprints/ps/p2611.pdf), no DOI identified | The revision reports counterexamples to the original transposition-polygon enclosure from v1. It studies the reverse inclusion under simple connectivity. Neither result disproves MOC. | [Complex flat swaps](MOC/ComplexFlatSwap.lean) use two-coordinate rotations, but start at an arbitrary maximizing mixer. They do not rely on the polygon enclosure. |

The [two-outlier block comparison](MOC/PositiveTwoOutlierBlock.lean) uses
Schur elimination for Hermitian blocks; see E. V. Haynsworth,
*Determination of the inertia of a partitioned Hermitian matrix*,
[DOI](https://doi.org/10.1016/0024-3795(68)90050-5). The two-outlier
determinant comparison is proved directly, not taken from that paper.
The [spectral form](MOC/SpectralTwoOutlierComparison.lean) proves the
height-zero bound for the stated two-outlier spectra and every unitary
mixer. It uses an ambient inverse Gram determinant instead of an
adapted block basis.

For the algebraic slice, [Stacks Project §10.60](https://stacks.math.columbia.edu/tag/00KD)
records the principal and generalized height bounds. The
[upstream Mathlib development](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean)
is newer than the pinned project toolchain. This repository proves the
[prime-chain generator bound](MOC/KrullHeightChain.lean) on the pinned
toolchain. The [curve construction](MOC/FiniteCurveAtPinnedPrime.lean)
uses finite Noether normalization and
[going down over a normal domain](https://stacks.math.columbia.edu/tag/00H8).
Lean proves the required characteristic-zero going-down result using
Galois transitivity of primes. These steps complete the transfer, not
the terminal support inequality.

[Chevalley constructibility](https://stacks.math.columbia.edu/tag/054K)
and Euclidean closedness enter the [exact profile locus](MOC/ExactProfileLocus.lean).
The proof passes through the complex closed points and uses a dense
principal open of an irreducible affine set. Constructibility, not
Euclidean closedness alone, is essential. Stacks Project tags identify
these reference statements; they do not have paper DOIs.

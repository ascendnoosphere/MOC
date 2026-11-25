# Literature and proof scope

Use [the proof tree](ProofTree.md) for the current Lean routes. The sources
below are references for those routes. A published theorem or a preprint is
not an imported axiom. A statement counts as verified here only when a
linked Lean declaration proves it.

| Primary source | Result or technique | Use in this repository |
| --- | --- | --- |
| D. Zheng, *The Marcus–de Oliveira conjecture for n = 4*, [preprint DOI](https://doi.org/10.13140/RG.2.2.36790.25923) | Theorem 1.2 gives a common two-table mixture; Theorem 3.6 moves a strict witness to at least six contacts. | Lean proves [the exact two-table statement](MOC/FourMinorTransport.lean) by an independent effect argument and [reduces order four to at least seven real orthogonal contacts](MOC/ZhengContactReduction.lean). See the [PDF audit](ZhengOrderFourReview.md) for Proposition 4.4, which is not verified. |
| S. Elliott and M. T. Jury, *Composition operators on Hardy spaces of a half-plane*, [journal DOI](https://doi.org/10.1112/blms/bdr110), [open preprint DOI](https://doi.org/10.48550/arXiv.0907.0350) | Proposition 2.2 states the boundary angular-derivative comparison for the half-plane. | [Half-plane limit](MOC/HalfPlaneContactLimit.lean) proves the needed positive-real radial quotient limit directly from the Schwarz lemma. It does not use a composition-operator theorem. See [affine gap continuation](AffineGapContinuation.md). |
| C. T. C. Wall, *Singular Points of Plane Curves*, chapter 2, [DOI](https://doi.org/10.1017/CBO9780511617560.003) | Convergent plane-curve Puiseux expansions. | The [alternative affine end argument](AffineGapContinuation.md) obtains its Laurent sector by finite covering and a removable singularity. [Lean checks the meromorphic endpoint](MOC/ContactMeromorphicSector.lean), not the construction of the sector from the given affine curve. |
| S. Basu and M.-F. Roy, *Quantitative Curve Selection Lemma*, [journal DOI](https://doi.org/10.1007/s00209-021-02837-0), [preprint DOI](https://doi.org/10.48550/arXiv.1803.00505) | Real semialgebraic curve selection with degree bounds. | [Affine gap continuation](AffineGapContinuation.md) explains why control on a real arc alone does not give the needed reality or order of a leading coefficient. No degree bound is imported. |
| B. Howard, J. Millson, A. Snowden and R. Vakil, *The equations for the moduli space of n points on the line*, [DOI](https://doi.org/10.1215/00127094-2008-063) | Projective configuration charts and invariant relations. | [Anchored matching coordinates](MOC/Source.lean) give an explicit rank-one kernel chart. No invariant-ring presentation is assumed in the Lean transfer. |
| J. K. Merikoski and A. Virtanen, *Some notes on de Oliveira's determinantal conjecture*, [DOI](https://doi.org/10.1016/0024-3795(89)90709-X) | Subset-image and squared-minor conditions for common weights. | [Signed moments](MOC/Weights.lean) and the [order-five objective formula](MOC/OrderFivePairCost.lean) support certificates for a chosen spectral objective. They do not assert a positive law for every objective at once. The [antipodal center formula](MOC/AntipodalCenterMinor.lean) uses just one subset-image probability. |
| P. R. Halmos, *Two subspaces*, [DOI](https://doi.org/10.1090/S0002-9947-1969-0251519-5) | The four common sign spaces and Theorem 2's generic two-projection decomposition. | The [singular antipodal jet](MOC/AntipodalKernelJet.lean) proves the required kernel split and trace parity directly, without assuming the full decomposition. See [scope and the smaller-order comparison](AntipodalKernelJets.md). |
| S. W. Drury, *OMC for Householder reflections*, [DOI](https://doi.org/10.1016/S0024-3795(99)00173-1) | MOC for Householder mixers; failure of the stronger common compound law in order five. | [Order-five obstruction](MOC/OrderFiveCommonLawObstruction.lean) proves the distinction by bounding the number of moved labels. The example is not a counterexample to MOC. |
| S. W. Drury, *The external vertices conjecture in case n = 4*, [DOI](https://doi.org/10.13001/1081-3810.1131) | Normalized external subset certificates in order four. | [Radial certificate theorem](MOC/RadialExternalCertificates.lean) proves the exact geometric consequence in any order when such certificates are supplied. The segment from zero to the determinant meets the matching hull. The determinant can still lie beyond the hull. |
| Y. N. Shitov, *A further sufficient condition for the determinantal conjecture*, [English edition DOI](https://doi.org/10.4213/im9292e) | One real spectrum and at most three nonreal entries in the other spectrum. | [Real-pivot reduction](MOC/FiveNonreal.lean). This result is not a claim for two arbitrary complex spectra. |
| J. I. Mulero-Martínez, *A variational framework for determinantal inequalities of normal matrices: Successes and obstructions*, [DOI](https://doi.org/10.1016/j.laa.2026.03.019) | Support-function proofs in structured cases and an example of a nonmonomial maximizer. | Compare the [stationary witness reduction](MOC/OrderFourIndependent.lean). Do not infer that all support maximizers are monomial from stationarity alone. |
| R. Lyons, *Determinantal probability measures*, [DOI](https://doi.org/10.1007/s10240-003-0016-0), [author manuscript](https://rdlyons.pages.iu.edu/pdf/bases.pdf) | Projection determinantal measures and stochastic domination for nested subspaces. | [Full flag law](MOC/FullFlagLaw.lean) glues checked adjacent couplings to realize all squared-minor marginals along one flag. No common law across all flags is claimed. The [crossed-minor theorem](MOC/CrossedMinorBridge.lean) uses the same shadow mechanism for two crossed minor arrays, not as a common permutation law. |
| A. Kovacec, *A large polygonal region contained in a simply connected Marcus de Oliveira region*, [DMUC Preprint 26-11 v2, 4 Nov 2026](https://www.mat.uc.pt/preprints/ps/p2611.pdf), no DOI identified | The revision reports counterexamples to the original transposition-polygon enclosure from v1. It studies the reverse inclusion under simple connectivity. Neither result disproves MOC. | [Complex flat swaps](MOC/ComplexFlatSwap.lean) use two-coordinate rotations, but start at an arbitrary maximizing mixer. They do not rely on the polygon enclosure. |
| M. Speck, *Determinants of Sums of Normal Matrices*, [Auburn dissertation, 2024](https://etd.auburn.edu/handle/10415/9283), no DOI identified | Theorem 2.2.31 describes the kernel of the subset-image map by induced three-label alternating vectors. | The [contact marker theorem](MOC/ContactMarkerRank.lean) checks the exact relation between matching-function relations and subset incidences directly. It does not use or formalize the representation-theoretic description. |
| G. Lakos, *A short proof of the elliptical range theorem*, [DOI](https://doi.org/10.1007/s00013-023-01957-9), [arXiv:2208.06248](https://arxiv.org/abs/2208.06248) | The numerical range of a complex two-by-two matrix is a possibly degenerate filled ellipse. | [Pair-plane support and optimality](MOC/PairRayleigh.lean) identify the determinant of the pair orbit with a cofactor Rayleigh quotient. The support formula and identity optimality test are proved directly. |
| R. W. Cottle, *Manifestations of the Schur complement*, [DOI](https://doi.org/10.1016/0024-3795(74)90066-4) | Block elimination via the Schur complement. | The [three-slot expansion](MOC/TripleOrbit.lean) uses an invertible inactive block, then evaluates the mixed determinant of the active triple. The [corank-two cubic note](AntipodalCubicAudit.md) uses the same block elimination and separates the paper spectral-mixture comparison from the checked [coefficient formula](MOC/AntipodalCubicSchur.lean) and [residual cancellation](MOC/AntipodalCubicEnergy.lean). |
| D. Wang, W. Chen, S. Z. Khong and L. Qiu, *On the phases of a complex matrix*, [DOI](https://doi.org/10.1016/j.laa.2020.01.035), [arXiv:1904.07211](https://arxiv.org/abs/1904.07211) | §4, Theorem 4.3 concerns phase interlacing for sectorial Schur complements. | The [flat-pair argument](FlatPairReduction.md) proves the needed strict half-plane inheritance directly and records which local implications are Lean-checked. |
| S. W. Drury, *Essentially Hermitian matrices revisited*, [DOI](https://doi.org/10.13001/1081-3810.1239) | §1 uses common fractional-linear transport of spectra in the determinantal conjecture. | The [complex tied-swap note](ComplexTiedSwap.md) separates this determinant covariance from the directly proved covariance of inverse-entry zeros. |
| G. A. Jones, *Automorphisms and regular embeddings of merged Johnson graphs*, [DOI](https://doi.org/10.1016/j.ejc.2004.01.012) | Theorem 2 classifies automorphisms, including the complement symmetry in the middle layer. | The [crossed-cut scope note](DeterministicAndFractional.md) combines the classification on paper with Lean's adjacency and complement-exclusion lemmas. Jones's theorem is not a Lean dependency. |
| Y. Filmus and E. Mossel, *Harmonicity and invariance on slices of the Boolean cube*, [DOI](https://doi.org/10.1007/s00440-019-00900-w), [preprint DOI](https://doi.org/10.48550/arXiv.1507.02713) | Disjoint differences span the top harmonic subspace on a slice. | The [dimension note](research/agenda-2026-11-25/MarkerHarmonicDimension.md) derives the exact reciprocal overlap objective dimension. [Lean checks the harmonic coefficient identity](MOC/PartialMatchingHarmonic.lean), not the dimension theorem. |
| P. Hall, *On Representatives of Subsets*, [DOI](https://doi.org/10.1112/jlms/s1-10.37.26) | The finite marriage condition. | The [unequal-color feasibility criterion](MOC/UnequalColorHall.lean) reduces Hall’s inequalities to color multiplicities. It does not count matchings. |
| R. M. Redheffer, *On the relation of transmission-line theory to scattering and transfer*, [DOI](https://doi.org/10.1002/sapm19624111) | Feedback under block elimination. | The [strict disk barrier](MOC/OrbitTargets.lean) proves the needed energy estimate directly; it does not import a feedback theorem. |
| M. Oszmaniec et al., *Simulating positive-operator-valued measures with projective measurements*, [DOI](https://doi.org/10.1103/PhysRevLett.119.190501), [preprint DOI](https://doi.org/10.48550/arXiv.1609.06139) | Projective simulability and qutrit effects. | Background for the [effect decomposition](MOC/FourEffectDecomposition.lean); the exact two-basis result follows from the real rank-two support argument. |

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

The [isolated-fibre reduction](MOC/ContactFibreIsolation.lean) uses the
finiteness of the minimal primes of a Noetherian ring
([Stacks Project, Tag 00FR](https://stacks.math.columbia.edu/tag/00FR))
and the polynomial separation behind
[Tag 0BX1](https://stacks.math.columbia.edu/tag/0BX1). It applies the
fixed-gap contact strategy of Zheng
([preprint DOI](https://doi.org/10.13140/RG.2.2.36790.25923)) to a strict
smaller-prime branch even when the contact threshold has been reached.

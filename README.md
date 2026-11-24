# Marcus–de Oliveira in Lean

This Lean 4 library states the Marcus–de Oliveira conjecture (MOC) and proves the cases below. The unrestricted conjecture is open. [Claim](Lean/MOC/Claim.lean)

**Order-four external proof under review (2026-11-24).** Denzel Zheng's [October 2026 preprint](https://doi.org/10.13140/RG.2.2.36790.25923) claims the full order-four theorem. The supplied main PDF has been reviewed and its facet/contact census and several key polynomial identities have been independently verified in exact arithmetic. The required separate exceptional-contact supplement was not available, so the order-four theorem has not been added to the Lean-verified results. See the [review and audit](Lean/ZhengOrderFourReview.md). The project now also has a [general contact reduction and order-five research note](Lean/OrderFiveContactReduction.md).

## Build

Install Elan. Run these commands from the repository root. [Elan](https://github.com/leanprover/elan)

```sh
cd Lean
lake build
```

Elan uses the Lean version in `lean-toolchain`. Lake uses the dependency revisions in `lake-manifest.json`. [Toolchain](Lean/lean-toolchain) · [Manifest](Lean/lake-manifest.json)

## Proved cases

Let $A$ and $B$ be normal matrices of order $n$, with ordered spectra $a$ and $b$. Let $U$ be their relative unitary matrix. A matching product is $P_\sigma=\prod_j(a_{\sigma(j)}+b_j)$.

| MOC proved for | Order | Lean proof |
| --- | --- | --- |
| All complex spectra and all relative unitary matrices. | At most three | [Small.lean](Lean/MOC/Small.lean) |
| Pairs with a common unitary eigenbasis. | Any finite order | [Normal.lean](Lean/MOC/Normal.lean) |
| Pairs with a singular sum. | Any finite order | [Singular.lean](Lean/MOC/Singular.lean) |
| Two real spectra. | Any finite order | [Hermitian.lean](Lean/MOC/Hermitian.lean) |
| Two spectra on parallel affine lines. | Any finite order | [Collinear.lean](Lean/MOC/Collinear.lean) |
| A real first spectrum and a second spectrum that is real outside one specified entry. | Any positive order | [OneOffLine.lean](Lean/MOC/OneOffLine.lean) |
| A real first spectrum and at most three nonreal eigenvalues in the second spectrum, counted with multiplicity. | Any finite order | [FiveNonreal.lean](Lean/MOC/FiveNonreal.lean) |
| A real first spectrum and at most three distinct nonreal eigenvalues in the second spectrum, with arbitrary multiplicities. | Any finite order | [HermitianByNormalGeneral.lean](Lean/MOC/HermitianByNormalGeneral.lean) |
| A real first spectrum and a second spectrum whose nonreal eigenvalues lie on one circle or line. The real eigenvalues may be arbitrary. | Any finite order | [HermitianByNormalGeneral.lean](Lean/MOC/HermitianByNormalGeneral.lean) |
| The first spectrum and all but one entry of the negated second spectrum on the same circle or line. | Any positive order | [GeneralizedSpectralCircles.lean](Lean/MOC/GeneralizedSpectralCircles.lean) |
| The first spectrum on a circle or line, with at most three distinct values of the negated second spectrum outside that circle or line. The outlier values may have arbitrary multiplicities. | Any finite order | [HermitianByNormalGeneral.lean](Lean/MOC/HermitianByNormalGeneral.lean) |
| The first spectrum lies on a circle or line $C$. Each entry of the negated second spectrum lies on $C$ or on a second circle or line $D$. Either part can have any size. | Any finite order | [TwoCircleCover.lean](Lean/MOC/TwoCircleCover.lean) |
| The first spectrum and the negated second spectrum on two tangent circles of positive radius. | Any finite order | [CircleSpectra.lean](Lean/MOC/CircleSpectra.lean) |
| Two spectra that each lie on a circle or line, with independent circles or lines. | Any finite order | [TwoSpectralCircles.lean](Lean/MOC/TwoSpectralCircles.lean) |
| A spectrum with at most two distinct values on either side. | Any finite order | [TwoValues.lean](Lean/MOC/TwoValues.lean) |
| A second spectrum whose entries, except for one specified entry, take at most two distinct values. | Any positive order | [ThreeValues.lean](Lean/MOC/ThreeValues.lean) |
| A first spectrum with one value in all but at most two positions. | Any finite order | [TwoExceptions.lean](Lean/MOC/TwoExceptions.lean) |
| Either spectrum with a repeated value. | Four | [TwoExceptions.lean](Lean/MOC/TwoExceptions.lean) |
| An opposite eigenvalue pair, with $a_i+b_j=0$ for some $i,j$. | Four | [FourCoincidence.lean](Lean/MOC/FourCoincidence.lean) |
| An opposite eigenvalue pair whose two eigenvalue multiplicities sum to at least $n-2$. | Any finite order | [OppositePair.lean](Lean/MOC/OppositePair.lean) |
| An opposite eigenvalue pair of simple eigenvalues with normal reciprocal compressions on the overlap of the two spectral support spaces. | Five | [OppositePairNormal.lean](Lean/MOC/OppositePairNormal.lean) |
| Two equilateral triples with opposite first vertices and independent nonzero complex scales. Each spectrum has a fourth point off its circumcircle. | Four | [FourEquilateral.lean](Lean/MOC/FourEquilateral.lean) |
| The centrally symmetric spectra $t+s\{\pm2,\pm(2+i)\}$ and $-t+s\{\pm3,\pm(3-i)\}$, with $s\ne0$. Both spectra are nonconcyclic, and every cross-sum is nonzero. | Four | [FourCentralSymmetry.lean](Lean/MOC/FourCentralSymmetry.lean) |
| The first spectrum has entries $x,-x,y,-y$. The second spectrum is $t$ times the first. The axes $x,y$ and the scale $t$ can be any complex numbers. Opposite shifts are allowed. | Four | [HomotheticFour.lean](Lean/MOC/HomotheticFour.lean) |
| In order five, three entries of the first spectrum match three entries of the negated second spectrum. The other two entries of either list are equal. At larger orders, append copies of one matched value to both signed lists. | Five or greater | [ThreeSharedRepeatedFiveShapes.lean](Lean/MOC/ThreeSharedRepeatedFiveShapes.lean) |
| The first spectrum has entries $0,x,-x,y,-y$. The second spectrum is twice the first. The axes $x,y$ can be any complex numbers. Both lists can have additional zeros and opposite shifts. | Five or greater | [DoubledFive.lean](Lean/MOC/DoubledFive.lean) |
| For $X=(0,1,-1,i,-i)$, the spectra are $c+sX$ and $-c+rsX$, with complex $c,s$ and real $r\ge0$. Both lists can have additional copies of their centers. | Five or greater | [FiveCross.lean](Lean/MOC/FiveCross.lean) · [CrossPadding.lean](Lean/MOC/CrossPadding.lean) |
| The first spectrum and the negated second spectrum share the four values $f(0),f(2),f(3),f(6)$ for a fractional-linear map $f$ with no pole at $0,2,3,6$. The other two entries are arbitrary. At larger orders, repeat one of the four shared signed values. | Five or greater | [HarmonicAnchors.lean](Lean/MOC/HarmonicAnchors.lean) |
| The fixed Hermitian spectrum $(-9,-8,-6,-2,8)$, every complex partner, and relative unitaries in a neighborhood of the specified rational orthogonal matrix. At each unitary, one probability law applies to every partner. | Five | [HermitianLineCertificate.lean](Lean/MOC/HermitianLineCertificate.lean) |
| A total rank of at most $n+2$ for $A+tI$ and $B-tI$, for some complex scalar $t$. | Any finite order | [RankSum.lean](Lean/MOC/RankSum.lean) · [RankTwoOverlap.lean](Lean/MOC/RankTwoOverlap.lean) |
| Each list has at most three free entries. The other entries are $c$ in the first list and $-c$ in the second list. | Any finite order | [MarkedPadding.lean](Lean/MOC/MarkedPadding.lean) |
| Each list has at most four free entries. The other entries are $c$ in the first list and $-c$ in the second list. | Six or greater | [MarkedPadding.lean](Lean/MOC/MarkedPadding.lean) |
| Start with an order-$d$ pair that satisfies MOC for every relative unitary. If the two lists contain at most $d+3$ nonzero entries in total, append the same number of zeros to each list. The enlarged relative unitary is arbitrary. | Any order $n\ge d$ | [SpectralZeroPadding.lean](Lean/MOC/SpectralZeroPadding.lean) |
| Relative unitary $U=I+(z-1)vv^*$, with $\lVert v\rVert=1$ and $\lvert z\rvert=1$. | Any positive order | [HouseholderSupport.lean](Lean/MOC/HouseholderSupport.lean) |
| A relative unitary with a row or column that has at most two nonzero entries. | Four | [SparseRow.lean](Lean/MOC/SparseRow.lean) · [Small.lean](Lean/MOC/Small.lean) |
| An upper Hessenberg relative unitary after independent row and column permutations. Entries below the first subdiagonal are zero. | Any finite order | [SparseRow.lean](Lean/MOC/SparseRow.lean) |
| A relative unitary that splits into blocks of order at most three after independent row and column permutations. Any number of blocks is allowed. | Any finite order | [ExtendedCases.lean](Lean/MOC/ExtendedCases.lean) |
| A relative unitary $U$ for which $U-I$ has zero entries outside a principal block of order at most three. | Any finite order | [IdentityPadding.lean](Lean/MOC/IdentityPadding.lean) · [Small.lean](Lean/MOC/Small.lean) |
| Matching products that all lie on one affine line. | Any finite order | [CollinearKernelSupport.lean](Lean/MOC/CollinearKernelSupport.lean) |
| Large shifts $(a-z,b)$ for fixed $a,b,U$, with the trace margin given below. The theorem applies for all sufficiently large $\lvert z\rvert$. | Any finite order | [ExtendedCases.lean](Lean/MOC/ExtendedCases.lean) |
| Large shifts $(a-z,b)$ for arbitrary spectra when every entry of the relative unitary $U$ is nonzero. The radius may depend on $a,b,U$. | Any finite order | [ExtendedCases.lean](Lean/MOC/ExtendedCases.lean) |

A common fractional-linear map can act on the first spectrum and the negated second spectrum in each case. Its determinant must be nonzero. Its pole must avoid both signed spectra. The transformed pair has the same relative unitary. If fixed weights represent every partner of a first spectrum, they also represent every partner of its transformed spectrum. The converse holds. For this result the pole need only avoid the first spectrum. [ProjectiveTransport.lean](Lean/MOC/ProjectiveTransport.lean) · [CommonLawTransport.lean](Lean/MOC/CommonLawTransport.lean)

### Sufficient tests

Each test proves MOC for an instance that meets its hypotheses.

| Test | Lean proof |
| --- | --- |
| All real signed determinant weights of $U$ are nonnegative. | [Weights.lean](Lean/MOC/Weights.lean) |
| For every permutation $\sigma$, the matching product has the form $c+\sum_j f(j,\sigma(j))$, with fixed $c$ and $f$. | [Weights.lean](Lean/MOC/Weights.lean) |
| The relative unitary $U$ maximizes the determinant projection in a fixed direction. Its sum is normal and has largest Frobenius norm among the maximizing sums. | [NormalOrbit.lean](Lean/MOC/NormalOrbit.lean) |
| In order four, the relative unitary $U$ maximizes the determinant projection in a fixed direction. Its sum is normal and the maximizing projection is nonzero. | [NormalSupportMaximum.lean](Lean/MOC/NormalSupportMaximum.lean) |
| A convex representation of zero gives weights at least $\varepsilon\ge0$ to two matching products $p,q$. Require $\lVert p\rVert+\lVert q\rVert>0$ and $(\lVert p\rVert+\lVert q\rVert)\lvert\det(A+B)\rvert\le\varepsilon\lvert\mathrm{Im}(p\bar q)\rvert$. | [DiskBoundary.lean](Lean/MOC/DiskBoundary.lean) |

For the large-shift case, let $T=\mathrm{tr}(AB)$ and $q_\sigma=\sum_j a_{\sigma(j)}b_j$. The margin requires a $\delta>0$ that applies in every unit direction. For each $\eta$ with $\lvert\eta\rvert=1$, some permutation satisfies $\mathrm{Re}(\eta(T-q_\sigma))\ge\delta$.

The source guide defines the Lean statement and lists equivalent forms and proof reductions. [Source guide](Lean/README.md)

For the normal-maximizer approach, see the [research note](Lean/NormalMaximizerResearch.md). It gives exact counterexamples to universal normality of Frobenius-maximal support sums, proves a sufficient joint determinant/Frobenius law for the existential tie-break, and isolates the remaining general proof obligation. The note is mathematical research, not a Lean-checked extension of the proved cases.

For the Hessenberg-maximizer approach, see the [Hessenberg research note](Lean/HessenbergMaximizerResearch.md). It proves the arbitrary-kernel sparse-row recursion, nonnegativity of the signed permutation law for Hessenberg unitaries, support-preserving elimination, and exact Givens constraints. The general existence of a sparse maximizing representative remains open; these new proofs are not Lean-checked.

The [order-four sparse-maximizer note](Lean/SparseMaximizerOrderFour.md) proves the determinant hull inclusion for any order-four unitary with at least four zero entries, classifies the three-zero pattern, establishes its sharp negative signed-mass bound, and reduces its spectral support test to a three-variable convex minimization. It also gives an obstruction to sparsification for general minor-linear objectives. These are mathematical proofs, not yet Lean-checked.

The [stationary pivot reduction](Lean/StationaryPivotReduction.md) proves that any order-four global support maximizer with a zero entry can be replaced by a permutation maximizer for arbitrary complex spectra. More generally it applies to a real stationary mixer with a nonnegative entrywise Schur-complement pivot. The [three-zero tangent certificate](Lean/StationaryThreeZero.md) gives an independent explicit proof and symbolic check for that pattern. These are mathematical proofs, not yet Lean-checked; the fully supported case remains open.

The [dense stationary order-four reduction](Lean/DenseStationaryOrderFour.md) eliminates two of the three dense real sign classes using the stationary pivot theorem, reduces all remaining no-pivot sign patterns to one explicit Hadamard/minor-sign chamber, and formulates the remaining full conjecture as an explicit polynomial feasibility problem. Its emptiness is not yet established.

The [stationary Latin-gap note](Lean/StationaryLatinGap.md) proves the real-orthogonal stationary signed marginal identity in every finite order, derives thirteen geometric-mean bounds and twenty-four strict linear gap conditions for a hypothetical order-four violation, and reduces the residual proof to a finite spectral-only sufficient feasibility test. It includes exact permutation checks and an integer spectral obstruction to using the geometric-mean condition alone. The spectral feasibility problem remains unresolved; the new mathematics is not Lean-checked.

The [general contact reduction](Lean/OrderFiveContactReduction.md) extends Zheng's contact argument to arbitrary complex unitary mixers and every order using normalized rank-two kernels, without a new realification theorem. Any hypothetical order-five counterexample can be chosen with at least eight supporting matching labels. The note also extends the dense real orthogonal Cauchy-mixer common-law proof to arbitrary orders using the published nonnegative double-dimer identity. These are mathematical derivations, not new Lean-checked theorems. Exact verification scripts: [facet and contact census](Lean/research/zheng_contact_audit.py), [matching identities](Lean/research/zheng_algebra_audit.py).

The [reconstructed Zheng supplementary certificates](Lean/ZhengReconstructedSupplement.md) independently prove seven exceptional six-contact cases (T1 and T18–T23). The [parallel exact checker](Lean/research/zheng_reconstructed_cases.py) verifies all replacement identities and restricted cubic signs and proves a double-coincidence common-law obstruction. Combined with the 124 minor-only classes, these methods cover 131 of the 214 contact classes. The other 83 exceptional cases remain unaudited; the full order-four theorem is not yet a Lean-verified result.

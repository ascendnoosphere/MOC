# Proved cases of MOC

This list gives cases in which Lean proves the determinant inclusion. A case
applies only to the matrices or spectra in its description. All orders are
finite.

Let $A$ and $B$ be normal matrices of order $n$. Let $a$ and $b$ be their
ordered eigenvalue lists. Let $U$ be the unitary matrix that relates their
eigenbases. A matching product is $P_\sigma=\prod_j(a_{\sigma(j)}+b_j)$.

## Basic cases

| MOC proved for | Order | Lean proof |
| --- | --- | --- |
| All complex spectra and all relative unitary matrices. | At most three | [Small.lean](MOC/Small.lean) |
| Pairs with a common unitary eigenbasis. | Any finite order | [Normal.lean](MOC/Normal.lean) |
| Pairs with a singular sum. | Any finite order | [Singular.lean](MOC/Singular.lean) |

## Conditions on the spectra

| MOC proved for | Order | Lean proof |
| --- | --- | --- |
| Two real spectra. | Any finite order | [Hermitian.lean](MOC/Hermitian.lean) |
| Two spectra on parallel affine lines. | Any finite order | [Collinear.lean](MOC/Collinear.lean) |
| A real first spectrum and a second spectrum that is real outside one specified entry. | Any positive order | [OneOffLine.lean](MOC/OneOffLine.lean) |
| A real first spectrum and at most three nonreal eigenvalues in the second spectrum, counted with multiplicity. | Any finite order | [FiveNonreal.lean](MOC/FiveNonreal.lean) |
| A real first spectrum and at most three distinct nonreal eigenvalues in the second spectrum, with arbitrary multiplicities. | Any finite order | [HermitianByNormalGeneral.lean](MOC/HermitianByNormalGeneral.lean) |
| A real first spectrum and a second spectrum whose nonreal eigenvalues lie on one circle or line. The real eigenvalues may be arbitrary. | Any finite order | [HermitianByNormalGeneral.lean](MOC/HermitianByNormalGeneral.lean) |
| The first spectrum and all but one entry of the negated second spectrum on the same circle or line. | Any positive order | [GeneralizedSpectralCircles.lean](MOC/GeneralizedSpectralCircles.lean) |
| The first spectrum on a circle or line, with at most three distinct values of the negated second spectrum outside that circle or line. The outlier values may have arbitrary multiplicities. | Any finite order | [HermitianByNormalGeneral.lean](MOC/HermitianByNormalGeneral.lean) |
| The first spectrum lies on a circle or line $C$. Each entry of the negated second spectrum lies on $C$ or on a second circle or line $D$. Either part can have any size. | Any finite order | [TwoCircleCover.lean](MOC/TwoCircleCover.lean) |
| The first spectrum and the negated second spectrum on two tangent circles of positive radius. | Any finite order | [CircleSpectra.lean](MOC/CircleSpectra.lean) |
| Two spectra that each lie on a circle or line, with independent circles or lines. | Any finite order | [TwoSpectralCircles.lean](MOC/TwoSpectralCircles.lean) |
| A spectrum with at most two distinct values on either side. | Any finite order | [TwoValues.lean](MOC/TwoValues.lean) |
| A second spectrum whose entries, except for one specified entry, take at most two distinct values. | Any positive order | [ThreeValues.lean](MOC/ThreeValues.lean) |
| A first spectrum with one value in all but at most two positions. | Any finite order | [TwoExceptions.lean](MOC/TwoExceptions.lean) |
| Either spectrum with a repeated value. | Four | [TwoExceptions.lean](MOC/TwoExceptions.lean) |
| An opposite eigenvalue pair, with $a_i+b_j=0$ for some $i,j$. | Four | [FourCoincidence.lean](MOC/FourCoincidence.lean) |
| An opposite eigenvalue pair whose two eigenvalue multiplicities sum to at least $n-2$. | Any finite order | [OppositePair.lean](MOC/OppositePair.lean) |
| An opposite eigenvalue pair of simple eigenvalues with normal reciprocal compressions on the overlap of the two spectral support spaces. | Five | [OppositePairNormal.lean](MOC/OppositePairNormal.lean) |
| Two equilateral triples with opposite first vertices and independent nonzero complex scales. Each spectrum has a fourth point off its circumcircle. | Four | [FourEquilateral.lean](MOC/FourEquilateral.lean) |
| A total rank of at most $n+2$ for $A+tI$ and $B-tI$, for some complex scalar $t$. | Any finite order | [RankSum.lean](MOC/RankSum.lean) · [RankTwoOverlap.lean](MOC/RankTwoOverlap.lean) |
| Each list has at most three free entries. The other entries are $c$ in the first list and $-c$ in the second list. | Any finite order | [MarkedPadding.lean](MOC/MarkedPadding.lean) |
| Each list has at most four free entries. The other entries are $c$ in the first list and $-c$ in the second list. | Six or greater | [MarkedPadding.lean](MOC/MarkedPadding.lean) |
| Start with an order-$d$ pair that satisfies MOC for every relative unitary. If the two lists contain at most $d+3$ nonzero entries in total, append the same number of zeros to each list. The enlarged relative unitary is arbitrary. | Any order $n\ge d$ | [SpectralZeroPadding.lean](MOC/SpectralZeroPadding.lean) |

## Conditions on the relative unitary

| MOC proved for | Order | Lean proof |
| --- | --- | --- |
| Relative unitary $U=I+(z-1)vv^*$, with $\lVert v\rVert=1$ and $\lvert z\rvert=1$. | Any positive order | [HouseholderSupport.lean](MOC/HouseholderSupport.lean) |
| A relative unitary with a row or column that has at most two nonzero entries. | Four | [SparseRow.lean](MOC/SparseRow.lean) · [Small.lean](MOC/Small.lean) |
| An upper Hessenberg relative unitary after independent row and column permutations. Entries below the first subdiagonal are zero. | Any finite order | [SparseRow.lean](MOC/SparseRow.lean) |
| A relative unitary that splits into blocks of order at most three after independent row and column permutations. Any number of blocks is allowed. | Any finite order | [ExtendedCases.lean](MOC/ExtendedCases.lean) |
| A relative unitary $U$ for which $U-I$ has zero entries outside a principal block of order at most three. | Any finite order | [IdentityPadding.lean](MOC/IdentityPadding.lean) · [Small.lean](MOC/Small.lean) |

## Other proved cases

| MOC proved for | Order | Lean proof |
| --- | --- | --- |
| Matching products that all lie on one affine line. | Any finite order | [CollinearKernelSupport.lean](MOC/CollinearKernelSupport.lean) |
| Large shifts $(a-z,b)$ for fixed $a,b,U$, with the trace margin given below. The theorem applies for all sufficiently large $\lvert z\rvert$. | Any finite order | [ExtendedCases.lean](MOC/ExtendedCases.lean) |
| Large shifts $(a-z,b)$ for arbitrary spectra when every entry of the relative unitary $U$ is nonzero. The radius may depend on $a,b,U$. | Any finite order | [ExtendedCases.lean](MOC/ExtendedCases.lean) |

For the first large-shift result, set $T=\mathrm{tr}(AB)$ and
$q_\sigma=\sum_j a_{\sigma(j)}b_j$. The required margin is a number
$\delta>0$. For each $\eta$ with $\lvert\eta\rvert=1$, there must be a
permutation $\sigma$ with $\mathrm{Re}(\eta(T-q_\sigma))\ge\delta$.

## Change of spectral coordinates

You can apply the same fractional-linear map to $a$ and $-b$. Its determinant
must be nonzero, and its pole must not be in either list. The map preserves the
determinant inclusion and keeps the same relative unitary.
[Proof](MOC/ProjectiveTransport.lean)

## Sufficient conditions for one instance

| Test | Lean proof |
| --- | --- |
| All real signed determinant weights of $U$ are nonnegative. | [Weights.lean](MOC/Weights.lean) |
| For every permutation $\sigma$, the matching product has the form $c+\sum_j f(j,\sigma(j))$, with fixed $c$ and $f$. | [Weights.lean](MOC/Weights.lean) |
| The relative unitary $U$ maximizes the determinant projection in a fixed direction. Its sum is normal and has largest Frobenius norm among the maximizing sums. | [NormalOrbit.lean](MOC/NormalOrbit.lean) |
| In order four, the relative unitary $U$ maximizes the determinant projection in a fixed direction. Its sum is normal and the maximizing projection is nonzero. | [NormalSupportMaximum.lean](MOC/NormalSupportMaximum.lean) |
| A convex representation of zero gives weights at least $\varepsilon\ge0$ to two matching products $p,q$. Require $\lVert p\rVert+\lVert q\rVert>0$ and $(\lVert p\rVert+\lVert q\rVert)\lvert\det(A+B)\rvert\le\varepsilon\lvert\mathrm{Im}(p\bar q)\rvert$. | [DiskBoundary.lean](MOC/DiskBoundary.lean) |

# Marcus–de Oliveira in Lean

This Lean 4 library states the Marcus–de Oliveira conjecture (MOC) and proves the cases below. The unrestricted conjecture is open. [Claim](Lean/MOC/Claim.lean)

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
| The first spectrum and all but one entry of the negated second spectrum on the same circle or line. | Any positive order | [GeneralizedSpectralCircles.lean](Lean/MOC/GeneralizedSpectralCircles.lean) |
| The first spectrum and the negated second spectrum on two tangent circles of positive radius. | Any finite order | [CircleSpectra.lean](Lean/MOC/CircleSpectra.lean) |
| A spectrum with at most two distinct values on either side. | Any finite order | [TwoValues.lean](Lean/MOC/TwoValues.lean) |
| A first spectrum with one value in all but at most two positions. | Any finite order | [TwoExceptions.lean](Lean/MOC/TwoExceptions.lean) |
| Either spectrum with a repeated value. | Four | [TwoExceptions.lean](Lean/MOC/TwoExceptions.lean) |
| An opposite eigenvalue pair, with $a_i+b_j=0$ for some $i,j$. | Four | [FourCoincidence.lean](Lean/MOC/FourCoincidence.lean) |
| A total rank of at most $n+2$ for $A+tI$ and $B-tI$, for some complex scalar $t$. | Any finite order | [RankSum.lean](Lean/MOC/RankSum.lean) · [RankTwoOverlap.lean](Lean/MOC/RankTwoOverlap.lean) |
| Relative unitary $U=I+(z-1)vv^*$, with $\lVert v\rVert=1$ and $\lvert z\rvert=1$. | Any positive order | [HouseholderSupport.lean](Lean/MOC/HouseholderSupport.lean) |
| A relative unitary with a row or column that has at most two nonzero entries. | Four | [SparseRow.lean](Lean/MOC/SparseRow.lean) · [Small.lean](Lean/MOC/Small.lean) |
| A relative unitary that splits into two blocks of order at most three after independent row and column permutations. | At most six | [Small.lean](Lean/MOC/Small.lean) |
| A relative unitary $U$ for which $U-I$ has zero entries outside a principal block of order at most three. | Any finite order | [IdentityPadding.lean](Lean/MOC/IdentityPadding.lean) · [Small.lean](Lean/MOC/Small.lean) |
| Large shifts $(a-z,b)$ for fixed $a,b,U$, with the trace margin given below. The theorem applies for all sufficiently large $\lvert z\rvert$. | Four | [FourCommonShift.lean](Lean/MOC/FourCommonShift.lean) |

### Sufficient tests

Each test proves MOC for an instance that meets its hypotheses.

| Test | Lean proof |
| --- | --- |
| All real signed determinant weights of $U$ are nonnegative. | [Weights.lean](Lean/MOC/Weights.lean) |
| For every permutation $\sigma$, the matching product has the form $c+\sum_j f(j,\sigma(j))$, with fixed $c$ and $f$. | [Weights.lean](Lean/MOC/Weights.lean) |
| The relative unitary $U$ maximizes the determinant projection in a fixed direction. Its sum is normal and has largest Frobenius norm among the maximizing sums. | [NormalOrbit.lean](Lean/MOC/NormalOrbit.lean) |
| A convex representation of zero gives weights at least $\varepsilon\ge0$ to two matching products $p,q$. Require $\lVert p\rVert+\lVert q\rVert>0$ and $(\lVert p\rVert+\lVert q\rVert)\lvert\det(A+B)\rvert\le\varepsilon\lvert\operatorname{Im}(p\bar q)\rvert$. | [DiskBoundary.lean](Lean/MOC/DiskBoundary.lean) |

For the large-shift case, let $T=\operatorname{tr}(AB)$ and $q_\sigma=\sum_j a_{\sigma(j)}b_j$. The margin requires a $\delta>0$ that applies in every unit direction. For each $\eta$ with $\lvert\eta\rvert=1$, some permutation satisfies $\operatorname{Re}(\eta(T-q_\sigma))\ge\delta$.

The source guide defines the Lean statement and lists equivalent forms and proof reductions. [Source guide](Lean/README.md)

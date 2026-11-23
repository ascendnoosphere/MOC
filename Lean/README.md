# MOC source guide

## Statement

Let $a$ and $b$ be two ordered spectra of length $n$. Let $U$ be the unitary matrix that relates their eigenbases. The proposition `MOC.Holds a b U` states the inclusion below. [Definitions](MOC/Core.lean)

$$
\det\bigl(\mathrm{diag}(a)+U\mathrm{diag}(b)U^*\bigr)
\in \mathrm{conv}_{\mathbb R}
\left\{\prod_{j=1}^{n}(a_{\sigma(j)}+b_j)\mid\sigma\in S_n\right\}.
$$

`MOC.Conjecture (Fin n)` states the inclusion for all spectra and relative unitary matrices of order $n$. `MOC.MOCIsTrue` states the inclusion for every finite order. [Claim](MOC/Claim.lean)

## Equivalent forms and reductions

The [proved cases](../README.md#proved-cases) list the inclusion theorems. The results below give equivalent statements or specify which instances suffice for a proof.

| Reduction | Lean source |
| --- | --- |
| The statement for ordered spectra and a relative unitary is equivalent to the statement for normal matrices with their eigenvalue lists. | [Normal.lean](MOC/Normal.lean) |
| In a positive order, it suffices to prove MOC for spectra with equal traces. | [Core.lean](MOC/Core.lean) |
| It suffices to treat spectra for which all pair sums are nonzero and all matching products are distinct. | [SpectralPerturbation.lean](MOC/SpectralPerturbation.lean) |
| For fixed spectra, it suffices to prove MOC for each relative unitary with no zero entries. One can also impose nonzero pair sums and distinct matching products at the same time. | [FullSupportReduction.lean](MOC/FullSupportReduction.lean) |
| A counterexample of least order has order at least four. No independent row and column permutations give a proper block split of its relative unitary. | [Claim.lean](MOC/Claim.lean) |
| In a counterexample of least order, every row and column has at least three nonzero entries. | [SparseRow.lean](MOC/SparseRow.lean) |
| In a positive order, MOC has an equivalent determinant statement with matching factors $1-x_i y_j$. Set one specified entry of $x$ and one of $y$ to zero. | [Source.lean](MOC/Source.lean) |
| Order $n+1$ is equivalent to a determinant inclusion in order $n$. Use an $n\times(n+1)$ coisometry to compress the second diagonal matrix. Index the matching products by injections into the second spectrum. | [PrincipalCoisometry.lean](MOC/PrincipalCoisometry.lean) |
| After shifting an opposite eigenvalue pair to zero, the determinant hull test reduces to the overlap of the two spectral support spaces. The reduced comparison uses reciprocal nonzero eigenvalues and an explicit real contraction factor. | [OppositePair.lean](MOC/OppositePair.lean) |
| At each order, the Hermitian-by-normal claim is equivalent to MOC for all pairs with either spectrum on a circle or line. | [HermitianByNormal.lean](MOC/HermitianByNormal.lean) |
| For at most $k$ nonreal partner eigenvalues in arbitrary order, it suffices to prove Hermitian-by-normal MOC in orders at most $k$. For $k=5$, the exact remaining cases are orders four and five. | [FiveNonreal.lean](MOC/FiveNonreal.lean) |
| To prove unrestricted Hermitian-by-normal MOC, it suffices to treat orders at least four in which every partner eigenvalue is nonreal. | [FiveNonreal.lean](MOC/FiveNonreal.lean) |
| Order four reduces to the Hermitian-by-normal case and pairs of distinct-entry spectra. In the second case, neither spectrum lies on a circle or line. | [HermitianByNormal.lean](MOC/HermitianByNormal.lean) |
| In order four, MOC is equivalent to the existence of a maximizing normal sum in each direction on each unitary orbit. Requiring such a maximizer in every finite order is equivalent to the unrestricted conjecture. | [NormalSupportMaximum.lean](MOC/NormalSupportMaximum.lean) |
| At a positive Hermitian orbit support maximum with a simple real spectrum, an exact transposition bound relates repeated stationary poles to inverse imaginary minors. A definite partner imaginary part makes the bound strict and forces distinct poles. | [HermitianStationarySwap.lean](MOC/HermitianStationarySwap.lean) |
| In a single complex spectral coordinate, a strict violation can be moved to a maximizer with at least three active permutations if the convex hull of the slopes contains zero in its interior. | [SpectralAffineContact.lean](MOC/SpectralAffineContact.lean) |
| If a fixed unitary and direction give a strict violation in the unit spectral polydisk, some maximum of the support excess there has at least three maximizing permutations. | [PolydiskContact.lean](MOC/PolydiskContact.lean) |
| A regular order-four support gap that dominates a positive multiple of a relabeled mixed profile has at most ten maximizing permutations. | [FourMixedContactBound.lean](MOC/FourMixedContactBound.lean) |
| In order four, the common law for a fixed simple real spectrum follows from weighted permutation support bounds for $1<t\le 2$. Twelve permutation scores determine every score in this family. | [HermitianByNormalFour.lean](MOC/HermitianByNormalFour.lean) · [WeightedDiamondCensus.lean](MOC/WeightedDiamondCensus.lean) |

For $x \ge 0$, all sixteen weighted-diamond forms are nonnegative on the squared minors of an order-four unitary. To prove the support bound it suffices to decompose every nonnegative score gap into these forms and their row relabelings. [HermitianByNormalFourFacets.lean](MOC/HermitianByNormalFourFacets.lean)

The chart $x=u/(1+u)$ with $u>0$ covers the required open parameter interval. Integer coefficient checks certify each added permutation inequality. The twelve pivot evaluations and the first additional inequality have a checked decomposition into sixteen rays. [WeightedDiamondChart.lean](MOC/WeightedDiamondChart.lean) · [WeightedDiamondLowerInitial.lean](MOC/WeightedDiamondLowerInitial.lean)

The remaining ray lists can use bitsets to verify the support antichain and to check groups of non-adjacent crossings with a common third ray. [WeightedDiamondWitnessMasks.lean](MOC/WeightedDiamondWitnessMasks.lean)

The split contrast of a weighted-diamond score has rank at most one. Projected matching products have a split contrast of rank two when both split areas and the support multiplier are nonzero. [FourSpectralSupport.lean](MOC/FourSpectralSupport.lean)

`MOC.HermitianByNormal` states the inclusion for real $a$ and complex $b$. The claim for all orders is open. [Hermitian-by-normal statement](MOC/HermitianByNormal.lean)

## Common permutation weights

A fixed set of real weights works for every complex partner spectrum if it works for all partners with entries in $\{0,1\}$. For real $a$, fix one partner entry at a nonreal value. The same weights work for all partners if they work for every complex choice of the other entries. [CommonWeights.lean](MOC/CommonWeights.lean)

Let one entry of each spectrum vary. A fixed set of real weights works for all values if it works at the four pairs formed by two distinct choices on each side. When the fixed entries are real, choose nonreal $s,u$. The two pairs $(s,u)$ and $(s,\bar u)$ suffice. [TwoFreeEntries.lean](MOC/TwoFreeEntries.lean) · [TwoFreeRealAnchors.lean](MOC/TwoFreeRealAnchors.lean)

For a fixed unitary, one set of weights represents the determinant for every pair of spectra if it represents all the following pairs. Choose index sets $I,J$ of the same size, at most $\lfloor n/2\rfloor$. Set the first spectrum to zero on $I$ and one elsewhere. Set the second spectrum to one on $J$ and zero elsewhere. The corresponding determinant is the squared modulus of the minor on rows $I$ and columns $J$. [SubsetMarkerTest.lean](MOC/SubsetMarkerTest.lean)

At order five, a fixed relative unitary can have no single set of nonnegative weights that sums to one and works for every pair of spectra with an opposite eigenvalue pair at fixed labels. [OppositePair.lean](MOC/OppositePair.lean)

Let $a$, $x$, and $v$ be real lists of length $n$. For a partner of the form $x+zv$, the determinant and the matching products are polynomials in $z$. The coefficient of degree $n$ is the same in all these polynomials. The lower coefficients give a convex-hull test for one set of weights for all complex $z$. If the test holds, at most $n+1$ permutations suffice. The explicit order-five theorem takes membership in this hull as a hypothesis. [HermitianSpectralLine.lean](MOC/HermitianSpectralLine.lean)

## Check the library

Run `lake build` from this directory. The root module imports every project module and checks the axioms used by each safe declaration. The check permits `propext`, `Classical.choice`, and `Quot.sound`. [Build instructions](../README.md#build) · [Root module](MOC.lean)

Use `import MOC` in a Lean file in this package. All proved cases and sufficient tests in the main README are in the audit. To check an individual module, give Lake its module name.

```sh
lake build +MOC.RankTwoOverlap
```

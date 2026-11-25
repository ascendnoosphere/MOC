# Path 12: harmonic dimension of reciprocal overlap objectives

**Status:** exact dimension and cone counterexamples on paper. The general positivity step is open. This is about the linear span of zero-stratum objectives, not the affine dimension of the exact profile locus.

Let P,Q be disjoint support-label sets with sizes p,q. Let 0≤k≤min(p,q). The nonzero padded matching classes are the partial matchings M of size k between P and Q. Use variables xᵢ for P and zⱼ=−yⱼ for Q. The reciprocal matching polynomial of M is

    f_M(x,z) = ∏_{(i,j)∈M} (xᵢ−zⱼ).

The common reciprocal product factor is independent of M, so it does not change the evaluation span on the open set of nonzero shifted spectra. That open set is Zariski dense; an identity there extends to all complex x,z. A possible class of uncovered permutations contributes an additional coordinate identically zero.

## Exact dimension

A polynomial f_M is homogeneous of degree k, multiaffine, and invariant under translating every xᵢ,zⱼ by the same amount. Equivalently it is killed by the lowering operator D = Σᵢ ∂/∂Xᵢ on the m=p+q variables. Filmus–Mossel Lemma 3.7 says the homogeneous harmonic multiaffine space H_k is spanned by products of k differences on arbitrary disjoint pairs. Their Corollary 3.9 gives

    dim H_k = binom(p+q,k) − binom(p+q,k−1).

The following straightening argument is specific to our two blocks and shows that arbitrary pairs can be restricted to cross-pairs without losing span.

Take any disjoint-pair product, with a pairs wholly in P, b wholly in Q and c cross-pairs, so a+b+c=k. Straighten a P-pair and a Q-pair simultaneously:

    (x−x′)(z−z′) = (x−z)(x′−z′) − (x−z′)(x′−z).

This eliminates one pair of each type and preserves the number of occupied labels of either color. Repeat until one of a,b is zero. Suppose a>b initially. There are then a−b P-pairs remaining and q−c−2b≥a−b originally unused Q-labels. Use a different fresh label z for each remaining P-pair in

    x−x′ = (x−z) − (x′−z).

No monomial spoils matching disjointness. The b>a case is symmetric. Each resulting term is a cross-pair product. It follows that span{f_M}=H_k. This works over either ℝ or ℂ; the published harmonic spanning statement and dimension hold in characteristic zero. At k=0 the space consists of constants on cover classes.

The linear span of the profile vectors (f_M(x,z)) has the same dimension: a vector orthogonal to all evaluations is exactly a linear dependence among the f_M. Over ℝ, real x,z suffice by polynomial identity. Adding complex spectra and taking real parts over all support phases cannot enlarge that real span, because the coefficient matrix is real.

In the square full-overlap case p=q=k this recovers the Catalan dimension. When p=q=5 and k=2, the general cover-class count is 200, while the exact linear dimension is binom(10,2)−binom(10,1)=35. No numerical rank computation is needed.

For a lossless coordinate choice, use Boolean endpoints of Hamming weight k. A homogeneous squarefree polynomial evaluated at the indicator of a k-set gives that monomial's coefficient. Here its value is zero unless that k-set selects one endpoint of each paired edge; its sign is (−1)^(number chosen in Q). Thus the ordinary signed endpoint markers suffice, but live in the smaller harmonic subspace.

## Positivity does not follow from the diagram algebra

Let ρ be the natural unitary permutation representation on subsets (binary tensor basis). Its matrix coefficients are exactly the ordinary subset markers. Classical Schur–Weyl or Temperley–Lieb compresses this representation, and Speck's Theorem 2.2.31 describes its common kernel. Neither operation turns pointwise nonnegativity on permutations into positive-semidefinite positivity on matrix blocks.

For an exact symbolic witness, let v=(e_i−e_j)/√2 in the singleton summand and let τ swap i,j. With A=vv*, the marker-linear function f_A(σ)=tr(Aρ(σ)) has f_A(τ)=−1, despite A≽0. Conversely g(σ)=(1−⟨v,ρ(σ)v⟩)/2 is pointwise nonnegative (the representation and v are real, and Cauchy–Schwarz gives the bound), but g(1)=0 and g(τ)=1. No PSD A in any faithful direct-sum realization can represent g as tr(Aρ(σ)): g(1)=tr A=0 forces A=0. Thus the pointwise nonnegative cone and the PSD-coefficient cone are incomparable. This is an obstruction to that proposed positivity inference, not a statement that all other diagram cones fail.

Classical positivity of every simultaneous unitary marginal is separately obstructed by the repository's exact independent-crossing and uniform flat-reflection results. Those obstructions do not preclude an objective-dependent certificate. No new valid generator outside the ordinary marker cone, or proof of the full terminal bound, is asserted here.

## Primary sources and scope

- Filmus and Mossel, [Harmonicity and invariance on slices of the Boolean cube](https://arxiv.org/abs/1507.02713), Lemma 3.7 and Corollary 3.9, journal DOI [10.1007/s00440-019-00900-w](https://link.springer.com/article/10.1007/s00440-019-00900-w). Provides the harmonic spanning and dimension, not the bipartite straightening for spectral overlap or a positivity result.
- Filmus, [An Orthogonal Basis for Functions over a Slice of the Boolean Hypercube](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v23i1p23), DOI [10.37236/4567](https://doi.org/10.37236/4567). Gives an explicit orthogonal basis of the multiaffine harmonic space.
- Flores and Peltola, [Higher-spin quantum and classical Schur-Weyl duality for sl2](https://arxiv.org/abs/2008.06038), preprint DOI [10.48550/arXiv.2008.06038](https://doi.org/10.48550/arXiv.2008.06038). Commutant and diagram-algebra identifications; no classical simultaneous marginal law.
- Matthew Speck, [Determinants of Sums of Normal Matrices](https://etd.auburn.edu/handle/10415/9283), Auburn 2024, Theorem 2.2.31. The kernel is spanned by left-right translates of the three-label alternator. The author is Matthew, and the institutional record does not list a DOI.

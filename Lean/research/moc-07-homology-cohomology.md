# Marcus-de Oliveira formulations: Homology and cohomology

Atlas entries 073–084.

All finite eigenvalue lists include multiplicities unless stated otherwise. $`S_n`$ denotes the permutations of $`\{1,\ldots,n\}`$; $`U(n)`$ denotes the unitary group; $`*`$ denotes the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. An overline denotes closure. The original conjecture asserts that the determinant of a sum of two normal complex matrices with fixed eigenvalues is in the convex hull of the products of their pairwise matched eigenvalue sums. The statements below specify the operator, invariant and comparison data in each setting. New extensions require proof; an additional realization or finite spectral window is part of the statement when no intrinsic scalar determinant exists.

## Complex spectral form and equivalence

The following statement is part of each numbered formulation. Use the finite spectral realization specified in that entry. For continuous spectral data use a finite sample or a finite spectral resolution. For infinite-dimensional data use a finite spectral subspace. If an entry has fixed rank, take finite direct sums of its realizations and select the required number of modes. When the datum is not a linear operator, use one orthogonal complex coordinate for each selected occurrence of the datum.

Let the two selected spaces have the same positive dimension $`N`$. Choose orthonormal spectral bases in these spaces, with rank-one projections $`P_j,Q_j`$ onto the basis lines. In a repeated eigenspace, choose an orthonormal basis to distinguish its occurrences. Denote the associated scalar or labelled spectral data by $`s_j,t_j`$, respectively. Let $`f,g`$ be arbitrary complex-valued functions of the labelled data $`(s_j,j)`$ and $`(t_j,j)`$. Set

```math
A_f=\sum_{j=1}^N f(s_j,j)P_j,\qquad B_g=\sum_{j=1}^N g(t_j,j)Q_j.
```

For every unitary identification $`U`$ of the second selected space with the first, the conjecture is

```math
\det(A_f+UB_gU^*)\in\mathrm{conv}\left\{\prod_{j=1}^N\big(f(s_j,j)+g(t_{\pi(j)},\pi(j))\big):\pi\in S_N\right\}.
```

The permutation weights may depend on both evaluations and on $`U`$. If the spectra are simple, the occurrence labels are unnecessary: functions of the spectral values suffice.

The forward implication follows from normality of the two diagonal spectral evaluations. For the reverse implication, take any two normal complex matrices of order $`N`$ and list their eigenvalues in orthonormal eigenbases. Select $`N`$ modes in the stated realization of each object and assign these eigenvalues to the two lists through $`f`$ and $`g`$. The relative unitary is unrestricted. The determinant and every permutation product then agree with the original matrix conjecture. Thus the complex spectral form, with all finite ranks and evaluations, is equivalent in both directions. Direct sums and arbitrary unitary mixing here concern the selected linear realizations, not necessarily operations on the native objects. The specific reverse reductions below avoid the extra labels or sums when possible. The native determinant, norm, volume or signed invariant is retained in each entry; an intrinsic comparison not given by this matrix realization requires its own justification.

## 073 Chain complexes

Let $`(C_\bullet,d)`$ be a complex of complex vector spaces, with a finite-dimensional term $`C_k`$ of dimension $`n>0`$ and a fixed Hermitian inner product there. Let $`f,g`$ be degree-preserving chain endomorphisms (they commute with the differential). Require their maps $`f_k,g_k`$ on $`C_k`$ to be normal, with eigenvalues $`\lambda_j,\mu_j`$. For every unitary $`U:C_k\to C_k`$,

```math
\det(f_k+Ug_kU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

If $`U`$ extends to a unitary chain automorphism the sum is the degree-$`k`$ component of a chain map. The general degreewise comparison requires no such extension.

**Equivalence reduction.** Take the chain complex concentrated in degree k, with zero differential and chain space of dimension n. All normal linear endomorphisms are chain endomorphisms there. This recovers the original conjecture.

## 074 Singular homology

Let $`X`$ be a space with finite positive Betti number $`n=\dim_{\mathbb C}H_k(X;\mathbb C)`$. Let $`f,g:X\to X`$ be continuous maps inducing normal endomorphisms $`F=f_{*,k},G=g_{*,k}`$ of the homology space for a fixed Hermitian product. Let $`\lambda_j,\mu_j`$ be their eigenvalues. For every unitary $`U`$ on $`H_k(X;\mathbb C)`$,

```math
\det(f_{*,k}+Ug_{*,k}U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This uses the induced linear maps, not a pointwise sum of continuous maps of spaces.

**Equivalence reduction.** Take a wedge of n circles and a self-map acting by distinct integer degrees on the respective loops. Its first homology has n spectral lines. Complex spectral evaluation on those lines and unrestricted relative unitary position recover arbitrary normal pairs.

## 075 Singular cohomology

Let $`X`$ have finite positive $`n=\dim H^k(X;\mathbb C)`$ and let $`f,g:X\to X`$ induce normal pullbacks $`f^{*,k},g^{*,k}`$ for a fixed Hermitian inner product. List the eigenvalues of the two pullbacks as $`\lambda_j,\mu_j`$. For each unitary $`U`$ on $`H^k(X;\mathbb C)`$,

```math
\det(f^{*,k}+Ug^{*,k}U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

Over a field the cohomological pullback is the linear dual of the homological pushforward under the evaluation pairing. The linear dual preserves determinant and characteristic roots.

**Equivalence reduction.** Use the first cohomology of a wedge of n circles with maps of distinct integer degrees on the loops. The dual action has the same eigenvalues. Apply arbitrary complex functions to them and allow arbitrary cohomology-space unitaries.

## 076 Simplicial homology

Let $`K`$ be a finite simplicial complex, with its oriented $`k`$-simplex basis orthonormal. Let $`A=\partial_{k+1}\partial_{k+1}^*+\partial_k^*\partial_k`$ be its simplicial Laplacian on $`C_k(K;\mathbb C)`$ of dimension $`n>0`$. Let $`B`$ be a second Laplacian on the same chain space, for example from a second choice of weights with compatible adjoints. If $`\lambda_j,\mu_j`$ are the nonnegative spectra including zero, then for all unitary $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

A pseudodeterminant comparison instead requires restriction to a specified common positive invariant subspace. Harmonic zero modes encode homology and must not be silently removed from the full determinant.

**Equivalence reduction.** Use a finite simplicial chain space with at least n orthogonal Laplacian modes. Select n modes, retain their multiplicities by labelled lines if necessary, and evaluate arbitrary complex functions on those modes. The comparison is on the chosen chain-space block.

## 077 Cellular homology

Let $`X`$ be a finite CW complex and let $`f,g:X\to X`$ be cellular maps. On the $`n`$ dimensional cellular chain space $`C_k(X;\mathbb C)`$, with oriented cells as an orthonormal basis, assume the induced cellular chain maps $`F_k,G_k`$ are normal. Let $`\lambda_j,\mu_j`$ list their spectra. For every unitary $`U`$ of that chain space,

```math
\det(F_k+UG_kU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The dimension is the cell count in degree $`k`$, not necessarily the cellular homology rank.

**Equivalence reduction.** Use the cellular chain complex of a wedge of n circles, with one loop for each basis vector. Cellular self-maps of distinct integer degrees induce diagonal operators with distinct eigenvalues in degree one. Apply complex functions and full unitary mixing there.

## 078 De Rham cohomology

Let $`M`$ be a closed Riemannian manifold and $`f,g:M\to M`$ smooth maps. Fix $`k`$ with $`n=\dim H^k_{\mathrm{dR}}(M;\mathbb C)>0`$. Use the Hermitian inner product from harmonic representatives. Assume the induced pullbacks $`F=f^*,G=g^*`$ on cohomology are normal. For their eigenvalues $`\lambda_j,\mu_j`$ and every unitary $`U`$ on the cohomology space,

```math
\det(F+UGU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The maps are on cohomology classes, not on the infinite-dimensional space of all differential forms.

**Equivalence reduction.** Use a disjoint union of n closed manifolds, with constant modes in degree zero, or any compact manifold with a cohomology group of dimension at least n. Refine its cohomology eigenspaces into lines and apply complex evaluations of the selected labelled modes.

## 079 Dolbeault cohomology

Let $`X`$ be a compact complex manifold and $`f,g:X\to X`$ holomorphic maps. For fixed $`(p,q)`$ with $`n=h^{p,q}>0`$, let $`F,G`$ be their induced pullbacks on the finite-dimensional complex Dolbeault group $`H^{p,q}_{\bar\partial}(X)`$. Choose a Hermitian product for which $`F,G`$ are normal, and let $`\lambda_j,\mu_j`$ be their eigenvalues. For every unitary $`U`$ on this group,

```math
\det(F+UGU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The conjecture is degreewise in both holomorphic and antiholomorphic degree.

**Equivalence reduction.** Use a compact complex manifold with a Dolbeault group of dimension at least n, for example a disjoint union of n points in degree (0,0). Choose labelled orthogonal cohomology lines and complex evaluations on them.

## 080 Hodge theory

Let $`M`$ be a closed Riemannian manifold. Fix degree $`k`$ and two Hodge Laplacians $`\Delta_1,\Delta_2`$ for chosen metrics on $`k`$-forms. Select $`n>0`$ positive eigenmodes of each and let $`E_1,E_2`$ be the resulting finite Hilbert spaces, with eigenvalues $`\lambda_j,\mu_j`$. For each unitary identification $`U:E_2\to E_1`$,

```math
\det_{E_1}(\Delta_1|_{E_1}+U\Delta_2|_{E_2}U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The positive spectral-block determinant excludes the harmonic modes. It is not the zeta-regularized determinant of an infinite Hodge Laplacian.

**Equivalence reduction.** Use finite Hodge eigenmode spaces with at least n positive modes. Complex spectral evaluations of n selected modes give every normal pair. Neither the harmonic kernel nor the analytic continuation of the zeta determinant is needed for this converse.

## 081 Intersection homology

Let $`X`$ be a compact stratified pseudomanifold, fix a perversity $`\bar p`$ and degree $`k`$, and suppose $`V=IH_k^{\bar p}(X;\mathbb C)`$ has dimension $`n>0`$. Choose maps inducing endomorphisms $`F,G`$ on this group (for example suitable stratum-preserving isomorphisms). Require $`F,G`$ normal for a chosen Hermitian product. For their eigenvalues $`\lambda_j,\mu_j`$ and every unitary $`U`$ on $`V`$,

```math
\det_V(F+UGU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The choice of functorial maps and perversity is necessary before these operators are defined.

**Equivalence reduction.** For a smooth compact manifold the middle-perversity intersection homology agrees with ordinary homology. Use a finite direct sum of such homology realizations and select n spectral lines, then take arbitrary complex evaluations.

## 082 Group homology

Let $`G`$ be a group and $`W`$ a complex $`G`$-module. Fix $`k`$ with $`V=H_k(G,W)`$ finite-dimensional of dimension $`n>0`$. Take two compatible endomorphisms of the group-module data inducing $`F,G_0:V\to V`$. Assume normality for a fixed Hermitian structure and enumerate their eigenvalues $`\lambda_j,\mu_j`$. For every unitary $`U`$ on $`V`$,

```math
\det_V(F+UG_0U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

For instance equivariant maps of the coefficient module induce such endomorphisms. No arbitrary group endomorphism is assumed to act on fixed coefficients without compatibility.

**Equivalence reduction.** Take the trivial group and a complex coefficient module of dimension n in homological degree zero. The induced maps are arbitrary coefficient endomorphisms. Thus every normal matrix pair occurs without further spectral evaluation.

## 083 Group cohomology

Let $`G`$ be a group and $`W`$ a complex $`G`$-module with $`V=H^k(G,W)`$ of finite positive dimension $`n`$. Let two compatible coefficient or group-coefficient maps induce normal endomorphisms $`F,G_0`$ of $`V`$ with respect to a fixed Hermitian inner product. For their eigenvalues $`\lambda_j,\mu_j`$ and all unitary $`U:V\to V`$,

```math
\det_V(F+UG_0U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The maps must be defined on the same cohomology degree and coefficients.

**Equivalence reduction.** Take the trivial group with an n-dimensional complex coefficient module in cohomological degree zero. All linear coefficient maps act on this group, so every normal pair occurs.

## 084 Sheaf cohomology

Let $`\mathcal F`$ be a sheaf of complex vector spaces on $`X`$ with $`V=H^k(X,\mathcal F)`$ of finite positive dimension $`n`$. Let $`f,g:\mathcal F\to\mathcal F`$ be sheaf endomorphisms inducing normal linear maps $`F=H^k(f),G=H^k(g)`$ on $`V`$, for a chosen Hermitian product. For their eigenvalues $`\lambda_j,\mu_j`$ and any unitary $`U`$ on $`V`$,

```math
\det_V(H^k(f)+UH^k(g)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This statement uses the ordinary finite-dimensional cohomological determinant, not a scalar invariant of an arbitrary sheaf.

**Equivalence reduction.** Take a one-point space and a sheaf with stalk of dimension n. Its degree-zero cohomology is the stalk, and arbitrary normal sheaf endomorphisms give the matrix conjecture.


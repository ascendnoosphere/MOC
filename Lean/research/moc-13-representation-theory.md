# Marcus-de Oliveira formulations: Representation theory and harmonic analysis

Atlas entries 148–159.

All eigenvalue lists use the indicated multiplicities. $`S_n`$ is the set of permutations of $`\{1,\ldots,n\}`$; $`U(n)`$ is the complex unitary group; $`*`$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. The classical conjecture compares the determinant of a sum of two normal operators with the convex hull of products of matched eigenvalue sums. The following statements specify scalar realizations when the native objects are not complex operators. The chosen realizations and all rank conditions are part of the hypotheses.

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

## 148 Finite group representations

Let $`\rho,\eta`$ be complex representations of a finite group $`G`$ on Hilbert spaces of equal dimension $`n>0`$, with group-invariant Hermitian products. For $`g,h\in G`$, put $`A=\rho(g)`$ and $`B=\eta(h)`$; both are unitary. Let $`\lambda_j,\mu_j`$ be their eigenvalues, roots of unity with multiplicity. For every unitary identification $`U`$,

```math
\det(\rho(g)+U\eta(h)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The individual traces are character values. The statement compares sums of group actions, not the character of the group product.

**Equivalence reduction.** Use a cyclic group of order at least n and a direct sum of n distinct one-dimensional characters. At a generator their values are distinct roots of unity; complex spectral functions assign arbitrary values to them.

## 149 Lie algebra representations

Let $`V,W`$ be finite-dimensional complex weight representations of a semisimple complex Lie algebra with a fixed Cartan subalgebra $`\mathfrak h`$ and equal dimension $`n`$. List the weights $`a_j,b_j\in\mathfrak h^*`$ by weight multiplicity. Choose Hermitian products with orthogonal weight spaces. For every $`h\in\mathfrak h`$ the actions $`A=\rho_V(h)`$ and $`B=\rho_W(h)`$ are normal with eigenvalues $`a_j(h),b_j(h)`$. For every unitary identification $`U`$,

```math
\det(\rho_V(h)+U\rho_W(h)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(a_j(h)+b_{\pi(j)}(h)):\pi\in S_n\right\}.
```

The determinant representation of the associated torus has weight equal to the sum of the individual weights. The scalar product comparison is at the chosen Cartan element.

**Equivalence reduction.** Use a representation with n distinct weights for a fixed Cartan element, or select n weight occurrences from a direct sum of weight representations. Evaluate arbitrary complex functions on the selected scalar weight values instead of requiring linear evaluation.

## 150 Highest-weight theory

Let $`V_\lambda,V_\mu`$ be irreducible finite-dimensional representations of a connected compact Lie group with highest weights $`\lambda,\mu`$ and common dimension $`n`$. Fix a maximal torus and list all weights $`a_j,b_j`$ including multiplicities, not only the Weyl-orbit vertices. For each torus element $`t`$ let $`A(t),B(t)`$ be the represented unitary actions. For every unitary identification $`U`$,

```math
\det(A(t)+UB(t)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(a_j(t)+b_{\pi(j)}(t)):\pi\in S_n\right\}.
```

Here $`a_j(t),b_j(t)`$ are unit-circle character values. Weyl dimension supplies $`n`$; the highest-weight polytope alone does not supply the weight multiplicities.

**Equivalence reduction.** Use the n-dimensional irreducible representation of SU(2). Its torus weights are distinct and a generic torus element separates their character values. Arbitrary complex functions on those values and unrestricted relative unitaries give every matrix spectrum.

## 151 Root systems

Let $`\Phi,\Psi`$ be reduced crystallographic root systems of equal cardinality $`n>0`$, with roots enumerated as $`a_j,b_j`$. Fix real-linear scalar evaluations $`L_\Phi,L_\Psi`$ of their root spaces into $`\mathbb C`$. On the root-indexed Hilbert spaces define diagonal normal operators $`A e_j=L_\Phi(a_j)e_j`$ and $`B f_j=L_\Psi(b_j)f_j`$. For each unitary identification $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(L_\Phi(a_j)+L_\Psi(b_{\pi(j)})):\pi\in S_n\right\}.
```

The root sums vanish in both systems. The determinant of the root-value operator is not the Cartan matrix determinant, and $`n`$ is root count rather than root-system rank.

**Equivalence reduction.** Use root systems of sufficiently large cardinality and choose n distinct roots. A generic real-linear scalar evaluation separates the selected roots. Apply arbitrary complex functions to these scalar data, not just a fixed linear functional.

## 152 Weyl group representations

Let $`W`$ be a Weyl group acting on a real Euclidean reflection space of dimension $`n>0`$. Let $`w,v\in W`$ act by orthogonal matrices $`A,B`$. Their complex eigenvalues $`\lambda_j,\mu_j`$ are roots of unity. For every orthogonal $`Q`$ on the reflection space, or every unitary $`U`$ on its complexification,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The determinants of the inputs are their sign characters. The full permutation set refers to the eigenvalue list, not just the permutations available from Weyl-group elements.

**Equivalence reduction.** Use a Weyl group of sufficiently large rank and its reflection representation. Refine any repeated reflection eigenvalues into orthogonal labelled modes, or choose distinct eigenmodes of suitable elements. Use n such modes with arbitrary complex evaluation and full complex unitary mixing.

## 153 Compact-group harmonic analysis

Let $`G`$ be a compact group and $`\rho`$ an irreducible unitary representation of dimension $`n>0`$. For integrable functions $`f,g`$ on $`G`$ define Fourier matrices $`A=\int_G f(x)\rho(x)^*\,dx`$, $`B=\int_G g(x)\rho(x)^*\,dx`$ using normalized Haar measure. Require $`A,B`$ normal, and let $`\lambda_j,\mu_j`$ be their eigenvalues in this block. For every unitary $`U\in U(n)`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The comparison is within a Peter-Weyl block. Infinite sums over irreducible representations require additional determinant summability conditions.

**Equivalence reduction.** Use a compact group with an irreducible unitary representation of dimension n, for example the n-dimensional representation of SU(2). By Schur orthogonality its Fourier coefficients can realize every matrix in that block. Choose the normal ones to recover the original conjecture.

## 154 Abelian Fourier analysis

Let $`G`$ be a locally compact abelian group and let $`f,g`$ be bounded real positive Fourier multiplier symbols on its character group, restricted to a measurable region with a specified probability measure $`\nu`$. Assume they are bounded away from zero. Let $`\mu_f,\mu_g`$ be their pushforward laws and $`\Gamma`$ their probability couplings. The Fourier geometric determinant $`D(h)=\exp\int\log h\,d\nu`$ satisfies

```math
D(f+g)\in\left[\inf_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma,\ \sup_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma\right].
```

The common Fourier variable supplies a coupling. For finite equal-mass frequencies, permutation matchings give the extreme products. The infinite Haar measure is not normalized without a finite measure choice.

**Equivalence reduction.** Use a finite abelian group with n frequencies and the finite Fourier multiplier realization. Arbitrary complex values on those frequencies give arbitrary diagonal normal matrices; allow all relative unitary positions of the two multipliers.

## 155 Hecke algebras

Let $`\mathcal H`$ be a Hecke algebra acting on a finite-dimensional Hilbert space $`V`$ of automorphic forms of dimension $`n>0`$. Let $`T,S\in\mathcal H`$ act by normal operators $`A,B`$ on $`V`$, for instance elements in an adjoint-closed commuting Hecke algebra. Let $`\lambda_j,\mu_j`$ be their Hecke eigenvalues. For every unitary $`U`$ of $`V`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

For commuting Hecke actions the identity relative position is a permutation value. General $`U`$ need not intertwine the Hecke algebra.

**Equivalence reduction.** Use a finite Hilbert realization of a commuting Hecke action, and select n joint spectral lines, with labels on repeated eigenvalues. Take arbitrary complex functions on those joint eigencharacters and all relative unitary identifications of the selected lines.

## 156 Satake parameters

Let $`s,t`$ be semisimple Satake conjugacy parameters in a complex dual reductive group. Fix a finite-dimensional complex representation $`r`$ of the dual group of dimension $`n`$. Choose normal representatives $`A,B`$ of the conjugacy classes of $`r(s),r(t)`$, with eigenvalues $`\lambda_j,\mu_j`$ in orthonormal eigenbases. For each unitary $`U`$ and $`z\in\mathbb C`$,

```math
\det(I-z(A+UBU^*))\in\mathrm{conv}\left\{\prod_{j=1}^n(1-z(\lambda_j+\mu_{\pi(j)})):\pi\in S_n\right\}.
```

The local Euler determinant is evaluated in the chosen representation; its eigenvalues include weight multiplicities. The sum is not required to arise from another dual-group element.

**Equivalence reduction.** Use the standard representation of the complex dual group GL(n) with semisimple diagonal parameters. Its eigenvalues can be arbitrary nonzero complex lists. At a fixed nonzero characteristic parameter, affine changes and continuity give every original determinant instance.

## 157 Tensor categories of representations

Let $`\mathcal C`$ be a tensor category equipped with a complex linear realization functor to finite-dimensional Hilbert spaces. Choose objects $`X,Y`$ with realized dimension $`n>0`$ and endomorphisms $`f,g`$ whose realized maps $`A,B`$ are normal. Let $`\lambda_j,\mu_j`$ be the eigenvalues in the realization. For every unitary $`U`$ between the realized spaces,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The determinant is the ordinary scalar on the top exterior power of the realized space. A quantum or categorical dimension is not used as an integer permutation length unless the realization identifies it with that length.

**Equivalence reduction.** Use the tensor category of finite-dimensional complex representations of the trivial group. Its realization is the category of complex vector spaces, and all normal endomorphism pairs are available in each dimension.

## 158 Association schemes

Let two association schemes have the same number $`n>0`$ of vertices. In their complex Bose-Mesner algebras choose elements $`A=\sum_i a_i A_i`$, $`B=\sum_i b_i B_i`$, where the adjacency matrices form commuting adjoint-closed algebras. They are normal. Let the eigenvalues of each algebra element be listed using its eigenmatrix entries with the multiplicities of the primitive idempotents. Denote the lists by $`\lambda_j,\mu_j`$. For every unitary identification $`U`$ of vertex spaces,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The hull uses the vertex-space spectral length, not the number of distinct adjacency classes. The sum need not be an adjacency matrix of a scheme.

**Equivalence reduction.** Use the association scheme of a finite cyclic group with one adjacency class for each group element. The commuting Fourier blocks have n one-dimensional joint spectral spaces, and arbitrary complex linear combinations of adjacency matrices prescribe arbitrary diagonal eigenvalues.

## 159 Spherical harmonic analysis

On the unit sphere $`S^r`$, $`r\ge1`$, the nonnegative Laplace eigenvalue of degree $`\ell`$ is $`\ell(\ell+r-1)`$ with its spherical-harmonic multiplicity. Choose two finite sums of harmonic eigenspaces (possibly on spheres of different dimensions) having the same positive total dimension $`n`$. Let $`A,B`$ be their restricted Laplace operators, with eigenvalue lists $`\lambda_j,\mu_j`$ including the full selected multiplicities. For every unitary identification $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The determinant is over the chosen harmonic spectral windows. The complete heat trace and zeta determinant need separate infinite-dimensional regularization.

**Equivalence reduction.** Choose sufficiently many finite spherical-harmonic modes, including their multiplicities. Evaluate arbitrary complex functions on n distinct degree values if possible, or use the labelled spectral basis when multiplicities repeat.


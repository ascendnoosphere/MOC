# Marcus-de Oliveira formulations: Differential geometry, curvature and local geometry

Atlas entries 099–111.

All finite eigenvalue lists include multiplicities unless stated otherwise. $`S_n`$ denotes the permutations of $`\{1,\ldots,n\}`$, $`U(n)`$ the unitary group, $`*`$ the Hermitian adjoint and $`\mathrm{conv}`$ the real-affine convex hull. For normal complex operators $`A,B`$ of order $`n`$, the Marcus-de Oliveira conjecture compares $`\det(A+UBU^*)`$ with the products $`\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)})`$ of matched eigenvalue sums. The statements below specify the required operator and determinant for each object. An auxiliary realization is part of a formulation where the object itself has no scalar determinant.

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

## 099 Euclidean linear deformation

Let $`F,G:\mathbb R^n\to\mathbb R^n`$ be linear deformations. Let $`A=(F^TF)^{1/2}`$, $`B=(G^TG)^{1/2}`$ be their positive stretch operators with principal stretches $`\lambda_j,\mu_j\ge0`$. For every orthogonal $`Q`$,

```math
\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This is the unsigned Jacobian of the combined stretch operator. It does not assert a bound for the oriented determinant of $`F+QGQ^T`$ from singular values alone.

**Equivalence reduction.** Use diagonal linear deformations with distinct positive principal stretches. Their positive stretch operators have arbitrary positive simple spectra. Apply complex functions before the sum and allow unrestricted complex unitary identifications.

## 100 Affine geometry

Let $`f(x)=Ax+a`$ and $`g(x)=Bx+b`$ be affine maps of a complex affine space with a fixed Hermitian inner product on its translation space of dimension $`n`$. Assume $`A,B`$ normal with eigenvalues $`\lambda_j,\mu_j`$. For every unitary $`U`$ of the translation space,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

Translation parts do not affect the affine volume multiplier. The left side is the determinant of the linear part of the sum after identification of the affine origin.

**Equivalence reduction.** Already equivalent on complex affine spaces: any normal matrix is the linear part of a linear affine map, with its translation part set to zero.

## 101 Projective geometry

Let $`f,g`$ be projective linear transformations of $`\mathbb P(\mathbb C^n)`$. Fix invertible normal linear lifts $`A,B\in GL_n(\mathbb C)`$, including a specified choice of their nonzero scalar factors. Let $`\lambda_j,\mu_j`$ be the eigenvalues of those lifts. For every unitary $`U`$ on the lift space,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The scalar is a lift-dependent determinant. Projective eigenvalue ratios do not determine it without the lift normalization, and the sum can be singular.

**Equivalence reduction.** Use arbitrary invertible normal lifts of projective transformations. These realize arbitrary nonzero complex spectra. The general result with zeros follows by continuity of the determinant and the finitely many vertex products under scalar perturbations. Keep the lift normalization fixed.

## 102 Differential topology

Let $`f,g:M\to M`$ be smooth maps of an $`n`$ dimensional manifold with a common fixed point $`x`$. Fix an inner product on $`T_xM`$. Assume the complexified derivatives $`A=df_x,B=dg_x`$ are normal with eigenvalues $`\lambda_j,\mu_j`$. For every orthogonal $`Q:T_xM\to T_xM`$,

```math
\det(I-A-QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^n(1-\lambda_j-\mu_{\pi(j)}):\pi\in S_n\right\}.
```

The determinant is the local fixed-point index determinant for a map whose linearization is $`A+QBQ^T`$; its sign gives the index if that determinant is nonzero. This does not define a global sum of manifold maps.

**Equivalence reduction.** Every real linear map is a derivative at a fixed point of a smooth linear map of Euclidean space. Use real diagonal derivatives with distinct eigenvalues, complex spectral evaluations on their complexification, and the affine characteristic determinant with arbitrary unitary positions. A scalar shift removes the identity.

## 103 Riemannian geometry

Let $`g_0,g_1,g_2`$ be positive Riemannian metrics at a point of an $`n`$ dimensional manifold. On the tangent space with metric $`g_0`$ define positive endomorphisms $`A=g_0^{-1}g_1`$, $`B=g_0^{-1}g_2`$ by $`g_0(Ax,y)=g_1(x,y)`$ and the corresponding rule for $`B`$. Let $`\lambda_j,\mu_j>0`$ be their eigenvalues. For every $`g_0`$-orthogonal $`Q`$,

```math
\det(A+QBQ^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The square root is the ratio of the volume density of the metric $`g_1+g_2(Q^{-1}\cdot,Q^{-1}\cdot)`$ to that of $`g_0`$. Its bounds are the positive square roots of the extreme permutation products.

**Equivalence reduction.** Use positive diagonal metrics relative to the standard Euclidean metric on an n-dimensional tangent space. Apply arbitrary complex functions to the distinct relative metric eigenvalues. The complex determinant is the exact form; the real volume density remains its positive specialization.

## 104 Pseudo-Riemannian geometry

Let $`g_0`$ be a nondegenerate symmetric form of signature $`(p,q)`$ on a real space of dimension $`n=p+q`$, and let $`A=g_0^{-1}g_1`$, $`B=g_0^{-1}g_2`$ for two other nondegenerate symmetric forms. Fix a positive Hermitian inner product on the complexification for which $`A,B`$ are normal. For their complex eigenvalues $`\lambda_j,\mu_j`$ and every unitary $`U`$ for this positive inner product that also preserves the complex bilinear extension of $`g_0`$,

```math
\det(A+UBU^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

Self-adjointness for an indefinite metric alone does not imply normality for a positive inner product. The determinant may have either real sign for real $`U`$; no positivity is assumed.

**Equivalence reduction.** The positive-signature case contains arbitrary positive relative metric eigenvalues. At fixed indefinite signature use diagonal real endomorphisms in a pseudo-orthonormal frame, with distinct nonzero entries, and evaluate complex functions on the complexified tangent lines. Allow arbitrary complex unitary positions in this realization rather than only indefinite isometries.

## 105 Hypersurface geometry

Let two hypersurface second fundamental forms at a common identified $`n`$ dimensional Euclidean tangent space have self-adjoint shape operators $`A,B`$. Their principal curvatures are $`\lambda_j,\mu_j`$ with multiplicity. For every orthogonal $`Q`$,

```math
\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This is the Gauss-Kronecker curvature of the combined shape operator, when that operator is realized by a hypersurface. Its trace is the sum of principal curvatures, not the determinant.

**Equivalence reduction.** At a point a graph of a quadratic real function with zero first derivative has the specified symmetric Hessian as its shape operator. Choose distinct real curvatures, evaluate arbitrary complex functions, and use the complexified tangent space.

## 106 Ricci geometry

Fix a positive metric $`g`$ at a point of an $`n`$ dimensional manifold and two symmetric Ricci tensors $`R_1,R_2`$ on that tangent space. Let $`A=g^{-1}R_1`$, $`B=g^{-1}R_2`$ and let $`\lambda_j,\mu_j`$ be their real Ricci eigenvalues. For each $`g`$-orthogonal $`Q`$,

```math
\det(A+QBQ^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The trace is the scalar curvature of the combined tensor relative to $`g`$. The bound concerns the determinant of its Ricci endomorphism, whether or not the combined tensor is globally realizable.

**Equivalence reduction.** Use diagonal symmetric Ricci tensors in a fixed positive metric, with distinct real eigenvalues. For arbitrary order use the finite complex spectral coordinates of these tensors, not a global realization by a metric with prescribed Ricci curvature.

## 107 Curvature operator

Let $`V`$ be a real Euclidean space of dimension $`r\ge2`$ and let $`A,B`$ be self-adjoint algebraic curvature operators on $`\bigwedge^2 V`$, defined using the curvature tensor and the induced inner product. Put $`n=\binom r2`$ and let $`\lambda_j,\mu_j`$ be the eigenvalues. For every orthogonal $`Q`$ on $`\bigwedge^2 V`$,

```math
\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

If $`Q=\bigwedge^2 q`$ for an orthogonal $`q`$ on $`V`$, the transformed curvature operator retains the algebraic curvature symmetries. The trace is half the scalar curvature in the usual convention.

**Equivalence reduction.** Choose a curvature operator diagonal on coordinate bivectors, with freely specified diagonal sectional curvatures; these diagonal operators satisfy the algebraic curvature symmetries. Select n coordinate bivectors in sufficiently large dimension and evaluate arbitrary complex functions on their spectral modes.

## 108 Kähler geometry

Let $`h_0,h_1,h_2`$ be positive Hermitian metrics on the complex tangent space of a Kähler manifold at a point, with complex dimension $`n`$. Put $`A=h_0^{-1}h_1`$, $`B=h_0^{-1}h_2`$. For their positive Hermitian eigenvalues $`\lambda_j,\mu_j`$ and every $`h_0`$-unitary $`U`$,

```math
\det_{\mathbb C}(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This complex determinant is the volume-density ratio of the combined Hermitian metric relative to $`h_0`$ (with the same complex orientation). The real tangent dimension is $`2n`$.

**Equivalence reduction.** Use positive diagonal Hermitian metrics relative to a fixed standard Hermitian metric on a complex vector space of arbitrary dimension. Complex functions on the distinct relative eigenvalues recover all normal spectra.

## 109 Finsler geometry

Let $`F_0,F_1,F_2`$ be strongly convex Finsler metrics. At a fixed nonzero tangent vector $`v`$, their fundamental tensors are $`g_i(v)=\frac12 D_v^2 F_i^2`$, positive bilinear forms. On the $`n`$ dimensional tangent space with metric $`g_0(v)`$ let $`A=g_0(v)^{-1}g_1(v)`$ and $`B=g_0(v)^{-1}g_2(v)`$, with eigenvalues $`\lambda_j,\mu_j`$. For each $`g_0(v)`$-orthogonal $`Q`$,

```math
\det(A+QBQ^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The comparison is at the specified direction $`v`$; it does not identify the fundamental tensors in different directions or assert a global Finsler volume formula.

**Equivalence reduction.** Riemannian norms are strongly convex Finsler metrics, with fundamental tensors independent of direction. Use distinct positive relative tensor eigenvalues and evaluate arbitrary complex functions on the complexified tangent lines.

## 110 Hessian and Monge-Ampere geometry

Let $`u,v`$ be twice differentiable real functions on an open set of $`\mathbb R^n`$. At a point $`x`$ let $`\lambda_j,\mu_j`$ be the real eigenvalues of $`D^2u(x),D^2v(x)`$. For every orthogonal $`Q`$,

```math
\det(D^2u(x)+QD^2v(x)Q^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

For convex functions this is the nonnegative Monge-Ampere density of $`u(y)+v(x+Q^T(y-x))`$ at $`x`$. The Laplacian is the additive trace.

**Equivalence reduction.** At a point, real quadratic functions can realize any real symmetric Hessians, including diagonal ones with distinct eigenvalues. Apply arbitrary complex spectral functions and allow complex unitary changes of relative basis on the complexified tangent space.

## 111 Geometric measure theory

Let $`M`$ be a $`k`$-rectifiable set and let $`F,G`$ be Lipschitz maps with approximate differentials at a point where the approximate tangent $`T`$ has dimension $`k>0`$. Let $`A=|d_{\rm ap}F|`$, $`B=|d_{\rm ap}G|`$ denote the positive square roots of the two Gram endomorphisms of $`T`$. Write $`\lambda_j,\mu_j`$ for the $`k`$ singular values of the differentials, including zeros. For each orthogonal $`Q`$ on $`T`$,

```math
\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{k}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{k}\right\}.
```

The determinant is the $`k`$-Jacobian of this combined positive stretch on $`T`$. It does not assert that the Jacobian of the sum of the original maps is determined by their singular values.

**Equivalence reduction.** Use a Euclidean n-plane and diagonal linear maps as Lipschitz maps on it. Their approximate differentials have arbitrary positive singular values. Evaluate arbitrary complex functions of the selected stretches in the common complexified tangent space.


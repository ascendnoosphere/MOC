# Marcus-de Oliveira formulations: Jordan algebras and hyperbolicity

Atlas entries 037–048.

For all statements, $`n,N,r,d`$ denote the indicated positive spectral lengths, not necessarily the dimension of the original object. Eigenvalue lists use algebraic multiplicities unless a different rule is specified. $`S_n`$ is the set of permutations of $`\{1,\ldots,n\}`$, $`U(n)`$ is the group of complex unitary matrices, $`I`$ is the identity, and $`*`$ is the Hermitian adjoint. The convex hull of complex numbers uses real, nonnegative weights of sum one. The classical Marcus-de Oliveira conjecture states that for normal complex matrices $`A,B`$ of order $`n`$, with eigenvalues $`\lambda_j,\mu_j`$, and every unitary $`U`$, $`\det(A+UBU^*)`$ belongs to the convex hull of $`\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)})`$ over $`\pi\in S_n`$. Weights may depend on the two matrices and on $`U`$.

The numbering follows the Atlas of Generalized Spectral Invariants (November 2026). Each formulation specifies its hypotheses and the determinant or chosen scalar realization.

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

## 037 Euclidean Jordan algebra

Let $`J`$ be a simple Euclidean Jordan algebra with unit $`e`$ and rank $`r`$; its Jordan determinant $`\det_J(x)`$ is the product of the $`r`$ real spectral values in a Jordan-frame decomposition. Let $`a,b\in J`$ have spectral values $`\lambda_j,\mu_j`$. For every Jordan automorphism $`g`$ of $`J`$,

```math
\det_J(a+g(b))\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{r}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{r}\right\}.
```

The hull is a real interval. This is an intrinsic candidate for Jordan rank, not for the real vector-space dimension of $`J`$.

**Equivalence reduction.** Use the spectral lines of a Jordan frame in a complex Hilbert realization. The real symmetric matrix Jordan algebras have arbitrary rank and distinct real spectral lists, so complex evaluation recovers every normal pair. The intrinsic Jordan automorphism comparison remains separate.

## 038 Real symmetric Jordan algebra

Let $`A,B`$ be real symmetric matrices of order $`n`$ with real eigenvalues $`\lambda_j,\mu_j`$. The Jordan product is $`A\circ B=(AB+BA)/2`$ and the Jordan determinant is the ordinary determinant. For every orthogonal $`Q\in O(n)`$,

```math
\det(A+QBQ^T)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

**Equivalence reduction.** Use diagonal real symmetric matrices with distinct real eigenvalues and arbitrary complex functions of them. The evaluated operators and the relative unitary are complex; the real orthogonal determinant comparison is the specialization.

## 039 Complex Hermitian Jordan algebra

Let $`A,B\in M_n(\mathbb C)`$ be Hermitian with real eigenvalues $`\lambda_j,\mu_j`$. Regard them as elements of the real Jordan algebra with product $`(AB+BA)/2`$. For every $`U\in U(n)`$,

```math
\det_J(A+UBU^*)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

Here $`\det_J=\det_{\mathbb C}`$ on Hermitian matrices; Jordan rank is $`n`$, not the real dimension $`n^2`$.

**Equivalence reduction.** Use Hermitian matrices of arbitrary order with distinct real eigenvalues. Arbitrary complex functions on these eigenvalues realize all normal spectra.

## 040 Quaternionic Hermitian Jordan algebra

Let $`A,B\in M_n(\mathbb H)`$ be Hermitian. List their $`n`$ real right eigenvalues $`\lambda_j,\mu_j`$. Define the Moore determinant $`\det_M`$ of a quaternionic Hermitian matrix as the product of its real right eigenvalues. For every quaternionic unitary $`U`$,

```math
\det_M(A+UBU^*)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The interval uses $`n`$ eigenvalues, not the $`2n`$ eigenvalues of the complex realization. Squaring a determinant does not by itself prove this signed interval statement.

**Equivalence reduction.** Choose the n real diagonal quaternionic eigenvalues distinct, and use the n corresponding Jordan spectral coordinates. Their complex scalar evaluations with the full unitary group give the exact form. The Moore determinant itself remains a real invariant.

## 041 Albert algebra

Let $`J=H_3(\mathbb O)`$ be the real Albert algebra of Hermitian three-by-three octonionic matrices with its Jordan product. Let $`a,b`$ have three real Jordan spectral values $`\lambda_j,\mu_j`$. Write $`N_J`$ for the exceptional cubic Jordan norm. For every unit-preserving Jordan automorphism $`g`$ of $`J`$,

```math
N_J(a+g(b))\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{3}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{3}\right\}.
```

The six products define the real comparison interval. No associative matrix determinant is used.

**Equivalence reduction.** Select spectral lines from finite direct sums of rank-three frames. Choose arbitrary complex values on them and allow all relative complex unitaries. The single Albert cubic has rank three and does not represent arbitrary matrix orders.

## 042 Spin factor

In the Euclidean Jordan spin factor $`\mathbb R\oplus\mathbb R^m`$ let $`a=(s,x)`$ and $`b=(t,y)`$. The rank-two determinant is $`D(c,z)=c^2-\|z\|^2`$. For each orthogonal $`Q\in O(m)`$,

```math
(s+t)^2-(\|x\|+\|y\|)^2\le D(s+t,x+Qy)\le(s+t)^2-(\|x\|-\|y\|)^2.
```

These endpoints are the two permutation products of the spectral pairs $`s\pm\|x\|`$ and $`t\pm\|y\|`$. The inequalities follow from the triangle and reverse triangle inequalities.

**Equivalence reduction.** Use finite sums of rank-two spin-frame realizations, selecting the required number of complex spectral lines. The rank-two norm inequality itself is a theorem, not an equivalent unrestricted conjecture.

## 043 Symmetric cones

Let $`J`$ be a simple Euclidean Jordan algebra of rank $`r`$, and let $`a,b`$ be in the interior of its cone of squares. Their Jordan spectral values $`\lambda_j,\mu_j`$ are positive. For every Jordan automorphism $`g`$ fixing the unit,

```math
\det_J(a+g(b))\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{r}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{r}\right\}.
```

The bounds are positive. This uses the compact frame-changing automorphisms, not all cone automorphisms, which can change spectral values.

**Equivalence reduction.** Use the positive diagonal elements in matrix symmetric cones of arbitrary Jordan rank. Evaluate arbitrary complex functions of distinct positive Jordan spectral values and use all relative complex unitaries on the frame realization.

## 044 Hyperbolic polynomial

Let $`p`$ be homogeneous of degree $`d\ge1`$ and hyperbolic with respect to $`e`$, with $`p(e)>0`$. This means $`p(te-x)`$ has $`d`$ real roots for every real $`x`$. Write $`\lambda_j,\mu_j`$ for these roots for $`a,b`$ and let $`D_p(x)=p(x)/p(e)`$. Let $`g`$ be a real linear automorphism satisfying $`g(e)=e`$ and $`p(gx)=p(x)`$ for all $`x`$. The proposed assertion is

```math
D_p(a+g(b))\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{d}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{d}\right\}.
```

There need not be a frame or a realization of every permutation by $`g`$. This is a new test, not a consequence of hyperbolicity alone.

**Equivalence reduction.** Use the product polynomial on n real coordinates, hyperbolic along the all-ones vector. Its n roots are the coordinates. Complex scalar evaluations and arbitrary relative unitary positions recover every matrix order. The intrinsic hyperbolic polynomial comparison is not implied for general p.

## 045 Elementary symmetric cones

Fix $`1\le k\le n`$ and let $`p(x)=e_k(x)=\sum_{|I|=k}\prod_{i\in I}x_i`$ on $`\mathbb R^n`$, hyperbolic along $`\mathbf1`$. Let $`a,b`$ be in its open hyperbolicity cone. Let $`\lambda_j,\mu_j`$ be the $`k`$ roots of $`e_k(t\mathbf1-a)`$ and $`e_k(t\mathbf1-b)`$. For every coordinate permutation $`Q`$ the proposed assertion is

```math
e_k(a+Qb)/\binom nk\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{k}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{k}\right\}.
```

The permutation on the right acts on the $`k`$ hyperbolic roots, not on the $`n`$ coordinates. These are different for $`k<n`$.

**Equivalence reduction.** The case k equal to n gives the coordinate product polynomial and arbitrary distinct root values. Complex evaluation on its root coordinates recovers the full conjecture. For fixed lower degree use the selected labelled hyperbolic-root modes.

## 046 Determinant barrier theory

Let $`A,B`$ be positive definite Hermitian matrices of order $`n`$ with positive eigenvalues $`\lambda_j,\mu_j`$. For every $`U\in U(n)`$, the log-det barrier $`F(X)=-\log\det X`$ satisfies

```math
-\max_{\pi\in S_n}\sum_{j=1}^n\log(\lambda_j+\mu_{\pi(j)})\le F(A+UBU^*)\le-\min_{\pi\in S_n}\sum_{j=1}^n\log(\lambda_j+\mu_{\pi(j)}).
```

This is the positive determinant interval under a decreasing logarithm, not convex-hull preservation by an arbitrary nonlinear function.

**Equivalence reduction.** Use arbitrary distinct positive spectra for the two input operators and evaluate complex functions before summing. Recover the determinant statement without applying a real logarithm to complex values; the log-det bound is the positive specialization.

## 047 Spectral convex analysis

Let $`A,B`$ be Hermitian of order $`n`$ with eigenvalues $`\lambda_j,\mu_j`$. For every unitary $`U`$, let $`c(U)`$ be the ordered real eigenvalue vector of $`A+UBU^*`$. Then the determinant objective on this vector satisfies

```math
\prod_{j=1}^n c_j(U)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The right side uses products of pairwise matched spectral sums. It is not the majorization permutahedron of either input; a determinant is not a linear functional of that permutahedron.

**Equivalence reduction.** Use arbitrary complex spectral evaluations of real diagonal Hermitian matrices with simple spectra. The comparison now uses the full complex product hull, not only the permutahedron of ordered real eigenvalues.

## 048 Mixed discriminants

Let $`A,B`$ be normal matrices of order $`n`$ with eigenvalues $`\lambda_j,\mu_j`$. For $`0\le k\le n`$, let $`D(A[n-k],C[k])`$ denote the polarization of $`\det`$, normalized by $`\det(sA+tC)=\sum_k\binom nk s^{n-k}t^k D(A[n-k],C[k])`$. For every unitary $`U`$ the coefficient candidate is

```math
\binom nk D(A[n-k],(UBU^*)[k])\in\mathrm{conv}\left\{\sum_{|I|=k}\prod_{i\notin I}\lambda_i\prod_{i\in I}\mu_{\pi(i)}:\pi\in S_n\right\}.
```

For the full pointwise equivalent determinant form, take all $`s,t\in\mathbb C`$ and assert

$`\det(sA+tUBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(s\lambda_j+t\mu_{\pi(j)}):\pi\in S_n\right\}.`$

The mixed coefficient assertion is a separate comparison. A common set of weights for all eigenvalue lists would be stronger.

**Equivalence reduction.** Use the pointwise evaluation of the full homogeneous determinant polynomial in the two scalar variables, rather than an isolated mixed coefficient. At both variables equal to one this recovers the matrix conjecture. Independent coefficient hulls and simultaneous coefficient weights are separate tests.


# Marcus-de Oliveira formulations: Convex, polyhedral and tropical geometry

Atlas entries 160–171.

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

## 160 Convex bodies

Let $`K,L\subset\mathbb R^n`$ be compact convex bodies with nonempty interiors and uniform probability measures. Let $`c_K,c_L`$ be their centroids and let $`A=\int_K(x-c_K)(x-c_K)^T\,d\nu_K(x)`$, $`B=\int_L(y-c_L)(y-c_L)^T\,d\nu_L(y)`$ be their positive covariance operators. Let $`\lambda_j,\mu_j`$ be the principal covariance eigenvalues. For every orthogonal $`Q`$,

```math
\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This determinant measures the squared ellipsoid scale of the sum of covariance operators; it is not the volume of the Minkowski sum of bodies. If $`X,Y`$ are independent uniform random vectors on $`K,L`$, the sum is the covariance of $`X+QY`$.

**Equivalence reduction.** Centered ellipsoids of arbitrary dimension have positive definite covariance matrices with freely chosen positive eigenvalues up to a fixed scalar factor. Use distinct eigenvalues and arbitrary complex functions of them in the covariance realization.

## 161 Polar convexity

Let $`K=\{x:x^TA^{-1}x\le1\}`$ and $`L=\{x:x^TB^{-1}x\le1\}`$ be origin-centered full-dimensional ellipsoids with $`A,B`$ positive definite. Their polars have shape matrices $`A^{-1},B^{-1}`$. Let $`\lambda_j,\mu_j`$ be the eigenvalues of $`A,B`$. For every orthogonal $`Q`$,

```math
\det(A^{-1}+QB^{-1}Q^T)\in\mathrm{conv}\left\{\prod_{j=1}^n(\lambda_j^{-1}+\mu_{\pi(j)}^{-1}):\pi\in S_n\right\}.
```

An ellipsoid of shape matrix $`C`$ has volume equal to the unit-ball volume times $`\sqrt{\det C}`$. The displayed statement uses the positive polar shape matrices, not an assertion that volumes of arbitrary polar bodies are reciprocal.

**Equivalence reduction.** Choose centered ellipsoids with distinct positive polar shape eigenvalues. Complex spectral evaluation of their reciprocal eigenvalue lists gives arbitrary normal spectra. Keep the volume interpretation only for the positive choices.

## 162 Zonotopes

Let $`K=\sum_{i=1}^m[0,v_i]`$ and $`L=\sum_{i=1}^p[0,w_i]`$ be zonotopes in $`\mathbb R^n`$. Define the generator-frame operators $`A=\sum_i v_i v_i^T`$ and $`B=\sum_i w_i w_i^T`$, positive semidefinite. With their $`n`$ eigenvalues $`\lambda_j,\mu_j`$ including zeros, for every orthogonal $`Q`$,

```math
\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

By Cauchy-Binet the determinant is the sum of squares of all $`n`$ by $`n`$ generator minors of the combined zonotope $`K+QL`$. Ordinary zonotope volume is the sum of their absolute values, not the square root of the sum of squares.

**Equivalence reduction.** Use zonotopes generated by n independent orthogonal vectors of freely chosen positive lengths. Their frame operators have distinct positive eigenvalues. Evaluate arbitrary complex functions on the corresponding spectral coordinates.

## 163 Mixed volumes

Let $`K,L\subset\mathbb R^n`$ be full-dimensional parallelotopes with generator matrices $`A,B`$ that are real symmetric positive definite in a common Euclidean frame. Write $`\lambda_j,\mu_j`$ for their eigenvalues. Let $`C=[0,1]^n`$. For every orthogonal $`Q`$, the volume of the parallelotope $`(A+QBQ^T)C`$ satisfies

```math
\mathrm{vol}_n((A+QBQ^T)C)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The volume equals $`\det(A+QBQ^T)`$ because the sum is positive definite. The mixed coefficients of $`\det(sA+tQBQ^T)`$ are mixed discriminants. They are not generally the mixed volumes of $`AC`$ and $`QBQ^TC`$ under Minkowski addition; a general body has no spectral determinant of this kind.

**Equivalence reduction.** Use parallelotope generators that are diagonal positive matrices of arbitrary order, with distinct entries. Their volume determinant comparison is positive; arbitrary complex spectral evaluations of these generators recover the full matrix statement.

## 164 Matroid theory

Let two rank-$`n`$ real representable matroids be presented by full-row-rank matrices $`X\in\mathbb R^{n\times m}`$ and $`Y\in\mathbb R^{n\times p}`$. Set $`A=XX^T`$, $`B=YY^T`$ and let $`\lambda_j,\mu_j`$ be their positive eigenvalues. For every orthogonal $`Q`$ on the row coordinate space,

```math
\det(XX^T+QYY^TQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The left side is the sum of squares of maximal minors of $`[X\ QY]`$, including zero minors for dependent sets. This is a scalar invariant of the chosen realizations, not of the abstract matroid base polytope alone.

**Equivalence reduction.** Use the free rank-n representable matroid with diagonal positive basis matrix. Its frame operator has arbitrary distinct positive eigenvalues. Apply complex spectral evaluations, retaining the dependence on the realization.

## 165 Oriented matroids

Let $`X,Y`$ be real full-row-rank realization matrices of two oriented matroids of rank $`n`$, with their column orders and signs fixed. The chirotope of each realization records signs of its maximal minors. Use their positive Gram operators $`A=XX^T`$, $`B=YY^T`$ and eigenvalues $`\lambda_j,\mu_j`$. For every orthogonal $`Q`$ of determinant one,

```math
\det(XX^T+QYY^TQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

Cauchy-Binet expresses the determinant as the sum of squared chirotope-realizing minors of the concatenated representation $`[X\ QY]`$. Chirotope signs alone do not fix the magnitudes or spectra, so the realizations are required.

**Equivalence reduction.** Use a diagonal positive basis realization of the free oriented rank-n matroid. Its chirotope signs are fixed but its positive Gram eigenvalues may vary independently. Complex functions on those eigenvalues and all complex unitary positions give the exact form.

## 166 Valuated matroids

Let two rank-$`n`$ realizable valuated matroids over a nonarchimedean field be represented by full-row-rank matrices $`X,Y`$. Fix square nonsingular $`n`$-column basis submatrices $`X_I,Y_J`$ and let $`s_j,t_j`$ be the valuations of their eigenvalues in an algebraic closure with extended valuation. Use $`A=\mathrm{diag}(e^{s_j})`$ and $`B=\mathrm{diag}(e^{t_j})`$ on $`\mathbb C^n`$. For each unitary $`U`$,

```math
\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).
```

The sum of each list is the valuation of its chosen Plücker basis minor, up to the fixed representation normalization. This comparison depends on the chosen basis matrices, not only their valuated matroid; no scalar eigenvalue list follows from an abstract basis valuation alone.

**Equivalence reduction.** Choose diagonal basis matrices over a valued field with distinct integral valuations, using powers of a uniformizer. Arbitrary complex functions on the n selected valuation coordinates give the full spectral comparison. Abstract Pluecker valuations do not determine that normal realization without a basis choice.

## 167 Tropical min-plus matrices

Let $`A,B`$ be real $`n`$ by $`n`$ min-plus matrices with finite entries, with tropical determinant $`\mathrm{tdet}(A)=\min_{\pi\in S_n}\sum_j A_{j,\pi(j)}`$. Choose the $`n`$ tropical characteristic roots $`s_j,t_j`$ counted by slope multiplicity, using the convention that their sums are $`\mathrm{tdet}(A),\mathrm{tdet}(B)`$. For $`\epsilon>0`$ form the positive spectral representatives $`X_\epsilon=\mathrm{diag}(e^{-s_j/\epsilon})`$, $`Y_\epsilon=\mathrm{diag}(e^{-t_j/\epsilon})`$. For all unitary $`U`$,

```math
\det(X_\epsilon+UY_\epsilon U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(e^{-s_j/\epsilon}+e^{-t_{\pi(j)}/\epsilon}):\pi\in S_n\right\}.
```

Applying $`-\epsilon\log`$ to the positive interval and taking $`\epsilon\downarrow0`$ bounds any existing limit of the left log-determinant by the minimum and maximum of $`\sum_j\min(s_j,t_{\pi(j)})`$. This is the tropical spectral representative formulation, not a claim about the entrywise tropical sum of arbitrary matrices. The minimum cycle mean is a different spectral notion.

**Equivalence reduction.** Use diagonal tropical characteristic data with n distinct slopes; for finite-entry tropical matrices these slopes can be realized by taking the off-diagonal entries sufficiently large. Apply arbitrary complex functions of the selected slope values at a fixed positive deformation parameter. The tropical limit loses the complex phase.

## 168 Tropical polynomials

Let $`f,g`$ be one-variable tropical polynomials with finite coefficients and the same positive degree $`n`$. Assume their Newton polygons supply $`n`$ finite tropical roots each, listed as $`s_j,t_j`$ with horizontal multiplicity. For $`\epsilon>0`$ define $`A_\epsilon=\mathrm{diag}(e^{-s_j/\epsilon})`$ and $`B_\epsilon=\mathrm{diag}(e^{-t_j/\epsilon})`$. For every unitary $`U`$,

```math
\det(A_\epsilon+UB_\epsilon U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(e^{-s_j/\epsilon}+e^{-t_{\pi(j)}/\epsilon}):\pi\in S_n\right\}.
```

The tropical limit of each vertex log-determinant $`-\epsilon\log`$ is $`\sum_j\min(s_j,t_{\pi(j)})`$. The real determinant is a chosen root realization, not the tropical resultant of arbitrary multivariate polynomials.

**Equivalence reduction.** Take one-variable tropical polynomials with n distinct finite tropical roots, obtained from a polynomial whose Newton slopes are those chosen roots. Complex evaluation on the n slope coordinates gives the full matrix statement before taking any tropical limit.

## 169 Newton polytopes

Let $`f,g`$ be nonzero Laurent polynomials in $`r`$ variables with equal support cardinality $`n>0`$. Enumerate their exponent vectors $`a_j,b_j\in\mathbb Z^r`$. Fix a complex torus point $`z\in(\mathbb C^\times)^r`$ and define diagonal normal monomial-value operators $`A=\mathrm{diag}(z^{a_j})`$, $`B=\mathrm{diag}(z^{b_j})`$. For every unitary $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(z^{a_j}+z^{b_{\pi(j)}}):\pi\in S_n\right\}.
```

The individual determinants are monomials $`z^{\sum a_j}`$ and $`z^{\sum b_j}`$. The Newton polytopes are the convex hulls of the exponent supports; their affine dimensions and volumes are different data.

**Equivalence reduction.** Choose a one-variable Laurent polynomial with n distinct exponent values, and evaluate monomials at a positive real torus point different from one. The values are distinct. Arbitrary complex functions of them yield every spectral list.

## 170 Bergman fans and tropical linear spaces

Let $`M,N`$ be valuated matroids on ground sets of equal size $`n>0`$, with tropical linear spaces $`\mathcal L(M),\mathcal L(N)`$. Choose finite coordinate representatives $`s=(s_j)\in\mathcal L(M)`$, $`t=(t_j)\in\mathcal L(N)`$ and fix their additive projective normalization, for example $`\min_j s_j=\min_j t_j=0`$. Let $`A=\mathrm{diag}(e^{s_j})`$, $`B=\mathrm{diag}(e^{t_j})`$. For every unitary $`U`$,

```math
\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).
```

The lists are chosen coordinate valuations satisfying the tropical circuit conditions. The comparison does not claim that a general mixed operator represents a point of either tropical linear space, or that the fan is a single ordinary convex hull.

**Equivalence reduction.** Use the free rank-n valuated matroid with finite zero basis valuation. Its tropical linear space permits n freely selected coordinate values modulo common translation. Choose distinct coordinates and evaluate arbitrary complex functions on them.

## 171 Convex optimization and semidefinite programming

Let $`X,Y`$ be positive definite primal or dual slack matrices of order $`n`$ in semidefinite programs. List their positive eigenvalues $`\lambda_j,\mu_j`$. For all unitary $`U`$ on the common variable space,

```math
\det(X+UYU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

Taking logarithms bounds the log-det objective between the extrema of the sums of logs of matched eigenvalue sums. Feasibility constraints may restrict the allowed unitary orbit, but a restricted orbit satisfies the same bound. The semidefinite cone is not the scalar permutation hull.

**Equivalence reduction.** Use unconstrained positive definite slack matrices with distinct positive eigenvalues, available in the positive semidefinite cone of arbitrary order. Complex spectral functions and all relative unitaries give the exact complex form; feasibility and the real log-det objective give restricted forms.


# Marcus-de Oliveira formulations: Convex, polyhedral and tropical geometry

Atlas entries 160–171.

All eigenvalue lists use the indicated multiplicities. $S_n$ is the set of permutations of $\{1,\ldots,n\}$; $U(n)$ is the complex unitary group; $*$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. The classical conjecture compares the determinant of a sum of two normal operators with the convex hull of products of matched eigenvalue sums. The following statements specify scalar realizations when the native objects are not complex operators. The chosen realizations and all rank conditions are part of the hypotheses.

## 160 Convex bodies

Let $K,L\subset\mathbb R^n$ be compact convex bodies with nonempty interiors and uniform probability measures. Let $c_K,c_L$ be their centroids and let $A=\int_K(x-c_K)(x-c_K)^T\,d\nu_K(x)$, $B=\int_L(y-c_L)(y-c_L)^T\,d\nu_L(y)$ be their positive covariance operators. Let $\lambda_j,\mu_j$ be the principal covariance eigenvalues. For every orthogonal $Q$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This determinant measures the squared ellipsoid scale of the sum of covariance operators; it is not the volume of the Minkowski sum of bodies. If $X,Y$ are independent uniform random vectors on $K,L$, the sum is the covariance of $X+QY$.

## 161 Polar convexity

Let $K=\{x:x^TA^{-1}x\le1\}$ and $L=\{x:x^TB^{-1}x\le1\}$ be origin-centered full-dimensional ellipsoids with $A,B$ positive definite. Their polars have shape matrices $A^{-1},B^{-1}$. Let $\lambda_j,\mu_j$ be the eigenvalues of $A,B$. For every orthogonal $Q$,

$$\det(A^{-1}+QB^{-1}Q^T)\in\mathrm{conv}\left\{\prod_{j=1}^n(\lambda_j^{-1}+\mu_{\pi(j)}^{-1}):\pi\in S_n\right\}.$$

An ellipsoid of shape matrix $C$ has volume equal to the unit-ball volume times $\sqrt{\det C}$. The displayed statement uses the positive polar shape matrices, not an assertion that volumes of arbitrary polar bodies are reciprocal.

## 162 Zonotopes

Let $K=\sum_{i=1}^m[0,v_i]$ and $L=\sum_{i=1}^p[0,w_i]$ be zonotopes in $\mathbb R^n$. Define the generator-frame operators $A=\sum_i v_i v_i^T$ and $B=\sum_i w_i w_i^T$, positive semidefinite. With their $n$ eigenvalues $\lambda_j,\mu_j$ including zeros, for every orthogonal $Q$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

By Cauchy-Binet the determinant is the sum of squares of all $n$ by $n$ generator minors of the combined zonotope $K+QL$. Ordinary zonotope volume is the sum of their absolute values, not the square root of the sum of squares.

## 163 Mixed volumes

Let $K,L\subset\mathbb R^n$ be full-dimensional parallelotopes with generator matrices $A,B$ that are real symmetric positive definite in a common Euclidean frame. Write $\lambda_j,\mu_j$ for their eigenvalues. Let $C=[0,1]^n$. For every orthogonal $Q$, the volume of the parallelotope $(A+QBQ^T)C$ satisfies

$$\mathrm{vol}_n((A+QBQ^T)C)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The volume equals $\det(A+QBQ^T)$ because the sum is positive definite. The mixed coefficients of $\det(sA+tQBQ^T)$ are mixed discriminants. They are not generally the mixed volumes of $AC$ and $QBQ^TC$ under Minkowski addition; a general body has no spectral determinant of this kind.

## 164 Matroid theory

Let two rank-$n$ real representable matroids be presented by full-row-rank matrices $X\in\mathbb R^{n\times m}$ and $Y\in\mathbb R^{n\times p}$. Set $A=XX^T$, $B=YY^T$ and let $\lambda_j,\mu_j$ be their positive eigenvalues. For every orthogonal $Q$ on the row coordinate space,

$$\det(XX^T+QYY^TQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The left side is the sum of squares of maximal minors of $[X\ QY]$, including zero minors for dependent sets. This is a scalar invariant of the chosen realizations, not of the abstract matroid base polytope alone.

## 165 Oriented matroids

Let $X,Y$ be real full-row-rank realization matrices of two oriented matroids of rank $n$, with their column orders and signs fixed. The chirotope of each realization records signs of its maximal minors. Use their positive Gram operators $A=XX^T$, $B=YY^T$ and eigenvalues $\lambda_j,\mu_j$. For every orthogonal $Q$ of determinant one,

$$\det(XX^T+QYY^TQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Cauchy-Binet expresses the determinant as the sum of squared chirotope-realizing minors of the concatenated representation $[X\ QY]$. Chirotope signs alone do not fix the magnitudes or spectra, so the realizations are required.

## 166 Valuated matroids

Let two rank-$n$ realizable valuated matroids over a nonarchimedean field be represented by full-row-rank matrices $X,Y$. Fix square nonsingular $n$-column basis submatrices $X_I,Y_J$ and let $s_j,t_j$ be the valuations of their eigenvalues in an algebraic closure with extended valuation. Use $A=\mathrm{diag}(e^{s_j})$ and $B=\mathrm{diag}(e^{t_j})$ on $\mathbb C^n$. For each unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The sum of each list is the valuation of its chosen Plücker basis minor, up to the fixed representation normalization. This comparison depends on the chosen basis matrices, not only their valuated matroid; no scalar eigenvalue list follows from an abstract basis valuation alone.

## 167 Tropical min-plus matrices

Let $A,B$ be real $n$ by $n$ min-plus matrices with finite entries, with tropical determinant $\mathrm{tdet}(A)=\min_{\pi\in S_n}\sum_j A_{j,\pi(j)}$. Choose the $n$ tropical characteristic roots $s_j,t_j$ counted by slope multiplicity, using the convention that their sums are $\mathrm{tdet}(A),\mathrm{tdet}(B)$. For $\epsilon>0$ form the positive spectral representatives $X_\epsilon=\mathrm{diag}(e^{-s_j/\epsilon})$, $Y_\epsilon=\mathrm{diag}(e^{-t_j/\epsilon})$. For all unitary $U$,

$$\det(X_\epsilon+UY_\epsilon U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(e^{-s_j/\epsilon}+e^{-t_{\pi(j)}/\epsilon}):\pi\in S_n\right\}.$$

Applying $-\epsilon\log$ to the positive interval and taking $\epsilon\downarrow0$ bounds any existing limit of the left log-determinant by the minimum and maximum of $\sum_j\min(s_j,t_{\pi(j)})$. This is the tropical spectral representative formulation, not a claim about the entrywise tropical sum of arbitrary matrices. The minimum cycle mean is a different spectral notion.

## 168 Tropical polynomials

Let $f,g$ be one-variable tropical polynomials with finite coefficients and the same positive degree $n$. Assume their Newton polygons supply $n$ finite tropical roots each, listed as $s_j,t_j$ with horizontal multiplicity. For $\epsilon>0$ define $A_\epsilon=\mathrm{diag}(e^{-s_j/\epsilon})$ and $B_\epsilon=\mathrm{diag}(e^{-t_j/\epsilon})$. For every unitary $U$,

$$\det(A_\epsilon+UB_\epsilon U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(e^{-s_j/\epsilon}+e^{-t_{\pi(j)}/\epsilon}):\pi\in S_n\right\}.$$

The tropical limit of each vertex log-determinant $-\epsilon\log$ is $\sum_j\min(s_j,t_{\pi(j)})$. The real determinant is a chosen root realization, not the tropical resultant of arbitrary multivariate polynomials.

## 169 Newton polytopes

Let $f,g$ be nonzero Laurent polynomials in $r$ variables with equal support cardinality $n>0$. Enumerate their exponent vectors $a_j,b_j\in\mathbb Z^r$. Fix a complex torus point $z\in(\mathbb C^\times)^r$ and define diagonal normal monomial-value operators $A=\mathrm{diag}(z^{a_j})$, $B=\mathrm{diag}(z^{b_j})$. For every unitary $U$,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(z^{a_j}+z^{b_{\pi(j)}}):\pi\in S_n\right\}.$$

The individual determinants are monomials $z^{\sum a_j}$ and $z^{\sum b_j}$. The Newton polytopes are the convex hulls of the exponent supports; their affine dimensions and volumes are different data.

## 170 Bergman fans and tropical linear spaces

Let $M,N$ be valuated matroids on ground sets of equal size $n>0$, with tropical linear spaces $\mathcal L(M),\mathcal L(N)$. Choose finite coordinate representatives $s=(s_j)\in\mathcal L(M)$, $t=(t_j)\in\mathcal L(N)$ and fix their additive projective normalization, for example $\min_j s_j=\min_j t_j=0$. Let $A=\mathrm{diag}(e^{s_j})$, $B=\mathrm{diag}(e^{t_j})$. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The lists are chosen coordinate valuations satisfying the tropical circuit conditions. The comparison does not claim that a general mixed operator represents a point of either tropical linear space, or that the fan is a single ordinary convex hull.

## 171 Convex optimization and semidefinite programming

Let $X,Y$ be positive definite primal or dual slack matrices of order $n$ in semidefinite programs. List their positive eigenvalues $\lambda_j,\mu_j$. For all unitary $U$ on the common variable space,

$$\det(X+UYU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Taking logarithms bounds the log-det objective between the extrema of the sums of logs of matched eigenvalue sums. Feasibility constraints may restrict the allowed unitary orbit, but a restricted orbit satisfies the same bound. The semidefinite cone is not the scalar permutation hull.

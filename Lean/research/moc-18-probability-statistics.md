# Marcus-de Oliveira formulations: Probability, statistics and information geometry

Atlas entries 208–219.

All eigenvalue lists use the indicated multiplicities. $S_n$ is the set of permutations of $\{1,\ldots,n\}$; $U(n)$ is the complex unitary group; $*$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. The Marcus-de Oliveira conjecture asserts that the determinant of the sum of two normal complex operators with fixed eigenvalues lies in the convex hull of products of pairwise matched eigenvalue sums. The statements below specify the spectral data, determinant and necessary scalar realization for each setting.

## 208 Covariance matrices

Let $X,Y$ be random vectors in $\mathbb R^n$ with finite second moments and covariance matrices $A,B$, with nonnegative eigenvalues $\lambda_j,\mu_j$. For every orthogonal $Q$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

If $X,Y$ are independent, the left side is the generalized variance of $X+QY$. Dependence adds cross-covariance terms not in this formulation.

## 209 Precision matrices

Let $A,B$ be positive definite covariance matrices of order $n$ with eigenvalues $\lambda_j,\mu_j>0$. Their precision matrices are $A^{-1},B^{-1}$. For every unitary $U$ (orthogonal for real covariance matrices),

$$\det(A^{-1}+UB^{-1}U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(\lambda_j^{-1}+\mu_{\pi(j)}^{-1}):\pi\in S_n\right\}.$$

Independent Gaussian information contributions with the same parameterization add as precision matrices. If the combined covariance is the inverse of the sum, its determinant lies between the reciprocals of the largest and smallest positive products.

## 210 Correlation matrices

Let $A,B$ be positive semidefinite correlation matrices of order $n$, each with diagonal entries one, and let $\lambda_j,\mu_j$ be their eigenvalues. For each real orthogonal $Q$,

$$\det\left(\frac{A+QBQ^T}{2}\right)\in\mathrm{conv}\left\{\frac{1}{2^n}\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)}):\pi\in S_n\right\}.$$

The average is a correlation matrix whenever $QBQ^T$ has unit diagonal, in particular for a coordinate permutation. The trace of each input and of the average is $n$.

## 211 Fisher information geometry

Let $I_0,I_1,I_2$ be Fisher information bilinear forms at a common identified point of an $n$ dimensional real parameter space, with $I_0$ positive definite and $I_1,I_2$ positive semidefinite. Define the relative self-adjoint operators $A=I_0^{-1}I_1$, $B=I_0^{-1}I_2$. Let $\lambda_j,\mu_j$ be their eigenvalues. For every $I_0$-orthogonal $Q$,

$$\det(A+QBQ^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The square root of this determinant is the relative Jeffreys density of the combined information form. Independent observations add Fisher information in a common parameterization. Zero eigenvalues account for nonidentifiable directions.

## 212 Gaussian entropy

Let two independent centered nondegenerate Gaussian random vectors $X,Y$ on $\mathbb R^n$ have covariance matrices $A,B$ with positive eigenvalues $\lambda_j,\mu_j$. For every orthogonal $Q$, their sum has differential entropy $h(X+QY)=\frac12\log((2\pi e)^n\det(A+QBQ^T))$. Define $l=\min_\pi\prod_j(\lambda_j+\mu_{\pi(j)})$ and $u=\max_\pi\prod_j(\lambda_j+\mu_{\pi(j)})$. Then

$$\frac12\log((2\pi e)^n l)\le h(X+QY)\le\frac12\log((2\pi e)^n u).$$

The products are positive, so the logarithm preserves their real order. This is the entropy form of the positive matrix determinant comparison.

## 213 Density operators

Let $\rho,\sigma$ be density operators on a complex Hilbert space of dimension $n$ (positive semidefinite with trace one). Let their eigenvalue lists be probabilities $p_j,q_j$ including zeros. For $0\le t\le1$ and every unitary $U$,

$$\det(t\rho+(1-t)U\sigma U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(tp_j+(1-t)q_{\pi(j)}):\pi\in S_n\right\}.$$

The sum is a density operator of trace one. The product over the entire Hilbert space includes zeros. A support pseudodeterminant needs an identified common support of fixed rank.

## 214 Von Neumann entropy

Let $\rho,\sigma$ be positive definite density operators of order $n$, with eigenvalues $p_j,q_j$. For $0<t<1$ and each unitary $U$ put $\omega_U=t\rho+(1-t)U\sigma U^*$ and let $S(\omega_U)=-\mathrm{tr}(\omega_U\log\omega_U)$. The determinant-induced entropy analogue is the logarithmic mean for the maximally mixed state:

$$\min_\pi\frac1n\sum_j\log(tp_j+(1-t)q_{\pi(j)})\le \frac1n\log\det\omega_U\le\max_\pi\frac1n\sum_j\log(tp_j+(1-t)q_{\pi(j)}).$$

For the von Neumann entropy itself, the distinct spectral-functional comparison to formulate is

$$S(\omega_U)\in\mathrm{conv}\left\{-\sum_{j=1}^n r_{\pi j}\log r_{\pi j}:\pi\in S_n\right\},\qquad r_{\pi j}=tp_j+(1-t)q_{\pi(j)}.$$

The latter is a real entropy interval; it follows from Hermitian eigenvalue majorization and concavity of $-x\log x$, not simply from the determinant conjecture. The weighted geometric mean $e^{-S(\omega_U)}$ follows by the decreasing exponential.

## 215 Markov chains

Let $P,Q$ be finite row-stochastic matrices of order $n$, normal in the Euclidean complexified state inner product (or in a specified common stationary inner product). Let $\lambda_j,\mu_j$ be their complex transition eigenvalues. For $0\le t\le1$ and each unitary $U$ for the chosen product,

$$\det(tP+(1-t)UQU^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(t\lambda_j+(1-t)\mu_{\pi(j)}):\pi\in S_n\right\}.$$

For state permutations in the Euclidean model the average remains stochastic, hence has eigenvalue one. General Markov transition matrices may be nonnormal; the determinant comparison does not follow from the stochastic property alone.

## 216 Reversible Markov chains

Let $P,Q$ be transition matrices of two reversible Markov chains on $n$ states with common strictly positive stationary law $\nu$. Regard them as self-adjoint operators on $\ell^2(\nu)$ with real eigenvalues $\lambda_j,\mu_j\in[-1,1]$. For each $\nu$-unitary $U$ and $t\in[0,1]$,

$$\det(tP+(1-t)UQU^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(t\lambda_j+(1-t)\mu_{\pi(j)}):\pi\in S_n\right\}.$$

A state permutation preserving $\nu$ preserves reversibility under conjugation. The real hull is an interval. The stationary mode can be excluded by restricting both operators and $U$ to the common mean-zero subspace.

## 217 Principal component analysis

Let $A_0,B_0$ be covariance matrices and choose their $k>0$ leading principal component spaces, of the same dimension $k$, with retained eigenvalues $\lambda_j,\mu_j$. Let $A,B$ be the restrictions to those spaces. For each orthogonal identification $Q$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{k}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{k}\right\}.$$

The determinant is the generalized variance in the combined retained coordinate space. The traces are the sums of retained explained variances. Selecting the top $k$ eigenvalues of the full sum is a different operation.

## 218 Kernel methods and reproducing kernel Hilbert spaces

Let $K,L$ be two positive semidefinite Gram matrices of size $n$ obtained from positive-definite kernels on chosen data sets of equal size. Let $\lambda_j,\mu_j$ be the kernel eigenvalues including zeros. Fix regularization parameter $\alpha>0$. For every unitary $U$,

$$\det(I+(K+ULU^*)/\alpha)\in\mathrm{conv}\left\{\prod_{j=1}^n\left(1+\frac{\lambda_j+\mu_{\pi(j)}}{\alpha}\right):\pi\in S_n\right\}.$$

The log of the left side is a regularized kernel log-determinant, and all comparison products are positive. For trace-class positive integral kernel operators, the analogous Fredholm determinant uses the convergent infinite products and closed hull.

## 219 Optimal experimental design

Let $A,B$ be information matrices of two designs for the same $n$ parameters, each positive semidefinite, with eigenvalues $\lambda_j,\mu_j$. For $t\in[0,1]$ and every unitary $U$ (orthogonal for real parameters),

$$\det(tA+(1-t)UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(t\lambda_j+(1-t)\mu_{\pi(j)}):\pi\in S_n\right\}.$$

The left side is the D-optimality objective for a combined design whenever the transformed matrix is feasible. Taking logs is valid for positive definite sums. An A-optimality objective such as $\mathrm{tr}(A^{-1})$ is a different invariant.

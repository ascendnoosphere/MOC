# Marcus-de Oliveira formulations: Jordan algebras and hyperbolicity

Atlas entries 037–048.

For all statements, $n,N,r,d$ denote the indicated positive spectral lengths, not necessarily the dimension of the original object. Eigenvalue lists use algebraic multiplicities unless a different rule is specified. $S_n$ is the set of permutations of $\{1,\ldots,n\}$, $U(n)$ is the group of complex unitary matrices, $I$ is the identity, and $*$ is the Hermitian adjoint. The convex hull of complex numbers uses real, nonnegative weights of sum one. The classical Marcus-de Oliveira conjecture states that for normal complex matrices $A,B$ of order $n$, with eigenvalues $\lambda_j,\mu_j$, and every unitary $U$, $\det(A+UBU^*)$ belongs to the convex hull of $\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)})$ over $\pi\in S_n$. Weights may depend on the two matrices and on $U$.

The numbering follows the Atlas of Generalized Spectral Invariants (November 2026). Each formulation specifies its hypotheses and the determinant or chosen scalar realization.

## 037 Euclidean Jordan algebra

Let $J$ be a simple Euclidean Jordan algebra with unit $e$ and rank $r$; its Jordan determinant $\det_J(x)$ is the product of the $r$ real spectral values in a Jordan-frame decomposition. Let $a,b\in J$ have spectral values $\lambda_j,\mu_j$. For every Jordan automorphism $g$ of $J$,

$$\det_J(a+g(b))\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{r}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{r}\right\}.$$

The hull is a real interval. This is an intrinsic candidate for Jordan rank, not for the real vector-space dimension of $J$.

## 038 Real symmetric Jordan algebra

Let $A,B$ be real symmetric matrices of order $n$ with real eigenvalues $\lambda_j,\mu_j$. The Jordan product is $A\circ B=(AB+BA)/2$ and the Jordan determinant is the ordinary determinant. For every orthogonal $Q\in O(n)$,

$$\det(A+QBQ^T)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

## 039 Complex Hermitian Jordan algebra

Let $A,B\in M_n(\mathbb C)$ be Hermitian with real eigenvalues $\lambda_j,\mu_j$. Regard them as elements of the real Jordan algebra with product $(AB+BA)/2$. For every $U\in U(n)$,

$$\det_J(A+UBU^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Here $\det_J=\det_{\mathbb C}$ on Hermitian matrices; Jordan rank is $n$, not the real dimension $n^2$.

## 040 Quaternionic Hermitian Jordan algebra

Let $A,B\in M_n(\mathbb H)$ be Hermitian. List their $n$ real right eigenvalues $\lambda_j,\mu_j$. Define the Moore determinant $\det_M$ of a quaternionic Hermitian matrix as the product of its real right eigenvalues. For every quaternionic unitary $U$,

$$\det_M(A+UBU^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The interval uses $n$ eigenvalues, not the $2n$ eigenvalues of the complex realization. Squaring a determinant does not by itself prove this signed interval statement.

## 041 Albert algebra

Let $J=H_3(\mathbb O)$ be the real Albert algebra of Hermitian three-by-three octonionic matrices with its Jordan product. Let $a,b$ have three real Jordan spectral values $\lambda_j,\mu_j$. Write $N_J$ for the exceptional cubic Jordan norm. For every unit-preserving Jordan automorphism $g$ of $J$,

$$N_J(a+g(b))\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{3}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{3}\right\}.$$

The six products define the real comparison interval. No associative matrix determinant is used.

## 042 Spin factor

In the Euclidean Jordan spin factor $\mathbb R\oplus\mathbb R^m$ let $a=(s,x)$ and $b=(t,y)$. The rank-two determinant is $D(c,z)=c^2-\|z\|^2$. For each orthogonal $Q\in O(m)$,

$$(s+t)^2-(\|x\|+\|y\|)^2\le D(s+t,x+Qy)\le(s+t)^2-(\|x\|-\|y\|)^2.$$

These endpoints are the two permutation products of the spectral pairs $s\pm\|x\|$ and $t\pm\|y\|$. The inequalities follow from the triangle and reverse triangle inequalities.

## 043 Symmetric cones

Let $J$ be a simple Euclidean Jordan algebra of rank $r$, and let $a,b$ be in the interior of its cone of squares. Their Jordan spectral values $\lambda_j,\mu_j$ are positive. For every Jordan automorphism $g$ fixing the unit,

$$\det_J(a+g(b))\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{r}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{r}\right\}.$$

The bounds are positive. This uses the compact frame-changing automorphisms, not all cone automorphisms, which can change spectral values.

## 044 Hyperbolic polynomial

Let $p$ be homogeneous of degree $d\ge1$ and hyperbolic with respect to $e$, with $p(e)>0$. This means $p(te-x)$ has $d$ real roots for every real $x$. Write $\lambda_j,\mu_j$ for these roots for $a,b$ and let $D_p(x)=p(x)/p(e)$. Let $g$ be a real linear automorphism satisfying $g(e)=e$ and $p(gx)=p(x)$ for all $x$. The proposed assertion is

$$D_p(a+g(b))\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{d}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{d}\right\}.$$

There need not be a frame or a realization of every permutation by $g$. This is a new test, not a consequence of hyperbolicity alone.

## 045 Elementary symmetric cones

Fix $1\le k\le n$ and let $p(x)=e_k(x)=\sum_{|I|=k}\prod_{i\in I}x_i$ on $\mathbb R^n$, hyperbolic along $\mathbf1$. Let $a,b$ be in its open hyperbolicity cone. Let $\lambda_j,\mu_j$ be the $k$ roots of $e_k(t\mathbf1-a)$ and $e_k(t\mathbf1-b)$. For every coordinate permutation $Q$ the proposed assertion is

$$e_k(a+Qb)/\binom nk\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{k}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{k}\right\}.$$

The permutation on the right acts on the $k$ hyperbolic roots, not on the $n$ coordinates. These are different for $k<n$.

## 046 Determinant barrier theory

Let $A,B$ be positive definite Hermitian matrices of order $n$ with positive eigenvalues $\lambda_j,\mu_j$. For every $U\in U(n)$, the log-det barrier $F(X)=-\log\det X$ satisfies

$$-\max_{\pi\in S_n}\sum_{j=1}^n\log(\lambda_j+\mu_{\pi(j)})\le F(A+UBU^*)\le-\min_{\pi\in S_n}\sum_{j=1}^n\log(\lambda_j+\mu_{\pi(j)}).$$

This is the positive determinant interval under a decreasing logarithm, not convex-hull preservation by an arbitrary nonlinear function.

## 047 Spectral convex analysis

Let $A,B$ be Hermitian of order $n$ with eigenvalues $\lambda_j,\mu_j$. For every unitary $U$, let $c(U)$ be the ordered real eigenvalue vector of $A+UBU^*$. Then the determinant objective on this vector satisfies

$$\prod_{j=1}^n c_j(U)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The right side uses products of pairwise matched spectral sums. It is not the majorization permutahedron of either input; a determinant is not a linear functional of that permutahedron.

## 048 Mixed discriminants

Let $A,B$ be normal matrices of order $n$ with eigenvalues $\lambda_j,\mu_j$. For $0\le k\le n$, let $D(A[n-k],C[k])$ denote the polarization of $\det$, normalized by $\det(sA+tC)=\sum_k\binom nk s^{n-k}t^k D(A[n-k],C[k])$. For every unitary $U$ the coefficient candidate is

$$\binom nk D(A[n-k],(UBU^*)[k])\in\operatorname{conv}\left\{\sum_{|I|=k}\prod_{i\notin I}\lambda_i\prod_{i\in I}\mu_{\pi(i)}:\pi\in S_n\right\}.$$

The assertion is for a fixed coefficient $k$. The stronger simultaneous compound statement asks for a common set of permutation weights for all coefficients and all eigenvalue lists. Ordinary double stochasticity of the matrix of squared compound minors does not by itself provide such weights.

# Marcus-de Oliveira formulations: Exterior, symmetric and multilinear algebra

Atlas entries 013–024.

For all statements, $n,N,r,d$ denote the indicated positive spectral lengths, not necessarily the dimension of the original object. Eigenvalue lists use algebraic multiplicities unless a different rule is specified. $S_n$ is the set of permutations of $\{1,\ldots,n\}$, $U(n)$ is the group of complex unitary matrices, $I$ is the identity, and $*$ is the Hermitian adjoint. The convex hull of complex numbers uses real, nonnegative weights of sum one. The classical Marcus-de Oliveira conjecture states that for normal complex matrices $A,B$ of order $n$, with eigenvalues $\lambda_j,\mu_j$, and every unitary $U$, $\det(A+UBU^*)$ belongs to the convex hull of $\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)})$ over $\pi\in S_n$. Weights may depend on the two matrices and on $U$.

The numbering follows the Atlas of Generalized Spectral Invariants (November 2026). Each formulation specifies its hypotheses and the determinant or chosen scalar realization.

## 013 Exterior power

Let $A,B$ be normal on $\mathbb C^n$, with eigenvalues $\alpha_i,\beta_i$. For $1\le k\le n$, put $N=\binom nk$. Index the lists $\lambda_I=\prod_{i\in I}\alpha_i$, $\mu_I=\prod_{i\in I}\beta_i$ by all $k$-subsets $I$. For every unitary $V$ on $\bigwedge^k\mathbb C^n$,

$$\det(\bigwedge^k A+V(\bigwedge^k B)V^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

Use any enumeration of the subset lists as $\lambda_j,\mu_j$. The trace of $\bigwedge^k A$ is $e_k(\alpha)$. The induced sum is not $\bigwedge^k(A+B)$; a convex-hull assertion about $e_k(A+UBU^*)$ is the separate coefficient strengthening (paper Conjecture 11).

## 014 Top exterior power

Let $A,B$ be normal on a complex Hilbert space $V$ of dimension $n$, with eigenvalues $\lambda_j,\mu_j$. Let $c_U$ be the scalar by which $\bigwedge^n(A+UBU^*)$ acts on the one-dimensional space $\bigwedge^n V$. For every unitary $U$,

$$c_U\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The top exterior power of the sum, not the sum of the two top exterior powers, supplies this scalar.

## 015 Symmetric power

Let $A,B$ be normal on $\mathbb C^n$ with eigenvalues $\alpha_i,\beta_i$. For an integer $k\ge1$, let $N=\binom{n+k-1}{k}$. Enumerate the degree-$k$ monomials $\lambda_{\gamma}=\prod_i\alpha_i^{\gamma_i}$ and $\mu_{\gamma}=\prod_i\beta_i^{\gamma_i}$ over nonnegative integer vectors $\gamma$ with $\sum_i\gamma_i=k$. For every unitary $V$ on $\operatorname{Sym}^k\mathbb C^n$,

$$\det(\operatorname{Sym}^k A+V(\operatorname{Sym}^k B)V^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

The symmetric-power trace is the complete homogeneous polynomial $h_k$. The case $k=1$ recovers the matrix conjecture.

## 016 Tensor product

Let $A,C\in M_m(\mathbb C)$ and $B,D\in M_n(\mathbb C)$ all be normal. Let $N=mn$, and enumerate the eigenvalue products $\lambda_{ij}=\alpha_i\beta_j$ of $A\otimes B$ and $\mu_{ij}=\gamma_i\delta_j$ of $C\otimes D$. For every unitary $U$ on $\mathbb C^m\otimes\mathbb C^n$,

$$\det(A\otimes B+U(C\otimes D)U^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

## 017 Direct sum

Let $A,C$ be normal of order $m$, and $B,D$ normal of order $n$. Set $N=m+n$. Let $\lambda_j$ enumerate the concatenated eigenvalues of $A,B$, and $\mu_j$ those of $C,D$. For every $U\in U(N)$,

$$\det((A\oplus B)+U(C\oplus D)U^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

The same assertion applies when $U$ is block diagonal. Taking two diagonal blocks of sizes $1$ and $N-1$ permits arbitrary spectra for $N\ge2$.

## 018 Kronecker sum

Let $A,C$ be normal of order $m$ and $B,D$ normal of order $n$, with eigenvalues $\alpha_i,\gamma_i$ and $\beta_j,\delta_j$. Set $X=A\otimes I_n+I_m\otimes B$, $Y=C\otimes I_n+I_m\otimes D$, and $N=mn$. Enumerate $\lambda_{ij}=\alpha_i+\beta_j$, $\mu_{ij}=\gamma_i+\delta_j$. For every $U\in U(N)$,

$$\det(X+UYU^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

## 019 Endomorphism algebra, adjoint action

Let $A,B$ be normal of order $n$. On the $N=n^2$ dimensional Hilbert space of matrices with the Hilbert–Schmidt inner product set $X(M)=AM-MA$, $Y(M)=BM-MB$. Their eigenvalues are $\lambda_{ij}=\alpha_i-\alpha_j$ and $\mu_{ij}=\beta_i-\beta_j$. For every unitary $V$ of the endomorphism space,

$$\det(X+VYV^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

If $V$ is induced by matrix conjugation, the sum is itself an adjoint action and is singular. General $V$ need not preserve this structure.

## 020 Conjugation action

Let $A,B$ be invertible normal matrices of order $n$, with eigenvalues $\alpha_i,\beta_i$. On the matrix Hilbert space set $X(M)=AMA^{-1}$, $Y(M)=BMB^{-1}$. Both operators are normal. Enumerate $\lambda_{ij}=\alpha_i/\alpha_j$, $\mu_{ij}=\beta_i/\beta_j$, with $N=n^2$. For every unitary $V$ of that space,

$$\det(X+VYV^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

Each conjugation operator has determinant one; the statement concerns their sum.

## 021 Tensor algebraic eigenvalues

Fix real symmetric tensors $T,S$ of order $m\ge2$ and mode size $r$. For a tensor $Z$ let $p_Z(t)$ be the monic characteristic resultant of $Zx^{m-1}-t x^{[m-1]}$, where $x^{[m-1]}$ is the vector of component powers. Require degree $N=r(m-1)^{r-1}$, and define $D(Z)=(-1)^N p_Z(0)$. Enumerate the complex roots $\lambda_j$ of $p_T$ and $\mu_j$ of $p_S$. The direct additive candidate is

$$D(T+S)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

The use of the resultant fixes the eigenvalue convention. Ordinary orthogonal changes of coordinates do not generally preserve this nonlinear eigenvalue equation. No equivalence or universal validity is asserted.

## 022 Tensor Z-eigenvalues

For a real symmetric tensor $Z$ of order $m$ define its Z-spectrum as the distinct real stationary values of $Zx^m$ on the unit sphere, equivalently $Zx^{m-1}=\lambda x$ with $x^Tx=1$. For real symmetric tensors $T,S$ of the same format and $Q\in O(r)$, assume $T,S,T+Q\cdot S$ all have exactly $N\ge1$ distinct such values. Define $D_Z(Z)$ as their product, using each distinct value once. With $\lambda_j,\mu_j$ the Z-values of $T,S$, the candidate is

$$D_Z(T+Q\cdot S)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

Here $Q\cdot S$ is the simultaneous orthogonal action in every mode. The finite count and product convention are extra hypotheses, not intrinsic tensor determinants.

## 023 GKZ hyperdeterminant

Fix an equal-mode tensor format $(r,\ldots,r)$ of order $m\ge2$ for which the dual Segre variety is a hypersurface. Fix a nonzero normalization $\operatorname{Hdet}$ of its defining polynomial. Let $D_m(a)=\sum_{j=1}^r a_j e_j^{\otimes m}$ and $D_m(b)$ be diagonal tensors. Use unitary factors $U,\overline U$ in the first two modes and the identity in the other modes to transform $D_m(b)$, and denote the result by $T_U$. The proposed diagonal-orbit test is

$$\operatorname{Hdet}(D_m(a)+T_U)\in\operatorname{conv}\{\operatorname{Hdet}(D_m(a)+D_m(b_\pi)):\pi\in S_r\},$$

where $(b_\pi)_j=b_{\pi(j)}$. This choice agrees with the ordinary determinant problem when $m=2$. In higher order the polynomial is a discriminant, not a product of eigenvalues. The candidate may fail; its permutation hull is defined by the displayed diagonal values, not by a Newton polytope.

## 024 Gram matrices

Let $X,Y$ have the same number $n$ of columns and arbitrary row counts. Let $\lambda_j,\mu_j$ be the squared singular values, including zeros, of $X,Y$. For every $U\in U(n)$,

$$\det(X^*X+UY^*YU^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The determinant on the left is the squared volume of the column parallelotope of the vertically stacked matrix with blocks $X$ and $YU^*$.

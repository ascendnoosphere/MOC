# Marcus-de Oliveira formulations: Classical linear algebra and matrix analysis

Atlas entries 001–012.

For all statements, $n,N,r,d$ denote the indicated positive spectral lengths, not necessarily the dimension of the original object. Eigenvalue lists use algebraic multiplicities unless a different rule is specified. $S_n$ is the set of permutations of $\{1,\ldots,n\}$, $U(n)$ is the group of complex unitary matrices, $I$ is the identity, and $*$ is the Hermitian adjoint. The convex hull of complex numbers uses real, nonnegative weights of sum one. The classical Marcus-de Oliveira conjecture states that for normal complex matrices $A,B$ of order $n$, with eigenvalues $\lambda_j,\mu_j$, and every unitary $U$, $\det(A+UBU^*)$ belongs to the convex hull of $\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)})$ over $\pi\in S_n$. Weights may depend on the two matrices and on $U$.

The numbering follows the Atlas of Generalized Spectral Invariants (November 2026). Each formulation specifies its hypotheses and the determinant or chosen scalar realization.

## 001 Complex matrices

Let $n\ge1$ and let $A,B\in M_n(\mathbb C)$ be normal ($AA^*=A^*A$ and $BB^*=B^*B$). Let $\lambda_j,\mu_j$ be their respective characteristic roots. For every $U\in U(n)$,

$$\det(A+UBU^*)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Normality cannot be removed for arbitrary complex matrices. For $A=E_{12}$ and $B=E_{21}$ in order two, both eigenvalue lists are zero, but $\det(A+B)=-1$; $E_{ij}$ has a single unit entry at $(i,j)$.

## 002 Normal matrices

Let $A=\sum_\lambda\lambda P_\lambda$ and $B=\sum_\mu\mu Q_\mu$ be normal endomorphisms of the same complex Hilbert space of dimension $n$. The projections are orthogonal and sum to the identity in each family. Repeat $\lambda$ and $\mu$ according to the ranks of $P_\lambda,Q_\mu$, to obtain $\lambda_j,\mu_j$. For every unitary $U$,

$$\det(A+UBU^*)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The hull on the right is the hull of determinants of sums of commuting representatives. It is not the numerical range of $A+B$.

## 003 Hermitian matrices

Let $H,K$ be Hermitian matrices of order $n$ with real eigenvalue lists $\lambda_j,\mu_j$. For every $U\in U(n)$,

$$\min_{\pi\in S_n}\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)})\ \le\ \det(H+UKU^*)\ \le\ \max_{\pi\in S_n}\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)}).$$

## 004 Positive definite matrices

Let $A,B$ be positive definite Hermitian matrices of order $n$, with positive eigenvalues $\lambda_j,\mu_j$. For every unitary $U$,

$$\det(A+UBU^*)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Equivalently, its positive $n$th root is between the smallest and largest positive $n$th roots of the displayed products.

## 005 Unitary matrices

Let $A,B,U\in U(n)$. Write the eigenvalues of $A,B$ as $e^{i\theta_j},e^{i\phi_j}$, respectively, for real angles $\theta_j,\phi_j$. Then

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(e^{i\theta_j}+e^{i\phi_{\pi(j)}}):\pi\in S_n\right\}.$$

## 006 Nonnormal matrices

Let $A,B\in M_n(\mathbb C)$ be arbitrary matrices, and let $\lambda_j,\mu_j$ be their characteristic roots with algebraic multiplicity. Define the normal spectral representatives $X=\mathrm{diag}(\lambda_j)$ and $Y=\mathrm{diag}(\mu_j)$ on $\mathbb C^n$. For every unitary $U$,

$$\det(X+UYU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_n\right\}.$$

This spectral-representative form has the same range of input lists as the matrix conjecture. It does not compare $\det(A+UBU^*)$ for arbitrary nonnormal inputs: for $A=E_{12},B=E_{21},U=I$ in order two the determinant of the actual sum is $-1$ although the comparison products are all zero.

## 007 Rectangular maps

Let $X:\mathbb C^n\to\mathbb C^p$ and $Y:\mathbb C^n\to\mathbb C^q$. Set $A=(X^*X)^{1/2}$ and $B=(Y^*Y)^{1/2}$. Let $s_j,t_j$ be their $n$ singular values, including zeros. For every unitary $U$ on the common domain,

$$\det(|X|+U|Y|U^*)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{n}(s_j+t_{\pi(j)}):\pi\in S_{n}\right\}.$$

This is a determinant on the domain, not a determinant of $X+Y$ or the product of only the nonzero singular values of a rectangular sum.

## 008 Commuting normal tuple

Let $(A_1,\ldots,A_k)$ and $(B_1,\ldots,B_k)$ be two internally commuting normal tuples of order $n$. Their joint eigenvalue lists are $a_j,b_j\in\mathbb C^k$. For every complex linear functional $L:\mathbb C^k\to\mathbb C$ and every $U\in U(n)$,

$$\det\left(\sum_{\ell=1}^k L(e_\ell)(A_\ell+UB_\ell U^*)\right)\in\mathrm{conv}\left\{\prod_{j=1}^n L(a_j+b_{\pi(j)}):\pi\in S_n\right\}.$$

Here $e_\ell$ is a coordinate unit vector. The weights may depend on $L$. A single set of weights for all $L$ is a stronger assertion.

## 009 Regular matrix pencils

Let $A-tB$ and $C-tD$ be regular pencils of order $n$ with $B,D$ invertible. On the same complex Hilbert space require $X=B^{-1}A$ and $Y=D^{-1}C$ to be normal. Let $\lambda_j,\mu_j$ be the finite generalized eigenvalues of the two pencils. For every unitary $U$,

$$\det(B^{-1}A+UD^{-1}CU^*)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The statement excludes infinite generalized eigenvalues. It uses normalized pencils, not the sum of the unnormalized pencils.

## 010 Monic matrix polynomials

Let $P(t),Q(t)$ be monic matrix polynomials of degree $m$ with coefficients of order $r$. Let $C_P,C_Q$ be their block companion linearizations of order $N=mr$. Require both linearizations to be normal on a fixed common complex Hilbert space (or choose normal diagonal root realizations and state that choice). Let $\lambda_j,\mu_j$ be the roots of $\det P(t),\det Q(t)$, respectively. For every unitary $U$ on that space,

$$\det(C_P+UC_QU^*)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

For diagonal root realizations the statement is about those realizations, not about the actual companion matrices or $P+Q$.

## 011 Real skew-symmetric matrices

Let $A,B\in M_n(\mathbb R)$ satisfy $A^T=-A$, $B^T=-B$. Let their complex eigenvalues be $\lambda_j,\mu_j$ (opposite imaginary pairs, with any zeros). For every $U\in U(n)$ after complexification,

$$\det(A+UBU^*)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

For real orthogonal $U$ the sum remains real skew-symmetric; its determinant is the squared Pfaffian in even order and zero in odd order. The unrestricted permutation hull can contain values that are not squared Pfaffians.

## 012 Commutative-ring matrices

Let $R$ be a commutative unital ring, $A,B\in M_n(R)$, and let $\iota:R\to\mathbb C$ be a unital ring homomorphism. Require the entrywise images $\iota(A),\iota(B)$ to be normal. Let $\lambda_j,\mu_j$ be their characteristic roots. For every $U\in U(n)$,

$$\det(\iota(A)+U\iota(B)U^*)\ \in\ \mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

No ordinary real convex hull is specified over an arbitrary ring without a scalar realization.

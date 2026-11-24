# Marcus-de Oliveira formulations: Infinite-dimensional spectral and determinant theory

Atlas entries 061–072.

All finite eigenvalue lists include multiplicities unless stated otherwise. $S_n$ denotes the permutations of $\{1,\ldots,n\}$; $U(n)$ denotes the unitary group; $*$ denotes the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. An overline denotes closure. The original conjecture asserts that the determinant of a sum of two normal complex matrices with fixed eigenvalues is in the convex hull of the products of their pairwise matched eigenvalue sums. The statements below specify the operator, invariant and comparison data in each setting. New extensions require proof; an additional realization or finite spectral window is part of the statement when no intrinsic scalar determinant exists.

## 061 Compact operators

Let $A,B$ be compact normal operators on a separable Hilbert space. Choose a finite-dimensional common compression space $E$ with orthogonal projection $P$ such that $A_E=P A|_E$ and $B_E=P B|_E$ are normal. List their eigenvalues $\lambda_j,\mu_j$ with $n=\dim E>0$. For every unitary $U$ on $E$,

$$\det_E(A_E+UB_EU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This is the finite spectral-block formulation. If $A,B$ are also trace class, the Fredholm version gives a convergent infinite determinant. Compactness alone does not imply a convergent eigenvalue product.

## 062 Trace-class operators

Let $A,B$ be normal trace-class operators on a separable infinite-dimensional complex Hilbert space. List the eigenvalues in complete orthonormal eigenbases as summable sequences $\lambda_j,\mu_j$. For every unitary $U$ on the space,

$$\det_F(I+A+UBU^*)\in\overline{\operatorname{conv}}\left\{\prod_{j\ge1}(1+\lambda_j+\mu_{\pi(j)}):\pi\text{ a finite permutation of }\mathbb N\right\}.$$

The closed hull permits limits of finite permutations. Each product converges since the corresponding sum sequence is absolutely summable. Finite-rank truncation in trace norm connects this assertion to the matrix conjecture; the finite-dimensional version with $I$ removed is obtained by a scalar shift of the first matrix.

## 063 Hilbert-Schmidt operators

Let $A,B$ be normal Hilbert-Schmidt operators on a separable Hilbert space with eigenvalue sequences $\lambda_j,\mu_j$ in $\ell^2$, repeated according to complete eigenbases. For $C$ Hilbert-Schmidt define the second regularized determinant $\det_2(I+C)=\prod_j(1+c_j)e^{-c_j}$, using the algebraic eigenvalues $c_j$. Put $E_2(z)=(1+z)e^{-z}$. For every unitary $U$, propose

$$\det_2(I+A+UBU^*)\in\overline{\operatorname{conv}}\left\{\prod_{j\ge1}E_2(\lambda_j+\mu_{\pi(j)}):\pi\text{ a finite permutation of }\mathbb N\right\}.$$

The products are convergent. For finite rank the exponential correction is independent of the relative unitary position because trace is additive; in general the determinant is continuous in Hilbert-Schmidt norm. No ordinary trace of an arbitrary Hilbert-Schmidt operator is required.

## 064 Schatten classes

Fix an integer $p\ge1$. Let $A,B$ be normal operators in the Schatten class $S_p$ (the $p$th powers of their singular values are summable). Let $\lambda_j,\mu_j$ be their eigenvalues from complete orthonormal eigenbases. Define $E_p(z)=(1+z)\exp(\sum_{k=1}^{p-1}(-1)^k z^k/k)$ and $\det_p(I+C)=\prod_j E_p(c_j)$. For all unitary $U$, the regularized determinant candidate is

$$\det_p(I+A+UBU^*)\in\overline{\operatorname{conv}}\left\{\prod_{j\ge1}E_p(\lambda_j+\mu_{\pi(j)}):\pi\text{ a finite permutation of }\mathbb N\right\}.$$

For $p=1,2$ the finite-matrix conjecture and determinant continuity give the corresponding limit statement. For $p\ge3$ the higher trace corrections can depend on $U$; the displayed candidate is not an algebraic equivalent of the ordinary determinant conjecture.

## 065 Integral operators

Let $(X,\nu)$ be a finite measure space and let $A,B$ be normal trace-class integral operators on the separable space $L^2(X,\nu)$, with kernels $K_A,K_B$ and eigenvalue sequences $\lambda_j,\mu_j$ in complete orthonormal eigenbases. For every unitary $U$ on $L^2$,

$$\det_F(I+A+UBU^*)\in\overline{\operatorname{conv}}\left\{\prod_{j\ge1}(1+\lambda_j+\mu_{\pi(j)}):\pi\text{ a finite permutation of }\mathbb N\right\}.$$

Use the Fredholm determinant of the sum of integral operators, not an integral of pointwise kernel determinants. Kernel diagonal integrals give the traces only when the necessary diagonal regularity holds.

## 066 Elliptic operators on closed manifolds

Let $M$ be a closed Riemannian manifold and $L_1,L_2$ positive self-adjoint elliptic operators with compact resolvent on the same complex $L^2$ space. Choose $n$ orthonormal eigenfunctions of each, and let $E,F$ be their spans, with respective positive eigenvalues $\lambda_j,\mu_j$. For every unitary identification $U:F\to E$,

$$\det_E(L_1|_E+U(L_2|_F)U^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This uses finite elliptic spectral windows. Zeta determinants of full unbounded operators require analytic continuation and are not limits of unnormalized products in this hull.

## 067 Pseudodifferential calculus

Let $A,B$ be classical pseudodifferential operators on sections of a Hermitian vector bundle of rank $n$ over a closed manifold. Assume their principal symbols $a(x,\xi),b(x,\xi)$ have the same order and are normal endomorphisms at each nonzero cotangent vector $(x,\xi)$. At that vector let $\lambda_j,\mu_j$ be the symbol eigenvalues. For every unitary endomorphism $u$ of the fiber,

$$\det(a(x,\xi)+u b(x,\xi)u^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This is a pointwise symbol determinant. It does not identify the Wodzicki residue or a regularized determinant of the entire operator with a pointwise product.

## 068 Spectral triples

Let $(\mathcal A,H,D)$ be a spectral triple with a self-adjoint Dirac operator $D$ of compact resolvent. Let $D_1,D_2$ be two self-adjoint Dirac-type operators on $H$ with compact resolvent. Choose $n$ eigenvectors of each spanning $E_1,E_2$, and let $\lambda_j,\mu_j$ be their signed Dirac eigenvalues. For every unitary $U:E_2\to E_1$,

$$\det_{E_1}(D_1|_{E_1}+U(D_2|_{E_2})U^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The rank is the finite spectral count. The dimension spectrum of the triple (poles of its zeta functions) is not this eigenvalue list.

## 069 Dixmier trace theory

Let $A,B$ be positive compact operators in the weak trace ideal $\mathcal L^{1,\infty}$ on a separable Hilbert space. Let $A_N,B_N$ be the positive diagonal operators on $\mathbb C^N$ with their first $N$ singular values $s_j,t_j$, respectively. For all $U_N\in U(N)$,

$$\det(I_N+A_N+U_NB_NU_N^*)\in\operatorname{conv}\left\{\prod_{j=1}^{N}(1+s_j+t_{\pi(j)}):\pi\in S_{N}\right\}.$$

The shift by one occurs in every permutation factor. This is a finite product test of the singular data. A Dixmier trace is a generalized limit of logarithmically normalized sums, not a determinant; no unregularized infinite product is presumed.

## 070 De la Harpe-Skandalis determinant

Let $\mathcal A=M_n(\mathbb C)$ with normalized trace $\tau=\operatorname{Tr}/n$. Let $A,B$ be normal with eigenvalues $\lambda_j,\mu_j$, and suppose $C=A+UBU^*$ is invertible for a unitary $U$. For a piecewise smooth invertible path $g:[0,1]\to GL_n(\mathbb C)$ from $I$ to $C$, define $L(g)=(2\pi i)^{-1}\int_0^1\tau(g'(t)g(t)^{-1})\,dt$. Then

$$\exp(2\pi i n L(g))\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Changing the path changes $nL(g)$ by an integer, so the exponential is well defined and equals $\det C$. Singular sums are included by continuity of the ordinary determinant. In general Banach algebras the period group need not admit this scalar exponential.

## 071 Perturbation determinants

Let $A,B$ be normal trace-class operators on a separable Hilbert space with eigenvalue sequences $\lambda_j,\mu_j$. Fix $z\ne0$ and consider the relative Fredholm determinant against the reference operator $-zI$, namely $D_z(U)=\det_F((A+UBU^*-zI)(-zI)^{-1})$. For each unitary $U$,

$$D_z(U)\in\overline{\operatorname{conv}}\left\{\prod_{j\ge1}\left(1-\frac{\lambda_j+\mu_{\pi(j)}}{z}\right):\pi\text{ a finite permutation of }\mathbb N\right\}.$$

The relative operator is identity plus trace class. More general reference operators need not preserve the two spectra or reduce to the same permutation factors.

## 072 Scattering theory

At a fixed energy $E$, let $S_1(E),S_2(E)$ be unitary scattering matrices on a common $n$-channel Hilbert space. Let their eigenphases be $\theta_j,\phi_j$, so $\lambda_j=e^{i\theta_j}$ and $\mu_j=e^{i\phi_j}$. For every unitary channel mixing $U$,

$$\det(S_1(E)+US_2(E)U^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The sum is a determinant comparison of scattering amplitudes; it need not itself be a unitary scattering matrix. Resonance poles are not included among channel eigenvalues.

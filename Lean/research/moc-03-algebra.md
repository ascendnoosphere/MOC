# Marcus-de Oliveira formulations: Associative and nonassociative algebras

Atlas entries 025–036.

For all statements, $n,N,r,d$ denote the indicated positive spectral lengths, not necessarily the dimension of the original object. Eigenvalue lists use algebraic multiplicities unless a different rule is specified. $S_n$ is the set of permutations of $\{1,\ldots,n\}$, $U(n)$ is the group of complex unitary matrices, $I$ is the identity, and $*$ is the Hermitian adjoint. The convex hull of complex numbers uses real, nonnegative weights of sum one. The classical Marcus-de Oliveira conjecture states that for normal complex matrices $A,B$ of order $n$, with eigenvalues $\lambda_j,\mu_j$, and every unitary $U$, $\det(A+UBU^*)$ belongs to the convex hull of $\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)})$ over $\pi\in S_n$. Weights may depend on the two matrices and on $U$.

The numbering follows the Atlas of Generalized Spectral Invariants (November 2026). Each formulation specifies its hypotheses and the determinant or chosen scalar realization.

## 025 Finite associative unital algebra

Let $\mathcal A$ be a finite-dimensional complex unital associative algebra of dimension $n$ with a fixed Hermitian inner product. Let $L_a(x)=ax$ and $L_b(x)=bx$ be normal linear maps, with eigenvalues $\lambda_j,\mu_j$. For every unitary $U$ on $\mathcal A$,

$$\det_{\mathbb C}(L_a+UL_bU^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

If $UL_bU^*$ is again left multiplication by $b'$, the determinant is the regular norm of $a+b'$. No closure of the regular representation under all unitary conjugations is assumed.

## 026 Finite commutative algebra

Let $\mathcal A$ be a finite-dimensional commutative unital complex algebra of dimension $n$. For characters $\chi$ of $\mathcal A$, let $m_\chi$ be the dimension of the associated local factor. List $\lambda_j=\chi(a)$ and $\mu_j=\chi(b)$ with each character repeated $m_\chi$ times in the same order. Then

$$\det L_{a+b}\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

In fact $\det L_{a+b}=\prod_\chi(\chi(a)+\chi(b))^{m_\chi}$ is one permutation value, even if the multiplication maps are not normal.

## 027 Central simple algebra

Let $\mathcal A$ be central simple of degree $r$ over a field $F$ with a fixed embedding in $\mathbb C$. Choose a splitting $\mathcal A\otimes_F\mathbb C\simeq M_r(\mathbb C)$. Let $a,b$ have normal images with reduced characteristic roots $\lambda_j,\mu_j$. For every unitary $u$ in the split matrix algebra,

$$\operatorname{Nrd}(a+ubu^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{r}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{r}\right\}.$$

Here $\operatorname{Nrd}$ is the reduced norm of the complex scalar extension, equal to the ordinary determinant in the split representation.

## 028 Quaternion algebra

Let $q=a+v$ and $p=b+w$ in $\mathbb H$, where $a,b$ are real and $v,w$ are imaginary quaternions. Set $\lambda_{1,2}=a\pm i\|v\|$ and $\mu_{1,2}=b\pm i\|w\|$. For every unit quaternion $u$,

$$N(q+upu^{-1})\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{2}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{2}\right\}.$$

The quadratic norm $N(x)=x\bar x$ is the reduced determinant. Unit quaternion conjugation rotates the imaginary part, so the two endpoints are $(a+b)^2+(\|v\|\pm\|w\|)^2$.

## 029 Quaternionic matrices

Fix the standard complex representation $\chi:M_n(\mathbb H)\to M_{2n}(\mathbb C)$, a unital multiplicative map that preserves adjoints. Let $A,B$ be quaternionic normal matrices and let $\lambda_j,\mu_j$ list all $N=2n$ complex eigenvalues of $\chi(A),\chi(B)$, including conjugate pairs and multiplicity. For every quaternionic unitary $U$,

$$\det_{\mathbb C}\chi(A+UBU^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

The Study determinant is the nonnegative square root of the left side under the square-root convention. Do not take square roots of arbitrary complex permutation products; the displayed hull concerns the squared Study determinant.

## 030 Division-ring matrices

Let $D$ be a division ring with a specified unital faithful representation $\rho:D\to M_s(\mathbb C)$. Extend it to block matrices of order $r$. Let $A,B\in M_r(D)$ have normal complex images. Put $N=rs$ and let $\lambda_j,\mu_j$ be their complex eigenvalues. For every $U\in U(N)$,

$$\det_{\mathbb C}(\rho(A)+U\rho(B)U^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

The determinant here is a determinant of the realization. The Dieudonné determinant takes values in abelianized units; no ordinary convex combination in that group is specified.

## 031 Octonion algebra

Let $x=a+v$, $y=b+w$ be real octonions with imaginary parts $v,w$. Let $\lambda_{1,2}=a\pm i\|v\|$, $\mu_{1,2}=b\pm i\|w\|$. For every norm-preserving octonion automorphism $g$,

$$N(x+g(y))\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{2}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{2}\right\}.$$

The norm is $N(z)=z\bar z$. The bounds follow from $-\|v\|\|w\|\le\langle v,g(w)\rangle\le\|v\|\|w\|$. This statement does not use nonassociative matrix multiplication.

## 032 Clifford algebra

Let $\mathrm{Cl}(V,q)$ be a complex Clifford algebra of a finite-dimensional quadratic space, and choose a finite-dimensional spinor or regular representation $\rho$ on a complex Hilbert space of dimension $N$. For $a,b$ with normal represented operators, let $\lambda_j,\mu_j$ be the represented eigenvalues. For every unitary $U$,

$$\det(\rho(a)+U\rho(b)U^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

If the sum is represented by an algebra element, its representation determinant is used. The result depends on the selected representation.

## 033 Finite group algebra

Let $G$ be a finite group of order $N$. On $\mathbb C[G]$ use the orthonormal group basis and the involution $g^*=g^{-1}$ with conjugate coefficients. For normal $a,b$ in this algebra, let $\lambda_j,\mu_j$ be the eigenvalues of the left regular convolution matrices $L_a,L_b$. For every unitary $U$ of the regular space,

$$\det(L_a+UL_bU^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{N}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{N}\right\}.$$

The regular determinant is the group determinant; the spectrum includes the Fourier-block multiplicities.

## 034 Frobenius algebra

Let $\mathcal A$ be a finite-dimensional complex Frobenius algebra (an algebra with a nondegenerate bilinear pairing from a Frobenius functional). Choose a positive Hermitian inner product on its underlying $n$ dimensional space. Let $L_a,L_b$ be normal multiplication maps, with eigenvalues $\lambda_j,\mu_j$. For every unitary $U$,

$$\det(L_a+UL_bU^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This uses the regular trace and multiplication determinant, not the possibly nonpositive Frobenius functional.

## 035 Polynomial quotient

Let $p\in\mathbb C[t]$ be monic of degree $n$ and let $\mathcal A=\mathbb C[t]/(p)$. Let $a=f(t)$, $b=g(t)$ in this quotient. List the roots $r_j$ of $p$ with multiplicity and put $\lambda_j=f(r_j)$, $\mu_j=g(r_j)$. Then

$$\det L_{a+b}\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The determinant equals the product with the identity permutation. This follows from simultaneous triangularization of the two multiplication maps, including repeated roots.

## 036 Finite projective module

Let $E$ be a finite projective module of constant positive rank $n$ over a commutative unital ring $R$. Fix a homomorphism $x:R\to\mathbb C$ and a Hermitian inner product on $E_x=E\otimes_{R,x}\mathbb C$. Let $A,B\in\operatorname{End}_R(E)$ have normal fiber maps $A_x,B_x$ with eigenvalues $\lambda_j,\mu_j$. For every unitary $U$ of $E_x$,

$$\det(A_x+UB_xU^*)\ \in\ \operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The left side is the scalar on the top exterior fiber. A determinant line without an endomorphism or scalar realization is not a complex number.

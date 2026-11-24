# Marcus-de Oliveira formulations: Operator algebras and noncommutative analysis

Atlas entries 049–060.

All finite eigenvalue lists include multiplicities unless stated otherwise. $S_n$ denotes the permutations of $\{1,\ldots,n\}$; $U(n)$ denotes the unitary group; $*$ denotes the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. An overline denotes closure. The original conjecture asserts that the determinant of a sum of two normal complex matrices with fixed eigenvalues is in the convex hull of the products of their pairwise matched eigenvalue sums. The statements below specify the operator, invariant and comparison data in each setting. New extensions require proof; an additional realization or finite spectral window is part of the statement when no intrinsic scalar determinant exists.

## 049 Banach-space operators

Let $X$ be a complex Banach space and $A,B$ bounded operators with finite-dimensional common invariant subspace $E$ of positive dimension $n$. Fix a Hilbert inner product on $E$ for which both restrictions are normal. Let $\lambda_j,\mu_j$ be the eigenvalues of the restrictions. For every unitary $U:E\to E$,

$$\det_E(A|_E+UB|_EU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The determinant uses the finite-dimensional action, not the entire Banach-space spectrum. The inner product is part of the data. For nuclear determinants on infinite spaces, a separate continuity and summability condition is necessary.

## 050 Hilbert-space operators

Let $H$ be a separable infinite-dimensional complex Hilbert space, and let $A,B$ be normal trace-class operators on $H$. Fix complete orthonormal eigenbases, and list their eigenvalues $\lambda_j,\mu_j$ with multiplicity (including zeros for kernel basis vectors). For every unitary $U$ on $H$, the Fredholm determinant form is

$$\det_F(I+A+UBU^*)\in\overline{\operatorname{conv}}\left\{\prod_{j\ge1}(1+\lambda_j+\mu_{\pi(j)}):\pi\text{ a finite permutation of }\mathbb N\right\}.$$

The Fredholm determinant of $I+C$ for trace-class $C$ is the convergent eigenvalue product $\prod_j(1+c_j)$. Finite-rank approximation in trace norm and continuity of this determinant reduce the closed-hull formulation to the finite matrix conjecture. A finite permutation fixes all but finitely many indices.

## 051 Unital Banach algebra

Let $\mathcal A$ be a complex unital Banach algebra with a continuous unital homomorphism $\rho:\mathcal A\to M_n(\mathbb C)$. Let $a,b$ have normal images, and let $\lambda_j,\mu_j$ be the eigenvalues of those images. For every unitary $u\in U(n)$, the determinant associated with this representation satisfies

$$\det(\rho(a)+u\rho(b)u^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Its additive trace is $\operatorname{Tr}\rho(a)$. If an intrinsic trace-associated determinant instead takes values modulo a period group, this complex hull requires an additional scalar realization.

## 052 Commutative C-star algebra C(X)

Let $X$ be a compact space, $\nu$ a probability measure on $X$, and $f,g:X\to(0,\infty)$ continuous. Write $\mu_f=f_*\nu$, $\mu_g=g_*\nu$ for the distributions. A coupling $\gamma$ is a probability measure on $\mathbb R_{>0}^2$ with these two marginals. Define $D_\nu(h)=\exp(\int_X\log h\,d\nu)$. Then

$$D_\nu(f+g)\in\left[\inf_\gamma\exp\int\log(s+t)\,d\gamma(s,t),\ \sup_\gamma\exp\int\log(s+t)\,d\gamma(s,t)\right].$$

The actual joint distribution $(f,g)_*\nu$ is a coupling, so this is the commuting continuous version. For equal-mass atoms the extremal couplings are permutation matchings. Positivity fixes the logarithm; this does not define a complex determinant for arbitrary continuous functions.

## 053 Unital C-star algebra

Let $\mathcal A$ be a unital complex C-star algebra and $\rho:\mathcal A\to M_n(\mathbb C)$ a unital adjoint-preserving representation. For normal $a,b\in\mathcal A$, let $\lambda_j,\mu_j$ be the spectra with multiplicity of $\rho(a),\rho(b)$. For every unitary $u\in\mathcal A$,

$$\det(\rho(a+ubu^*))\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This is the classical conjecture in each finite-dimensional representation. An algebra without such a representation needs a separate determinant, as in the tracial formulation below.

## 054 Normal C-star element

Let $a,b$ be normal in a unital C-star algebra with a finite-dimensional unital adjoint-preserving representation $\rho$ of dimension $n$. For any continuous $f:\sigma(a)\to\mathbb C$, $g:\sigma(b)\to\mathbb C$, let $\lambda_j,\mu_j$ be the represented eigenvalues of $a,b$. For every unitary $U$ on the representation space,

$$\det(\rho(f(a))+U\rho(g(b))U^*)\in\operatorname{conv}\left\{\prod_{j=1}^n(f(\lambda_j)+g(\mu_{\pi(j)})):\pi\in S_n\right\}.$$

Continuous functional calculus preserves normality and gives the stated spectral values. Taking the identity functions gives the matrix form.

## 055 Finite von Neumann algebra

Let $(\mathcal M,\tau)$ be a finite von Neumann algebra with faithful normal tracial state $\tau(1)=1$. Let $a,b$ be positive invertible elements and let $\nu_a,\nu_b$ be their spectral probability measures under $\tau$. Write $\Gamma(\nu_a,\nu_b)$ for the set of probability couplings of these measures. For every unitary $u\in\mathcal M$, formulate the Fuglede-Kadison determinant version as

$$\inf_{\gamma\in\Gamma(\nu_a,\nu_b)}\exp\int\log(s+t)\,d\gamma\ \le\ \Delta_\tau(a+ubu^*)\ \le\ \sup_{\gamma\in\Gamma(\nu_a,\nu_b)}\exp\int\log(s+t)\,d\gamma,$$

where $\Delta_\tau(x)=\exp(\tau(\log|x|))$. For normalized matrix trace the bounds are the positive $n$th roots of the extreme permutation products. This determinant retains the modulus, not the complex phase.

## 056 Type II1 factor

Let $\mathcal M$ be a type II1 factor (a finite factor with diffuse projection ranks) with normalized trace $\tau$. Let $a=\sum_i\lambda_i p_i$ and $b=\sum_j\mu_j q_j$ be finite-spectrum positive invertible elements with orthogonal spectral projections summing to one. Define the transportation polytope $\mathcal T=\{m_{ij}\ge0:\sum_j m_{ij}=\tau(p_i),\sum_i m_{ij}=\tau(q_j)\}$. For every unitary $u$ the formulation is

$$\Delta_\tau(a+ubu^*)\in\operatorname{conv}\left\{\exp\left(\sum_{i,j}m_{ij}\log(\lambda_i+\mu_j)\right):m\in\mathcal T\right\}.$$

The real masses are normalized projection dimensions. In the diffuse factor the commuting configurations can realize such masses by splitting projections. In a matrix factor integer rank constraints give the original positive matrix matching interval after normalization.

## 057 Semifinite von Neumann algebra

Let $(\mathcal M,\tau)$ have a faithful normal semifinite trace. Fix a projection $p$ with $0<d=\tau(p)<\infty$. Let $a,b$ be positive invertible in the corner $p\mathcal Mp$, with unit $p$. Let $\nu_a,\nu_b$ be their spectral measures for $\tau/d$. For every unitary $u$ of the corner, with $\Gamma$ the set of probability couplings of these measures,

$$\exp\left(d^{-1}\tau(\log(a+ubu^*))\right)\in\left[\inf_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma,\ \sup_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma\right].$$

The logarithm is calculated in the finite-trace corner, not on the full infinite-trace identity.

## 058 Group von Neumann algebra

Let $G$ be a discrete group and $\mathcal N G$ its group von Neumann algebra on $\ell^2(G)$, with trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$. Let $a,b$ be positive invertible convolution operators with spectral probability measures $\nu_a,\nu_b$. For each unitary $u\in\mathcal N G$ and the set $\Gamma$ of probability couplings of $\nu_a,\nu_b$, the log-determinant comparison is

$$\tau(\log(a+ubu^*))\in\left[\inf_{\gamma\in\Gamma}\int\log(s+t)\,d\gamma,\ \sup_{\gamma\in\Gamma}\int\log(s+t)\,d\gamma\right].$$

Exponentiation gives the corresponding Fuglede-Kadison determinant interval. For a finite group the regular representation supplies a finite matrix specialization.

## 059 Free probability

Let $(\mathcal M,\tau)$ be a tracial von Neumann probability space with faithful normalized trace. Let $a,b$ be freely independent positive invertible self-adjoint variables, with compactly supported probability laws $\nu_a,\nu_b$. Write $\nu_a\boxplus\nu_b$ for their free additive convolution, that is, the law of $a+b$. If $\Gamma$ denotes the classical probability couplings of the two laws, the free determinant comparison is

$$\exp\int\log x\,d(\nu_a\boxplus\nu_b)(x)\in\left[\inf_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma,\ \sup_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma\right].$$

This compares a noncommutative sum with commuting couplings. For nonnormal variables the Brown measure and the absolute determinant do not in general give a complex determinant hull.

## 060 Calkin algebra

Let $H$ be an infinite-dimensional separable Hilbert space, $\mathcal Q(H)=\mathcal B(H)/\mathcal K(H)$ its Calkin algebra, and $q$ the quotient map. Fix a unital matrix subalgebra $\mathcal F\subset\mathcal Q(H)$ and an adjoint-preserving isomorphism $\rho:\mathcal F\to M_n(\mathbb C)$. Suppose $q(A),q(B)\in\mathcal F$ are normal, with represented eigenvalues $\lambda_j,\mu_j$. For each unitary $v\in\mathcal F$,

$$\det(\rho(q(A)+vq(B)v^*))\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The determinant is confined to the specified finite subalgebra and is insensitive to compact perturbations of the lifts. The full Calkin algebra has no ordinary scalar determinant of all elements. The Fredholm index is not such a determinant.

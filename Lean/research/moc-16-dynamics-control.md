# Marcus-de Oliveira formulations: Dynamics, ergodic theory and control

Atlas entries 184–195.

All eigenvalue lists use the indicated multiplicities. $S_n$ is the set of permutations of $\{1,\ldots,n\}$; $U(n)$ is the complex unitary group; $*$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. For normal operators the Marcus-de Oliveira conjecture compares the determinant of the sum over relative unitary positions with the convex hull of products of matched eigenvalue sums. The statements below identify the operator, its spectral length, and the determinant used in each setting. When the native object has no such determinant, the specified realization is part of the formulation.

## 184 Linear discrete dynamics

Let $x_{k+1}=Ax_k$ and $y_{k+1}=By_k$ be linear discrete-time systems on a complex Hilbert state space of dimension $n$, with normal update matrices and eigenvalue lists $\lambda_j,\mu_j$. For every unitary $U$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The left side is the one-step oriented complex volume multiplier of the combined update. The spectral radii of the original systems do not by themselves determine stability of their sum.

## 185 Continuous linear dynamics

Let $\dot x=Ax$ and $\dot y=By$ be continuous-time systems on a common complex Hilbert state space of dimension $n$, with normal generators and eigenvalues $\lambda_j,\mu_j$. For every unitary $U$ and $z\in\mathbb C$,

$$\det(zI-A-UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^n(z-\lambda_j-\mu_{\pi(j)}):\pi\in S_n\right\}.$$

At $z=0$ multiplication by $(-1)^n$ gives the determinant of the combined generator. The exponential-flow determinant $\det e^{t(A+UBU^*)}=e^{t(\operatorname{tr}A+\operatorname{tr}B)}$ is orbit-independent and is not the conjectured hull.

## 186 Floquet theory

Let two $T$-periodic linear systems on $n$ dimensional complex state spaces have fundamental solutions $\Phi_1(t),\Phi_2(t)$ normalized to $I$ at $t=0$. Require their monodromy matrices $A=\Phi_1(T),B=\Phi_2(T)$ normal for chosen Hermitian products. Let $\lambda_j,\mu_j$ be their Floquet multipliers. For every unitary identification $U$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The input determinants are given by the exponentials of the integrals of the generator traces over one period. The sum of monodromy matrices is not assumed to be the monodromy of the sum of the generators. No branch of Floquet exponents is required.

## 187 Oseledets theory

Let two invertible measurable linear cocycles of equal fiber dimension $n$ over ergodic probability-preserving systems satisfy the integrability conditions for the multiplicative ergodic theorem. Let their finite Lyapunov exponent lists $s_j,t_j$ include multiplicities of the Oseledets subspaces. Form positive operators $A=\operatorname{diag}(e^{s_j})$, $B=\operatorname{diag}(e^{t_j})$ on $\mathbb C^n$. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The separate log-determinants are the asymptotic log-volume rates per unit time. This is a comparison of exponent representatives, not a theorem for Lyapunov exponents of sums of cocycles.

## 188 Koopman operators

Let $T,S$ be invertible measure-preserving transformations of probability spaces. Their Koopman operators act by $K_Tf=f\circ T$ and $K_Sg=g\circ S$ on complex $L^2$ spaces and are unitary. Choose finite invariant subspaces of equal positive dimension $n$, on which their restrictions $A,B$ are unitary, with eigenvalues $\lambda_j,\mu_j$ on the unit circle. For every unitary identification $U$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The chosen finite observable spaces supply the determinant. The full Koopman spectrum may be continuous and does not yield an ordinary finite product.

## 189 Transfer operators

Let two dynamical systems have transfer operators $\mathcal L_1,\mathcal L_2$ on specified complex function spaces. Assume there are finite invariant subspaces of equal positive dimension $n$ with normal restrictions $A,B$ in chosen Hermitian products. Let $\lambda_j,\mu_j$ be the transfer eigenvalues in these subspaces. For every unitary identification $U$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

If the full transfer operators are trace class and normal on a Hilbert space, a separate Fredholm version uses $\det_F(I+A+UBU^*)$ with the convergent shifted products. Function-space dependence and nuclear or flat traces cannot be omitted.

## 190 Dynamical zeta functions

Let two dynamical systems admit finite determinant formulas in a specified realization, with normal transfer or induced cohomological operators $A,B$ of equal dimension $n>0$. Let $\lambda_j,\mu_j$ be the eigenvalues indexing their reciprocal zeta factors. For every $z\in\mathbb C$ and every unitary $U$,

$$\det(I-z(A+UBU^*))\in\operatorname{conv}\left\{\prod_{j=1}^n(1-z(\lambda_j+\mu_{\pi(j)})):\pi\in S_n\right\}.$$

The inverse of this determinant, when nonzero, belongs to the reciprocal of the hull with zero removed. Products with signed degree exponents require separate degreewise factors. A periodic-orbit expansion without a finite determinant realization does not supply this matrix statement.

## 191 Thermodynamic formalism

Let $T:X\to X$ and $S:Y\to Y$ be continuous dynamical systems on compact spaces with continuous real potentials $f,g$ and invariant probability measures $\nu,\eta$. Let $\mu_f=f_*\nu$, $\mu_g=g_*\eta$. For any probability coupling $\gamma_0$ of the two laws, define $D(\gamma_0)=\exp\int\log(e^s+e^t)\,d\gamma_0(s,t)$. Let $\Gamma$ be the full coupling set. Then

$$D(\gamma_0)\in\left[\inf_{\gamma\in\Gamma}D(\gamma),\ \sup_{\gamma\in\Gamma}D(\gamma)\right].$$

For equally weighted finite samples, the associated positive potential operators $A=\operatorname{diag}(e^{f_j})$, $B=\operatorname{diag}(e^{g_j})$ satisfy $\det(A+UBU^*)^{1/n}\in[\min_\pi\prod_j(e^{f_j}+e^{g_{\pi(j)}})^{1/n},\max_\pi\prod_j(e^{f_j}+e^{g_{\pi(j)}})^{1/n}]$. Pressure includes entropy and is not this geometric determinant.

## 192 Multifractal analysis

Let two multifractal measures have specified finite samples of $n>0$ local scaling exponents $s_j,t_j$ (each exponent is the limit of log mass divided by log radius, where defined). Form positive scaling operators $A=\operatorname{diag}(e^{s_j})$, $B=\operatorname{diag}(e^{t_j})$. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The separate log-determinants are the sums of the sampled exponents. This is a finite exponent comparison, not a statement that a multifractal dimension function or its Legendre transform is a spectral determinant.

## 193 Control theory

Let two finite-dimensional linear time-invariant control systems have normal state matrices $A,B$ of order $n$, with eigenvalue lists $\lambda_j,\mu_j$. For every unitary change of state coordinates $U$ and complex frequency $s$,

$$\det(sI-(A+UBU^*))\in\operatorname{conv}\left\{\prod_{j=1}^n(s-\lambda_j-\mu_{\pi(j)}):\pi\in S_n\right\}.$$

This is the characteristic determinant of the combined state matrix. Transfer-function poles can cancel unobservable or uncontrollable modes, so the eigenvalue list here includes all state modes. Pseudospectra of nonnormal systems are not this comparison hull.

## 194 Lyapunov stability and LMIs

Let $P,Q$ be positive definite Hermitian Lyapunov matrices of order $n$, for specified systems satisfying the desired strict Lyapunov inequalities. Let $\lambda_j,\mu_j>0$ be their eigenvalues. For every unitary $U$,

$$\det(P+UQU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The ellipsoid $\{x\in\mathbb R^n:x^T(P+UQU^*)x\le1\}$ for real symmetric matrices and orthogonal $U$ has volume equal to the unit-ball volume divided by the positive square root of this determinant. Its volume therefore lies between the reciprocal square roots of the extreme products, with the order reversed. The sum need not satisfy a common Lyapunov inequality unless feasibility is imposed separately.

## 195 Joint spectral radius

Let $\mathcal A,\mathcal B$ be finite families of matrices of order $n$. Fix two finite words of matrices from the respective families and form their products $X=A_{i_m}\cdots A_{i_1}$, $Y=B_{j_\ell}\cdots B_{j_1}$. Suppose $X,Y$ are normal on a common complex Hilbert space. With their eigenvalues $\lambda_j,\mu_j$ and every unitary $U$,

$$\det(X+UYU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The assertion is for every such pair of normal word products. Joint spectral radius is the limiting supremum of growth of word norms and is not a single eigenvalue list. For nonnormal products one can instead use positive singular-value operators $|X|,|Y|$, obtaining a different determinant comparison.

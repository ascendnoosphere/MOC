# Marcus-de Oliveira formulations: Algebraic geometry and stability

Atlas entries 124–135.

All eigenvalue lists use the indicated multiplicities. $S_n$ is the set of permutations of $\{1,\ldots,n\}$; $U(n)$ is the complex unitary group; $*$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. The classical conjecture compares the determinant of a sum of two normal operators with the convex hull of products of matched eigenvalue sums. The following statements specify scalar realizations when the native objects are not complex operators. The chosen realizations and all rank conditions are part of the hypotheses.

## 124 Commutative algebra and schemes

Let $R$ be a commutative unital $\mathbb C$-algebra and let $S$ be a finite locally free commutative $R$-algebra of rank $n>0$. Fix a complex point $x:R\to\mathbb C$ and write $S_x=S\otimes_{R,x}\mathbb C$. For $a,b\in S_x$ define $N_x(c)=\det L_c$, where $L_c$ is multiplication by $c$ on $S_x$. List $\lambda_j,\mu_j$ as the values of $a,b$ at the characters of $S_x$, repeated by the lengths of the corresponding local factors. Then

$$N_x(a+b)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

In this commutative case the joint local-factor list gives one of the permutation products. Prime ideals of an arbitrary scheme are not complex eigenvalues. The spectral length is the finite locally free rank, not Krull dimension.

## 125 Algebraic varieties

Let $X$ be a smooth complex algebraic variety and $f,g:X\to X$ regular maps fixing a common smooth point $x$. On the complex tangent space $T_xX$ of dimension $n>0$ choose a Hermitian product for which $A=df_x,B=dg_x$ are normal. With their eigenvalues $\lambda_j,\mu_j$, for every unitary $U$ on $T_xX$,

$$\det_{T_xX}(df_x+Udg_xU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The determinant is the Jacobian scalar on the top exterior tangent line of the sum of derivatives. This does not require a sum of the maps on the variety.

## 126 Vector bundles

Let $E\to X$ be a Hermitian complex vector bundle of rank $n>0$. Let $A,B$ be bundle endomorphisms that are normal on every fiber. At $x\in X$, write $\lambda_j(x),\mu_j(x)$ for their fiber eigenvalues. For every fiber unitary $U_x$,

$$\det(A_x+U_xB_xU_x^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(\lambda_j(x)+\mu_{\pi(j)}(x)):\pi\in S_n\right\}.$$

The determinant is the scalar action on $\bigwedge^n E_x$. No global continuous selection of convex weights or eigenvalue labels is required.

## 127 Line bundles

Let $L\to X$ be a complex line bundle. For two endomorphisms $A,B$, let $a_x,b_x$ be their scalar actions on the fiber $L_x$. For every fiber unitary $u$,

$$\det(A_x+uB_xu^*)=a_x+b_x\in\mathrm{conv}\{a_x+b_x\}.$$

This is the rank-one form. The unitary orbit is a singleton, and the top exterior power is the line itself.

## 128 Higgs bundles

Let $E$ be a rank-$n$ Hermitian holomorphic vector bundle over a complex curve with Higgs fields $\phi,\psi\in H^0(X,\mathrm{End}(E)\otimes K_X)$, where $K_X$ is the canonical line bundle. At a point $x$, fix a nonzero local generator $\omega$ of $K_X$ and put $A=\phi_x/\omega$, $B=\psi_x/\omega$. Require $A,B$ normal and list their spectral-cover roots $\lambda_j,\mu_j$ in this trivialization. For every unitary $U:E_x\to E_x$,

$$\omega^{-n}\det(\phi_x+U\psi_xU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

A change of trivialization multiplies the scalar determinant and all comparison products by the same complex factor. The untrivialized determinant is a section of $K_X^{\otimes n}$.

## 129 Harder-Narasimhan filtration

Let $E,F$ be vector bundles of the same positive rank $n$ on a smooth projective curve. Repeat each Harder-Narasimhan slope $s=\deg Q/\mathrm{rk}Q$ of a semistable graded quotient according to its rank, obtaining lists $s_j,t_j$. On Hermitian spaces of dimension $n$ let $A$ and $B$ act by $e^{s}$ and $e^{t}$ on orthogonal copies of these graded components. For every unitary identification $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

In this slope realization $\log\det A=\deg E=\deg\det E$, and likewise for $F$. The left side is the determinant of a sum of positive slope operators, not the degree of an unspecified sum of vector bundles.

## 130 Toric algebraic geometry

Let $L_1,L_2$ be torus-linearized line bundles on projective toric varieties with spaces of global sections of the same positive dimension $n$. Enumerate their torus weights $a_j,b_j$ in the character lattice, with multiplicities. For every point $z$ of the complex algebraic torus let $A(z),B(z)$ be the diagonal weight actions with eigenvalues $z^{a_j},z^{b_j}$ on orthogonal weight bases. Then for every unitary identification $U$,

$$\det(A(z)+UB(z)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(z^{a_j}+z^{b_{\pi(j)}}):\pi\in S_n\right\}.$$

The determinants of the individual operators are the determinant characters. The lattice polytope indexes the weights but its volume is not this determinant.

## 131 Newton-Okounkov theory

Let $D,E$ be big divisors with a specified full-rank valuation on their graded section algebras, and fix a degree $m$ in which the section spaces have equal finite dimension $n>0$. Choose valuation-adapted bases, with valuation vectors $a_j,b_j\in\mathbb Z^r$ (count repetitions if leaves have dimension greater than one). For any scalar evaluation $L:\mathbb R^r\to\mathbb C$ linear over $\mathbb R$, let $A=\mathrm{diag}(L(a_j/m))$ and $B=\mathrm{diag}(L(b_j/m))$. For every unitary $U$,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(L(a_j/m)+L(b_{\pi(j)}/m)):\pi\in S_{n}\right\}.$$

This is a fixed-degree valuation-operator determinant. The Newton-Okounkov body is a limit of normalized valuation data; its Euclidean volume is a different invariant. The conjecture does not presume convergence of the unnormalized determinants as $m$ increases.

## 132 Intersection theory

Let $X$ be a smooth projective complex variety of dimension $2k$. Choose an $n$ dimensional real space of numerical codimension-$k$ cycle classes with a basis $z_i$ and a positive Euclidean inner product that makes the basis orthonormal. Let $A,B$ be real symmetric matrices of two specified intersection pairings on this space, for example pairings obtained from algebraic correspondences that are self-adjoint. Let $\lambda_j,\mu_j$ be their real eigenvalues. For every orthogonal $Q$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This is a determinant of the finite intersection forms. Their basis, inner product and the two pairings must be fixed. Effective and nef cones alone do not specify these matrices.

## 133 Chern-Weil theory

Let $E\to X$ have complex rank $n$ and two unitary connections with curvature two-forms $F_1,F_2$. At a point $x$ and two fixed real tangent vectors $v,w$, define the Hermitian endomorphisms $A=(i/2\pi)F_1(v,w)$, $B=(i/2\pi)F_2(v,w)$. Let $\lambda_j,\mu_j$ be their real eigenvalues. For every fiber unitary $U$,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The scalar determinant uses curvature evaluated on a pair of tangent vectors. It is not evaluation of a top Chern form on $2n$ vectors; the latter involves exterior products of two-forms. Formal Chern roots do not have an ordinary real convex hull without a scalar evaluation.

## 134 Virtual enumerative geometry

Let a perfect obstruction theory at a complex point be represented by a two-term complex $E^{-1}\to E^0$ of finite-dimensional spaces. Choose two compatible endomorphisms inducing normal maps $A_k,B_k$ on each cohomology group $V_k=H^k(E^\bullet)$, $k=-1,0$, with fixed Hermitian products. Let $\lambda_{kj},\mu_{kj}$ denote the spectral lists of length $n_k$. For unitary $U_k$ define $C_k=A_k+U_kB_kU_k^*$ and

$$P_k=\mathrm{conv}\left\{\prod_{j=1}^{n_k}(\lambda_{kj}+\mu_{k,\pi(j)}):\pi\in S_{n_k}\right\}.$$

The statement is $\det C_k\in P_k$ for each degree. If $C_{-1}$ is invertible the scalar on the virtual determinant line is in $\{z_0/z_{-1}:z_0\in P_0,\ z_{-1}\in P_{-1}\setminus\{0\}\}$. The virtual dimension is a signed rank and does not define positive spectral multiplicity; virtual enumerative counts are not determinants of these sums.

## 135 Arakelov geometry

Let $E,F$ be Hermitian arithmetic vector bundles of equal positive rank $n$ over the integers of a number field. In a fixed arithmetic slope normalization, let $s_j,t_j$ be their arithmetic Harder-Narasimhan slopes repeated by quotient ranks, so their sums are the normalized arithmetic degrees. On orthogonal copies of their graded spaces define positive operators $A=\mathrm{diag}(e^{s_j})$ and $B=\mathrm{diag}(e^{t_j})$ at a chosen complex realization. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The individual log-determinants equal the specified normalized degrees of the metrized determinant lines. The comparison uses the slope realization; it is not a formula for the arithmetic degree of a sum of arithmetic bundles.

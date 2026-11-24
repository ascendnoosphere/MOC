# Marcus-de Oliveira formulations: Representation theory and harmonic analysis

Atlas entries 148–159.

All eigenvalue lists use the indicated multiplicities. $S_n$ is the set of permutations of $\{1,\ldots,n\}$; $U(n)$ is the complex unitary group; $*$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. The classical conjecture compares the determinant of a sum of two normal operators with the convex hull of products of matched eigenvalue sums. The following statements specify scalar realizations when the native objects are not complex operators. The chosen realizations and all rank conditions are part of the hypotheses.

## 148 Finite group representations

Let $\rho,\eta$ be complex representations of a finite group $G$ on Hilbert spaces of equal dimension $n>0$, with group-invariant Hermitian products. For $g,h\in G$, put $A=\rho(g)$ and $B=\eta(h)$; both are unitary. Let $\lambda_j,\mu_j$ be their eigenvalues, roots of unity with multiplicity. For every unitary identification $U$,

$$\det(\rho(g)+U\eta(h)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The individual traces are character values. The statement compares sums of group actions, not the character of the group product.

## 149 Lie algebra representations

Let $V,W$ be finite-dimensional complex weight representations of a semisimple complex Lie algebra with a fixed Cartan subalgebra $\mathfrak h$ and equal dimension $n$. List the weights $a_j,b_j\in\mathfrak h^*$ by weight multiplicity. Choose Hermitian products with orthogonal weight spaces. For every $h\in\mathfrak h$ the actions $A=\rho_V(h)$ and $B=\rho_W(h)$ are normal with eigenvalues $a_j(h),b_j(h)$. For every unitary identification $U$,

$$\det(\rho_V(h)+U\rho_W(h)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(a_j(h)+b_{\pi(j)}(h)):\pi\in S_n\right\}.$$

The determinant representation of the associated torus has weight equal to the sum of the individual weights. The scalar product comparison is at the chosen Cartan element.

## 150 Highest-weight theory

Let $V_\lambda,V_\mu$ be irreducible finite-dimensional representations of a connected compact Lie group with highest weights $\lambda,\mu$ and common dimension $n$. Fix a maximal torus and list all weights $a_j,b_j$ including multiplicities, not only the Weyl-orbit vertices. For each torus element $t$ let $A(t),B(t)$ be the represented unitary actions. For every unitary identification $U$,

$$\det(A(t)+UB(t)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(a_j(t)+b_{\pi(j)}(t)):\pi\in S_n\right\}.$$

Here $a_j(t),b_j(t)$ are unit-circle character values. Weyl dimension supplies $n$; the highest-weight polytope alone does not supply the weight multiplicities.

## 151 Root systems

Let $\Phi,\Psi$ be reduced crystallographic root systems of equal cardinality $n>0$, with roots enumerated as $a_j,b_j$. Fix real-linear scalar evaluations $L_\Phi,L_\Psi$ of their root spaces into $\mathbb C$. On the root-indexed Hilbert spaces define diagonal normal operators $A e_j=L_\Phi(a_j)e_j$ and $B f_j=L_\Psi(b_j)f_j$. For each unitary identification $U$,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(L_\Phi(a_j)+L_\Psi(b_{\pi(j)})):\pi\in S_n\right\}.$$

The root sums vanish in both systems. The determinant of the root-value operator is not the Cartan matrix determinant, and $n$ is root count rather than root-system rank.

## 152 Weyl group representations

Let $W$ be a Weyl group acting on a real Euclidean reflection space of dimension $n>0$. Let $w,v\in W$ act by orthogonal matrices $A,B$. Their complex eigenvalues $\lambda_j,\mu_j$ are roots of unity. For every orthogonal $Q$ on the reflection space, or every unitary $U$ on its complexification,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The determinants of the inputs are their sign characters. The full permutation set refers to the eigenvalue list, not just the permutations available from Weyl-group elements.

## 153 Compact-group harmonic analysis

Let $G$ be a compact group and $\rho$ an irreducible unitary representation of dimension $n>0$. For integrable functions $f,g$ on $G$ define Fourier matrices $A=\int_G f(x)\rho(x)^*\,dx$, $B=\int_G g(x)\rho(x)^*\,dx$ using normalized Haar measure. Require $A,B$ normal, and let $\lambda_j,\mu_j$ be their eigenvalues in this block. For every unitary $U\in U(n)$,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The comparison is within a Peter-Weyl block. Infinite sums over irreducible representations require additional determinant summability conditions.

## 154 Abelian Fourier analysis

Let $G$ be a locally compact abelian group and let $f,g$ be bounded real positive Fourier multiplier symbols on its character group, restricted to a measurable region with a specified probability measure $\nu$. Assume they are bounded away from zero. Let $\mu_f,\mu_g$ be their pushforward laws and $\Gamma$ their probability couplings. The Fourier geometric determinant $D(h)=\exp\int\log h\,d\nu$ satisfies

$$D(f+g)\in\left[\inf_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma,\ \sup_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma\right].$$

The common Fourier variable supplies a coupling. For finite equal-mass frequencies, permutation matchings give the extreme products. The infinite Haar measure is not normalized without a finite measure choice.

## 155 Hecke algebras

Let $\mathcal H$ be a Hecke algebra acting on a finite-dimensional Hilbert space $V$ of automorphic forms of dimension $n>0$. Let $T,S\in\mathcal H$ act by normal operators $A,B$ on $V$, for instance elements in an adjoint-closed commuting Hecke algebra. Let $\lambda_j,\mu_j$ be their Hecke eigenvalues. For every unitary $U$ of $V$,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

For commuting Hecke actions the identity relative position is a permutation value. General $U$ need not intertwine the Hecke algebra.

## 156 Satake parameters

Let $s,t$ be semisimple Satake conjugacy parameters in a complex dual reductive group. Fix a finite-dimensional complex representation $r$ of the dual group of dimension $n$. Choose normal representatives $A,B$ of the conjugacy classes of $r(s),r(t)$, with eigenvalues $\lambda_j,\mu_j$ in orthonormal eigenbases. For each unitary $U$ and $z\in\mathbb C$,

$$\det(I-z(A+UBU^*))\in\mathrm{conv}\left\{\prod_{j=1}^n(1-z(\lambda_j+\mu_{\pi(j)})):\pi\in S_n\right\}.$$

The local Euler determinant is evaluated in the chosen representation; its eigenvalues include weight multiplicities. The sum is not required to arise from another dual-group element.

## 157 Tensor categories of representations

Let $\mathcal C$ be a tensor category equipped with a complex linear realization functor to finite-dimensional Hilbert spaces. Choose objects $X,Y$ with realized dimension $n>0$ and endomorphisms $f,g$ whose realized maps $A,B$ are normal. Let $\lambda_j,\mu_j$ be the eigenvalues in the realization. For every unitary $U$ between the realized spaces,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The determinant is the ordinary scalar on the top exterior power of the realized space. A quantum or categorical dimension is not used as an integer permutation length unless the realization identifies it with that length.

## 158 Association schemes

Let two association schemes have the same number $n>0$ of vertices. In their complex Bose-Mesner algebras choose elements $A=\sum_i a_i A_i$, $B=\sum_i b_i B_i$, where the adjacency matrices form commuting adjoint-closed algebras. They are normal. Let the eigenvalues of each algebra element be listed using its eigenmatrix entries with the multiplicities of the primitive idempotents. Denote the lists by $\lambda_j,\mu_j$. For every unitary identification $U$ of vertex spaces,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The hull uses the vertex-space spectral length, not the number of distinct adjacency classes. The sum need not be an adjacency matrix of a scheme.

## 159 Spherical harmonic analysis

On the unit sphere $S^r$, $r\ge1$, the nonnegative Laplace eigenvalue of degree $\ell$ is $\ell(\ell+r-1)$ with its spherical-harmonic multiplicity. Choose two finite sums of harmonic eigenspaces (possibly on spheres of different dimensions) having the same positive total dimension $n$. Let $A,B$ be their restricted Laplace operators, with eigenvalue lists $\lambda_j,\mu_j$ including the full selected multiplicities. For every unitary identification $U$,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The determinant is over the chosen harmonic spectral windows. The complete heat trace and zeta determinant need separate infinite-dimensional regularization.

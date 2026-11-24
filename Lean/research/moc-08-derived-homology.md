# Marcus-de Oliveira formulations: Derived, higher and generalized homological theories

Atlas entries 085–098.

All finite eigenvalue lists include multiplicities unless stated otherwise. $S_n$ denotes the permutations of $\{1,\ldots,n\}$, $U(n)$ the unitary group, $*$ the Hermitian adjoint and $\mathrm{conv}$ the real-affine convex hull. For normal complex operators $A,B$ of order $n$, the Marcus-de Oliveira conjecture compares $\det(A+UBU^*)$ with the products $\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)})$ of matched eigenvalue sums. The statements below specify the required operator and determinant for each object. An auxiliary realization is part of a formulation where the object itself has no scalar determinant.

## 085 Hypercohomology

Let $\mathcal C^\bullet$ be a bounded complex of sheaves of complex vector spaces on $X$. Suppose its hypercohomology spaces $V_k=\mathbb H^k(X,\mathcal C^\bullet)$ are finite-dimensional, and choose Hermitian inner products. Let two derived endomorphisms induce normal maps $F_k,G_k$ with eigenvalues $\lambda_{kj},\mu_{kj}$, $1\le j\le n_k=\dim V_k$. For every family of unitary maps $U_k$ on the nonzero spaces, the degreewise determinant scalars satisfy

$$D_k=\det(F_k+U_kG_kU_k^*)\in P_k=\mathrm{conv}\left\{\prod_{j=1}^{n_k}(\lambda_{kj}+\mu_{k,\pi(j)}):\pi\in S_{n_k}\right\}.$$

If every odd-degree $D_k$ is nonzero, the scalar on the alternating determinant line belongs to $\{\prod_k z_k^{(-1)^k}:z_k\in P_k,\ z_k\ne0\text{ in odd degree}\}$. This set is a product of hulls and inverse hulls, not a single convex hull. The alternating trace uses signs and does not define positive spectral multiplicities.

## 086 Hochschild homology

Let $\mathcal A$ be a complex associative algebra with $V=HH_k(\mathcal A)$ of dimension $n>0$. Let $f,g:\mathcal A\to\mathcal A$ be algebra endomorphisms inducing normal linear maps $F=HH_k(f),G=HH_k(g)$ in a chosen Hermitian inner product. For their eigenvalues $\lambda_j,\mu_j$ and every unitary $U$ on $V$,

$$\det_V(HH_k(f)+UHH_k(g)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Here Hochschild homology is the homology of the Hochschild chain complex with coefficients in the algebra itself.

## 087 Hochschild cohomology

Let $\mathcal A$ be a complex associative algebra with finite positive $n=\dim HH^k(\mathcal A,\mathcal A)$. Let $f,g$ be algebra automorphisms. Each acts on Hochschild cochains by conjugating the output and applying the inverse to all inputs; let $F,G$ be the induced cohomology maps. Assume $F,G$ are normal for a fixed Hermitian product. With their eigenvalues $\lambda_j,\mu_j$, for every unitary $U$ on $HH^k(\mathcal A,\mathcal A)$,

$$\det(F+UGU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

## 088 Cyclic homology

Let $\mathcal A$ be a complex unital algebra for which the cyclic homology group $HC_k(\mathcal A)$ has dimension $n>0$. Let two unital algebra endomorphisms induce $F,G$ on this group, both normal for a fixed Hermitian product. If $\lambda_j,\mu_j$ are their eigenvalues, then for every unitary $U$ on $HC_k(\mathcal A)$,

$$\det(F+UGU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Use the specified cyclic degree rather than the Euler characteristic of the cyclic complex.

## 089 Equivariant cohomology

Let a compact torus $T$ act on a space $X$. Let $R=H^*(BT;\mathbb C)$, the coefficient ring of Borel equivariant cohomology. Choose a finite free $R$-module of equivariant cohomology preserved by two induced $R$-linear maps $F,G$ and choose a character $x:R\to\mathbb C$. In the specialized space $V_x$ of rank $n>0$, assume $F_x,G_x$ normal with eigenvalues $\lambda_j,\mu_j$. For every unitary $U$ of $V_x$,

$$\det(F_x+UG_xU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The scalar specialization is required before taking the ordinary real-affine hull.

## 090 L2-homology

Let $G$ be a discrete group acting on a finite-type free cellular chain complex. Fix a degree and a finite positive von Neumann dimension $d$ of a Hilbert $\mathcal N G$-module $V$, for example the reduced $L^2$ homology module. Let $A,B$ be positive invertible equivariant endomorphisms of $V$. Let $\tau$ denote the module trace, and $\nu_A,\nu_B$ the spectral probability measures for $\tau/d$. For every equivariant unitary $U$, with $\Gamma$ the probability couplings of these measures,

$$\exp(d^{-1}\tau(\log(A+UBU^*)))\in\left[\inf_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma,\ \sup_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma\right].$$

The left side is the normalized Fuglede-Kadison determinant in the endomorphism algebra. It uses positive invertible operators, not the zero eigenvalues of a Laplacian.

## 091 Persistent homology

Let two finite persistence barcodes in the same degree have $n>0$ finite intervals $[b_j,d_j)$ and $[c_j,e_j)$, with lifetimes $\lambda_j=d_j-b_j>0$ and $\mu_j=e_j-c_j>0$. Associate to the barcodes the positive lifetime operators $A=\mathrm{diag}(\lambda_j)$ and $B=\mathrm{diag}(\mu_j)$ on $\mathbb C^n$. For every unitary $U$,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This compares lifetime products for a chosen linear combination of barcode coordinates. It is not a claim that an arbitrary unitary mixing is a morphism of persistence modules or that this determinant is intrinsic to the category.

## 092 Spectral sequences

Let $(E_r^{p,q},d_r)$ be a spectral sequence of complex vector spaces. Fix a page and a bidegree with $n=\dim E_r^{p,q}>0$ finite. Let two compatible spectral-sequence maps induce normal operators $F_r^{p,q},G_r^{p,q}$ in a fixed Hermitian inner product, with eigenvalues $\lambda_j,\mu_j$. For every unitary $U$ on that bidegree,

$$\det(F_r^{p,q}+UG_r^{p,q}U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Page differentials and passage to the next page may change spectral multiplicities. No common weights across pages are required.

## 093 Superalgebra

Let $V=V_{\bar0}\oplus V_{\bar1}$ be a finite complex super vector space with positive Hermitian inner products on its two summands. Let $A,B$ be even normal operators, with block eigenvalues $\lambda_{\epsilon j},\mu_{\epsilon j}$ of length $n_\epsilon$. For every even unitary $U=U_0\oplus U_1$ define $C_\epsilon=A_\epsilon+U_\epsilon B_\epsilon U_\epsilon^*$ and

$$P_\epsilon=\mathrm{conv}\left\{\prod_{j=1}^{n_\epsilon}(\lambda_{\epsilon j}+\mu_{\epsilon,\pi(j)}):\pi\in S_{n_\epsilon}\right\}.$$

The formulation is $\det C_\epsilon\in P_\epsilon$ in each parity. If $C_1$ is invertible, the Berezinian (superdeterminant) satisfies

$$\mathrm{Ber}(A+UBU^*)\in\{z_0/z_1:z_0\in P_0,\ z_1\in P_1\setminus\{0\}\}.$$

A zero-dimensional block has determinant one. Signed superdimension cannot replace the two spectral lengths.

## 094 Perfect complexes

Let $C^\bullet$ be a bounded perfect complex of complex vector spaces, and let derived endomorphisms $f,g$ induce normal $F_k,G_k$ on each finite-dimensional cohomology $H^k(C^\bullet)$, with a fixed Hermitian product there. Let their eigenvalues be $\lambda_{kj},\mu_{kj}$ of length $n_k$. For each family of unitary $U_k$, set $D_k=\det(F_k+U_kG_kU_k^*)$ and

$$P_k=\mathrm{conv}\left\{\prod_{j=1}^{n_k}(\lambda_{kj}+\mu_{k,\pi(j)}):\pi\in S_{n_k}\right\}.$$

The conjecture is $D_k\in P_k$ for each $k$. If the odd-degree maps of the sum are invertible, its induced scalar on the determinant line $\bigotimes_k(\bigwedge^{n_k}H^k)^{(-1)^k}$ lies in $\{\prod_k z_k^{(-1)^k}:z_k\in P_k,\ z_k\ne0\text{ for odd }k\}$. A determinant line is a line, not a number until a scalar action is specified.

## 095 Reidemeister torsion

Let $C^\bullet$ be a finite acyclic based complex. In each degree choose a splitting into boundaries and lifts of boundaries. The change-of-basis isomorphism $T_k$ from an adapted basis to the given basis has determinant entering Reidemeister torsion with exponent $\epsilon_k=(-1)^{k+1}$ (fix this convention). Choose two families of invertible normal change-of-basis matrices $A_k,B_k$ on the same based spaces, with eigenvalues $\lambda_{kj},\mu_{kj}$. For every unitary $U_k$ for which $C_k=A_k+U_kB_kU_k^*$ is invertible, define $P_k$ as the hull of $\prod_j(\lambda_{kj}+\mu_{k,\pi(j)})$ over $S_{n_k}$. The torsion-factor form is

$$\prod_k(\det C_k)^{\epsilon_k}\in\left\{\prod_k z_k^{\epsilon_k}:z_k\in P_k\setminus\{0\}\right\}.$$

When the $C_k$ are adapted basis changes of an acyclic complex, this product is its torsion in the stated convention. The condition of being an adapted basis change is additional to the matrix conjecture.

## 096 Ray-Singer analytic torsion

Let $M$ be a closed Riemannian manifold and choose two Hodge Laplacians in each degree $k$. Fix $n_k$ positive eigenmodes of each, with eigenvalues $\lambda_{kj},\mu_{kj}>0$, and let $A_k,B_k$ be the corresponding restricted positive operators on identified Hilbert spaces. For unitary $U_k$, define the finite spectral torsion of their sums by $\log T=\frac12\sum_k(-1)^{k+1}k\log\det(A_k+U_kB_kU_k^*)$. Let $l_k$ and $h_k$ be the minimum and maximum of $\sum_j\log(\lambda_{kj}+\mu_{k,\pi(j)})$ over permutations. Put $c_k=(-1)^{k+1}k/2$. Then

$$\sum_k\min(c_kl_k,c_kh_k)\le\log T\le\sum_k\max(c_kl_k,c_kh_k).$$

The finite spectral torsion has the same signed weights as Ray-Singer torsion. Passing to the zeta-regularized invariant requires a separate convergence argument.

## 097 L2-torsion

Let $C^\bullet$ be a finite-type Hilbert chain complex over a group von Neumann algebra, and let $A_k,B_k$ be positive invertible equivariant operators on its nonzero finite-trace terms. Let $\tau_k$ be the finite module trace and $d_k=\tau_k(1)$, and let $\Gamma_k$ be the probability couplings of their normalized spectral measures. For each equivariant unitary $U_k$ put $L_k=\tau_k(\log(A_k+U_kB_kU_k^*))$ and let $l_k,h_k$ be the infimum and supremum of $d_k\int\log(s+t)\,d\gamma$ for $\gamma\in\Gamma_k$. For torsion weights $c_k=(-1)^{k+1}k/2$, the comparison is

$$\sum_k\min(c_kl_k,c_kh_k)\le\sum_k c_kL_k\le\sum_k\max(c_kl_k,c_kh_k).$$

This is the Laplacian log-determinant version on a finite collection of determinant-class positive operators. For an actual $L^2$-torsion invariant require the appropriate acyclicity, kernel removal and differential compatibility.

## 098 Lefschetz fixed-point theory

Let $X$ be a finite CW complex and $f,g:X\to X$ continuous maps. For each nonzero finite-dimensional homology space $H_k(X;\mathbb C)$ suppose the induced operators $F_k,G_k$ are normal for a fixed Hermitian product. Let $\lambda_{kj},\mu_{kj}$ be their eigenvalues, and $U_k$ arbitrary unitary operators in those degrees. Then the degreewise Lefschetz determinant form is

$$\det(F_k+U_kG_kU_k^*)\in\mathrm{conv}\left\{\prod_j(\lambda_{kj}+\mu_{k,\pi(j)}):\pi\in S_{n_k}\right\}.$$

The Lefschetz trace of the graded sum is $\sum_k(-1)^k\sum_j(\lambda_{kj}+\mu_{kj})$, independent of $U_k$. If the sum is induced by a map of spaces, this is its Lefschetz number. Alternating determinant products use the product of degreewise hulls with inverses in odd degree, not a hull of signed trace averages.

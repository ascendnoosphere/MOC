# Marcus-de Oliveira formulations: Differential geometry, curvature and local geometry

Atlas entries 099–111.

All finite eigenvalue lists include multiplicities unless stated otherwise. $S_n$ denotes the permutations of $\{1,\ldots,n\}$, $U(n)$ the unitary group, $*$ the Hermitian adjoint and $\mathrm{conv}$ the real-affine convex hull. For normal complex operators $A,B$ of order $n$, the Marcus-de Oliveira conjecture compares $\det(A+UBU^*)$ with the products $\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)})$ of matched eigenvalue sums. The statements below specify the required operator and determinant for each object. An auxiliary realization is part of a formulation where the object itself has no scalar determinant.

## 099 Euclidean linear deformation

Let $F,G:\mathbb R^n\to\mathbb R^n$ be linear deformations. Let $A=(F^TF)^{1/2}$, $B=(G^TG)^{1/2}$ be their positive stretch operators with principal stretches $\lambda_j,\mu_j\ge0$. For every orthogonal $Q$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This is the unsigned Jacobian of the combined stretch operator. It does not assert a bound for the oriented determinant of $F+QGQ^T$ from singular values alone.

## 100 Affine geometry

Let $f(x)=Ax+a$ and $g(x)=Bx+b$ be affine maps of a complex affine space with a fixed Hermitian inner product on its translation space of dimension $n$. Assume $A,B$ normal with eigenvalues $\lambda_j,\mu_j$. For every unitary $U$ of the translation space,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Translation parts do not affect the affine volume multiplier. The left side is the determinant of the linear part of the sum after identification of the affine origin.

## 101 Projective geometry

Let $f,g$ be projective linear transformations of $\mathbb P(\mathbb C^n)$. Fix invertible normal linear lifts $A,B\in GL_n(\mathbb C)$, including a specified choice of their nonzero scalar factors. Let $\lambda_j,\mu_j$ be the eigenvalues of those lifts. For every unitary $U$ on the lift space,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The scalar is a lift-dependent determinant. Projective eigenvalue ratios do not determine it without the lift normalization, and the sum can be singular.

## 102 Differential topology

Let $f,g:M\to M$ be smooth maps of an $n$ dimensional manifold with a common fixed point $x$. Fix an inner product on $T_xM$. Assume the complexified derivatives $A=df_x,B=dg_x$ are normal with eigenvalues $\lambda_j,\mu_j$. For every orthogonal $Q:T_xM\to T_xM$,

$$\det(I-A-QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^n(1-\lambda_j-\mu_{\pi(j)}):\pi\in S_n\right\}.$$

The determinant is the local fixed-point index determinant for a map whose linearization is $A+QBQ^T$; its sign gives the index if that determinant is nonzero. This does not define a global sum of manifold maps.

## 103 Riemannian geometry

Let $g_0,g_1,g_2$ be positive Riemannian metrics at a point of an $n$ dimensional manifold. On the tangent space with metric $g_0$ define positive endomorphisms $A=g_0^{-1}g_1$, $B=g_0^{-1}g_2$ by $g_0(Ax,y)=g_1(x,y)$ and the corresponding rule for $B$. Let $\lambda_j,\mu_j>0$ be their eigenvalues. For every $g_0$-orthogonal $Q$,

$$\det(A+QBQ^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The square root is the ratio of the volume density of the metric $g_1+g_2(Q^{-1}\cdot,Q^{-1}\cdot)$ to that of $g_0$. Its bounds are the positive square roots of the extreme permutation products.

## 104 Pseudo-Riemannian geometry

Let $g_0$ be a nondegenerate symmetric form of signature $(p,q)$ on a real space of dimension $n=p+q$, and let $A=g_0^{-1}g_1$, $B=g_0^{-1}g_2$ for two other nondegenerate symmetric forms. Fix a positive Hermitian inner product on the complexification for which $A,B$ are normal. For their complex eigenvalues $\lambda_j,\mu_j$ and every unitary $U$ for this positive inner product that also preserves the complex bilinear extension of $g_0$,

$$\det(A+UBU^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Self-adjointness for an indefinite metric alone does not imply normality for a positive inner product. The determinant may have either real sign for real $U$; no positivity is assumed.

## 105 Hypersurface geometry

Let two hypersurface second fundamental forms at a common identified $n$ dimensional Euclidean tangent space have self-adjoint shape operators $A,B$. Their principal curvatures are $\lambda_j,\mu_j$ with multiplicity. For every orthogonal $Q$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This is the Gauss-Kronecker curvature of the combined shape operator, when that operator is realized by a hypersurface. Its trace is the sum of principal curvatures, not the determinant.

## 106 Ricci geometry

Fix a positive metric $g$ at a point of an $n$ dimensional manifold and two symmetric Ricci tensors $R_1,R_2$ on that tangent space. Let $A=g^{-1}R_1$, $B=g^{-1}R_2$ and let $\lambda_j,\mu_j$ be their real Ricci eigenvalues. For each $g$-orthogonal $Q$,

$$\det(A+QBQ^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The trace is the scalar curvature of the combined tensor relative to $g$. The bound concerns the determinant of its Ricci endomorphism, whether or not the combined tensor is globally realizable.

## 107 Curvature operator

Let $V$ be a real Euclidean space of dimension $r\ge2$ and let $A,B$ be self-adjoint algebraic curvature operators on $\bigwedge^2 V$, defined using the curvature tensor and the induced inner product. Put $n=\binom r2$ and let $\lambda_j,\mu_j$ be the eigenvalues. For every orthogonal $Q$ on $\bigwedge^2 V$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

If $Q=\bigwedge^2 q$ for an orthogonal $q$ on $V$, the transformed curvature operator retains the algebraic curvature symmetries. The trace is half the scalar curvature in the usual convention.

## 108 Kähler geometry

Let $h_0,h_1,h_2$ be positive Hermitian metrics on the complex tangent space of a Kähler manifold at a point, with complex dimension $n$. Put $A=h_0^{-1}h_1$, $B=h_0^{-1}h_2$. For their positive Hermitian eigenvalues $\lambda_j,\mu_j$ and every $h_0$-unitary $U$,

$$\det_{\mathbb C}(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This complex determinant is the volume-density ratio of the combined Hermitian metric relative to $h_0$ (with the same complex orientation). The real tangent dimension is $2n$.

## 109 Finsler geometry

Let $F_0,F_1,F_2$ be strongly convex Finsler metrics. At a fixed nonzero tangent vector $v$, their fundamental tensors are $g_i(v)=\frac12 D_v^2 F_i^2$, positive bilinear forms. On the $n$ dimensional tangent space with metric $g_0(v)$ let $A=g_0(v)^{-1}g_1(v)$ and $B=g_0(v)^{-1}g_2(v)$, with eigenvalues $\lambda_j,\mu_j$. For each $g_0(v)$-orthogonal $Q$,

$$\det(A+QBQ^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The comparison is at the specified direction $v$; it does not identify the fundamental tensors in different directions or assert a global Finsler volume formula.

## 110 Hessian and Monge-Ampere geometry

Let $u,v$ be twice differentiable real functions on an open set of $\mathbb R^n$. At a point $x$ let $\lambda_j,\mu_j$ be the real eigenvalues of $D^2u(x),D^2v(x)$. For every orthogonal $Q$,

$$\det(D^2u(x)+QD^2v(x)Q^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

For convex functions this is the nonnegative Monge-Ampere density of $u(y)+v(x+Q^T(y-x))$ at $x$. The Laplacian is the additive trace.

## 111 Geometric measure theory

Let $M$ be a $k$-rectifiable set and let $F,G$ be Lipschitz maps with approximate differentials at a point where the approximate tangent $T$ has dimension $k>0$. Let $A=|d_{\rm ap}F|$, $B=|d_{\rm ap}G|$ denote the positive square roots of the two Gram endomorphisms of $T$. Write $\lambda_j,\mu_j$ for the $k$ singular values of the differentials, including zeros. For each orthogonal $Q$ on $T$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{k}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{k}\right\}.$$

The determinant is the $k$-Jacobian of this combined positive stretch on $T$. It does not assert that the Jacobian of the sum of the original maps is determined by their singular values.

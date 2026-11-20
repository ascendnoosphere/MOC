# Exact two-row fibers, averaging, and coupled escape

Let A=D_a, let B=UD_bU*, and M=A+B. We study f=Re(eta det M) on the unitary orbit of B.

## Every two-row fiber is an affine image of a Bloch sphere

Fix i<j and move the SU(2) rotation from B onto A. Put d=(a_i-a_j)/2 and c=(a_i+a_j)/2. On the selected two-dimensional block, the rotated A is

\[
cI_2+d(n_1\sigma_1+n_2\sigma_2+n_3\sigma_3),\qquad n\in S^2.
\]

Write C=adj M and D=det M[S^c,S^c], S={i,j}. Choose sigma_2=[[0,-i],[i,0]]. Direct rank-two determinant expansion gives

\[
\det M(n)=\det M+L_1n_1+L_2n_2+L_3(n_3-1),
\tag{1}
\]

where

\[
L_1=d(C_{ij}+C_{ji}),\quad
L_2=i d(C_{ij}-C_{ji}),\quad
L_3=d(C_{ii}-C_{jj})+2d^2D.
\tag{2}
\]

For the derivation, Delta=d(n·sigma-sigma_3) and det Delta=-2d²(1-n_3). The determinant expansion is det M+tr(C Delta)+D det Delta. This proof is polynomial, so it does not assume invertibility of M or of the complementary principal block.

The image of the full sphere under the real linear map to C is a filled ellipse, possibly a segment or a point. With ell_k=Re(eta L_k), the exact maximum on the fiber is

\[
f-\ell_3+\sqrt{\ell_1^2+\ell_2^2+\ell_3^2}.
\tag{3}
\]

At a global maximum on the whole unitary orbit, every pair must satisfy ell_1=ell_2=0 and ell_3≥0. The first two conditions are the off-diagonal form of eta[adj M,A] being Hermitian. These are necessary conditions, not sufficient conditions for the full orbit maximum.

## Configuration for a coupled escape

Let

\[
a=(i,i,-i,-i),\quad b=(-3,-1,-2,0),\qquad
O=\frac12\begin{pmatrix}
1&1&1&1\\1&-1&1&-1\\1&1&-1&-1\\1&-1&-1&1
\end{pmatrix},\quad\eta=1.
\]

Then

\[
B=OD_bO^T=
\begin{pmatrix}
-3/2&-1&-1/2&0\\
-1&-3/2&0&-1/2\\
-1/2&0&-3/2&-1\\
0&-1/2&-1&-3/2
\end{pmatrix},
\qquad \det(A+B)=7.
\]

The permutation support maximum is 8: the two plus-i positions select a two-element subset of b, and the six such subsets have real products with maximum 8.

## A coherent four-coordinate escape

Let K have K_14=K_23=1, K_41=K_32=-1, and all other entries zero. Use the orbit path that moves exp(theta K) onto A. Since K²=-I, this is simultaneous rotation in the two complementary coordinate planes.

Using the two by two tensor decomposition and diagonalizing the second Pauli-X factor, the two determinant factors are

\[
7+i\sin(2\theta),\qquad 1-i\sin(2\theta)
\]

up to simultaneous conjugation from the sign convention for theta. Therefore

\[
\boxed{\operatorname{Re}\det M(\theta)=7+\sin^2(2\theta).}
\tag{4}
\]

At theta=pi/4 the path reaches the permutation support value 8. The four real cross-block tangent generators (13,14,23,24) have Hessian

\[
\begin{pmatrix}
-8&0&0&4\\0&-6&10&0\\0&10&-6&0\\4&0&0&-8
\end{pmatrix},
\]

with eigenvalues -16,-12,-4,4. Every coordinate direction is nonpositive, while a coupled direction is positive.

## Exact discrete/continuous averaging identity

Let E_ij denote averaging over the corresponding SU(2) fiber. The mean of n is zero, so (1) gives

\[
E_{ij}\det(A+B)=\det(A+B)-L_3.
\]

Swapping a_i and a_j corresponds to n=-e_3, hence

\[
\boxed{E_{ij}d(A,B)=\tfrac12\{d(A,B)+d(A^{(ij)},B)\}.}
\tag{5}
\]

This is an exact intertwining identity between continuous two-row averaging and a lazy discrete transposition of the diagonal spectrum. It does not make d a harmonic function with permutation boundary values. No local-to-global maximum principle is asserted.

## An actual fourth-order flat maximum

Take A=diag(1,1,-1,-1), B=diag(1,-1,1,-1), eta=-1. All permutation determinants are nonnegative, so the identity is a maximizing support vertex with support value zero.

Let K_12=K_13=1 with the skew counterparts and all other entries zero. Then K has real rank two. On the first three coordinates B=I-2e_2e_2^T, while A=I-2e_3e_3^T. The fourth sum entry remains -2. If v=exp(theta K)e_2, direct rank-one expansion gives

\[
\det(A+e^{\theta K}Be^{-\theta K})=16v_3^2
=4\{1-\cos(\sqrt2\theta)\}^2.
\]

The support function is therefore -4 theta^4+O(theta^6): its Hessian vanishes in this direction, but the function is not constant. This is a concrete reason the exact quadratic support-reduction argument for rank-one updates cannot simply be copied for a general rank-two rotation.

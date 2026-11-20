# The exact scalar obligation on a defect-one singular-value disk

## What is established

A defect-one contraction in dimension three has a one-complex-variable singular-value disk. Every scalar determinant support on that disk is a real quadratic in the disk coordinate. The entire disk inequality is equivalent to one two-by-two Hermitian positive semidefinite condition with one nonnegative scalar multiplier.

This reduction is exact. What remains open is whether actual normal spectral data always supply that positive matrix with the full and partial matching budget. No center-plus-boundary maximum principle is assumed.

## 1. The contraction and the comparison vertices

Let \(D\) be an \(m\times m\) contraction with

\[
\operatorname{rank}(I-D^*D)\le1.
\]

Singular-value decomposition places \(D\) on a disk

\[
D(z)=V\operatorname{diag}(I_{m-1},z)W^*
     =D_0+zxy^*,\qquad |z|\le1.
\tag{1}
\]

Here \(D_0\) is a corank-one partial isometry, \(D_0y=0\), \(D_0^*x=0\), and \(x,y\) are unit vectors. On \(|z|=1\), \(D(z)\) is unitary.

For diagonal normal data \(A=D_a\), \(B=D_b\), the scalar determinant is

\[
F(z)=\det(A+D(z)BD(z)^*).
\tag{2}
\]

The rank-one-deletion formulation uses the comparison points

\[
Z_\sigma=\prod_i(a_i+b_{\sigma(i)}),\qquad
Z_{\sigma,j}=a_j\prod_{i\ne j}(a_i+b_{\sigma(i)}).
\tag{3}
\]

The partial point retains \(a_j\), while the column \(\sigma(j)\) is consumed by the deleted site. It is not an arbitrary omission of both factors.

The categorical track proves that the universal defect-one inclusion in this enlarged hull is equivalent to MOC one dimension higher. The present note analyzes its exact radial proof obligation.

## 2. Four polynomial coefficients, without an invertibility assumption

Use the compatible bases in (1), and write

\[
V^*AV=\begin{pmatrix}A_{11}&A_{12}\\A_{21}&A_{22}\end{pmatrix},
\qquad
W^*BW=\begin{pmatrix}B_{11}&B_{12}\\B_{21}&B_{22}\end{pmatrix}.
\]

The final blocks \(A_{22},B_{22}\) are scalars. Put

\[
H_0=A_{11}+B_{11},\qquad J=\operatorname{adj}(H_0).
\]

The block determinant identity gives

\[
F(z)=C+Hz+H'\overline z+L|z|^2,
\tag{4}
\]

where

\[
\begin{aligned}
C&=A_{22}\det H_0-A_{21}JA_{12},\\
H&=-B_{21}JA_{12},\\
H'&=-A_{21}JB_{12},\\
L&=B_{22}\det H_0-B_{21}JB_{12}.
\end{aligned}
\tag{5}
\]

To check it, the lower-left block of the matrix in (2) is \(A_{21}+zB_{21}\), the upper-right block is \(A_{12}+\overline zB_{12}\), and the lower-right entry is \(A_{22}+|z|^2B_{22}\).
Expanding the scalar block determinant gives (5).
These are polynomial identities, so singular \(H_0\) causes no problem.

There is also an intrinsic interpretation:

\[
C=\det(A+D_0BD_0^*),\qquad
L=\det(B+D_0^*AD_0).
\tag{6}
\]

The coefficient of \(|z|^2\) is therefore a reciprocal center determinant, with the spectra exchanged and the partial isometry adjointed.

Alternatively, each compound minor of \(D_0+zxy^*\) is affine in \(z\). On the unitary circle, complementary minors have equal squared modulus and the full determinant has the form \(z\delta\), \(|\delta|=1\). Comparing the affine coefficients shows that squared slope minors are squared complementary center minors, which gives the second identity in (6).

The reciprocal partial vertices are \(Z_\sigma-Z_{\sigma,j}\). Ordinary full vertices \(Z_\sigma\) remain allowed. Rank deficiency alone does not justify dropping them from a scalar hull law.

## 3. Exact maximization and a two-by-two certificate

Fix a complex support direction \(\eta\), and put

\[
c=\operatorname{Re}(\eta C),\qquad
q=\operatorname{Re}(\eta L),\qquad
b=\frac{\eta H+\overline{\eta H'}}2.
\]

Then

\[
f(z)=\operatorname{Re}(\eta F(z))
=c+2\operatorname{Re}(bz)+q|z|^2.
\tag{7}
\]

Let \(h\) be any proposed upper bound. The following criterion is necessary and sufficient:

\[
\boxed{
f(z)\le h\ (|z|\le1)
\quad\Longleftrightarrow\quad
\exists\tau\ge0:
\begin{pmatrix}
h-c-\tau&-b\\
-\overline b&\tau-q
\end{pmatrix}\succeq0.
}
\tag{8}
\]

For sufficiency, write the right-hand matrix as \(Q\). Then

\[
h-f(z)=(1,z)^*Q(1,z)+\tau(1-|z|^2)\ge0.
\tag{9}
\]

For necessity, maximize the phase of \(z\) first. At radius \(r\),

\[
\max_{|z|=r}f(z)=c+2|b|r+qr^2.
\tag{10}
\]

There are two cases.

If \(q\ge0\), or if \(q<0\) and \(|b|\ge-q\), the maximum is

\[
c+q+2|b|.
\tag{11}
\]

Take \(\tau=q+|b|\ge0\).
The lower-right entry of \(Q\) is \(|b|\), and its upper-left entry is at least \(|b|\), so \(Q\succeq0\). The case \(b=0,q\ge0\) gives a diagonal matrix.

If \(q<0\) and \(|b|\le-q\), the maximum is attained at radius \(|b|/(-q)\), with value

\[
c+\frac{|b|^2}{-q}.
\tag{12}
\]

Taking \(\tau=0\), condition (8) is exactly

\[
\boxed{|b|^2\le(h-c)(-q).}
\tag{13}
\]

The zero case \(b=q=0\) is immediate. This proves every case of (8).

Thus the prospective induction does not require a vague interpolation principle. Its missing statement is a specific Schwarz-type budget (13) in the concave interior case, or the equivalent universal matrix condition (8).

## 4. Why the center is not an automatic smaller-dimensional case

For \(m=3\), the unitary circle in (1) is safely governed by MOC in dimension three. The center \(D_0\) is different.

Write \(D_0=XY^*\), with \(X,Y\) three-by-two isometries. When \(A\) is invertible,

\[
\det(A+D_0BD_0^*)
=\det A\,[1+\operatorname{tr}(ST)+\det S\det T],
\quad
S=X^*A^{-1}X,\quad T=Y^*BY.
\tag{14}
\]

It does prove that the center cannot be declared solved merely by citing separate selected-pair marginals from a compressed-matrix theorem.

Even a correct scalar center theorem, combined with a correct boundary theorem, would still leave the coherence coefficient \(b\) to control.

## 5. An actual three-dimensional disk with a positive certificate

Take

\[
A=\operatorname{diag}(1,-1,0),\qquad
B=\operatorname{diag}(2,-2,2),
\]

\[
D(z)=
\frac12\begin{pmatrix}1+z&1-z\\1-z&1+z\end{pmatrix}
\oplus(1).
\tag{15}
\]

The fixed Hadamard basis diagonalizes the first block into \(1,z\).
Hence the singular values of \(D(z)\) are exactly \(1,1,|z|\), and (15) is an actual defect-one disk.

Put \(z=x+iy\). In its first two coordinates,

\[
A_2+D_2(z)B_2D_2(z)^*
=
\begin{pmatrix}
1+2x&2iy\\
-2iy&-1-2x
\end{pmatrix}.
\]

Its determinant is \(-(1+2x)^2-4y^2\), and the third diagonal entry is 2. Therefore

\[
\boxed{F(z)=-2|1+2z|^2.}
\tag{16}
\]

For these spectra, the maximum of the six full matching products is \(-2\), while the maximum of the eighteen partial matching products is \(6\).
The partial height uses all eighteen partial matching products in dimension three.

The exact disk coefficients are

\[
c=-2,\qquad b=-4,\qquad q=-8.
\]

With the correct expanded height \(h=6\), \(\tau=0\) gives

\[
Q=\begin{pmatrix}8&4\\4&8\end{pmatrix}\succ0,\qquad \det Q=48.
\tag{17}
\]

## 6. Exact remaining bridge

For every actual \(A,B,V,W,\eta\), let

\[
h=\max_{\sigma,j}
\left\{
\operatorname{Re}(\eta Z_\sigma),
\operatorname{Re}(\eta Z_{\sigma,j})
\right\}.
\]

The universal induction obligation is precisely the existence of \(\tau\ge0\) in (8), with \(c,b,q\) defined by the actual block coefficients (5).
A constructive proof would have to couple the direct center, reciprocal center, and coherent cross terms within this expanded spectral budget.
Separate center bounds, a transfer-circle average, or singular-value endpoint interpolation do not by themselves provide that coupling.

The identities (4)–(8) hold in every dimension. The difficulty lies in the relation between their coefficients and the matching height, not in reducing the disk to a finite positive matrix.

## Reproducibility and coordination

code/theorems/finite_and_spin_geometry/dual_defect_one_disk_exact.py verify the actual example, its exact polynomial determinant, all 24 full and partial vertex values, and the positive matrix (17), using rational arithmetic.

The reciprocal-center identity and full induction/deletion framework are also proved in `categorical_defect_one_induction.md`.


# The algebraic input needed by the positivity proofs

This chapter separates two levels of algebraic information. The necessary
spectral equations used in the positive support theorems follow from the
explicit cubic and finite polynomial identities printed in this volume.
The stronger identification of the entire invariant variety, its singular
scheme, and its irreducible projected equation uses the precisely stated
invariant-theory theorem below. The positive support arguments do not
require the stronger identification when a necessary equation suffices.

## 1. Coordinates and the explicit cubic

For eight finite complex spectral parameters let

\[
z_\pi=\prod_{i=1}^{4}(a_i+b_{\pi(i)}).
\]

Use the following fourteen permutation products, in this order, as the
coordinate vector \(x=(x_0,\ldots,x_{13})\):

\[
1234,1243,1324,1342,1423,2134,2143,
2314,2341,2413,3124,3142,3412,4123.
\]

Here a string records the images of \(1,2,3,4\). The complete coefficient
table of the forty-nine-term cubic \(F(x)\), and the fourteen-to-105
matching-coordinate table, are printed in the exact invariant-coordinate
appendix. The underlying expansion uses seventy bracket monomials; this
is a different count from the 105 perfect matchings. Equivalently, with
\(\ell_M\) the printed linear coordinate of
each of the 105 increasingly oriented perfect matchings of eight labels,

\[
F(x)=\frac16\sum_M\epsilon(M)\ell_M(x)^3.
\tag{D1}
\]

The sign \(\epsilon(M)\) is the sign of the permutation obtained by
listing the oriented pairs successively. The explicit coordinate table
fixes the normalization, so no sign or scaling convention is implicit.

The exact polynomial identity needed below is

\[
\nabla F\bigl((z_\pi)_{\pi\text{ in the selected order}}\bigr)=0.
\tag{D2}
\]

This identity has a finite elementary verification: differentiate the
forty-nine-term table, substitute each of the fourteen four-factor
products, expand by the distributive law, collect monomials in the eight
spectral parameters, and cancel equal exponent vectors. The complete
integer polynomial procedure and its coefficient data are printed in the
algorithmic appendix. Every coefficient of each of the fourteen resulting
polynomials is zero. In particular, (D2) does not need a converse
description of the zero set of the gradient. Because \(F\) is homogeneous,
(D2) also holds after multiplying the product vector by any complex
support scalar \(\eta\).

## 2. Necessary equations for every actual real support cost

Set \(z=\eta(z_\pi)\), \(c=\Re z\), and \(d=\Im z\), so that
\(z=c+id\). For a real cubic the quadratic polarization identity is

\[
\nabla F(c+id)=\nabla F(c)-\nabla F(d)+iH_F(c)d.
\]

Applying (D2) and taking real and imaginary parts proves

\[
\boxed{H_F(c)d=0,\qquad \nabla F(d)=\nabla F(c).}
\tag{D3}
\]

Also \(F(c)=0\). One elementary way to see this is to put
\(u=z/2\), \(v=\overline z/2\). Both gradient vectors vanish. Cubic
polarization gives

\[
F(u+v)=F(u)+F(v)+\nabla F(u)\cdot v+\nabla F(v)\cdot u=0,
\]

where Euler's formula gives \(F(u)=F(v)=0\).

Finally,

\[
\boxed{\det H_F(c)=0.}
\tag{D4}
\]

If \(d\ne0\), (D3) supplies a nonzero Hessian-kernel vector. If
\(d=0\), then (D2) says \(\nabla F(c)=0\), and Euler's formula
\(H_F(c)c=2\nabla F(c)\) supplies a kernel vector unless \(c=0\).
At \(c=0\), the Hessian itself is zero. This proves (D4) in all cases.

Equations (D2)--(D4) are necessary spectral equations. Their derivation
does not assert that every real solution is an actual spectral cost.

## 3. Eliminate a constant cost without a geometric identification theorem

Let \(e=(1,\ldots,1)\). Define the four linear forms

\[
\begin{aligned}
B_{00}(x)&=x_0-x_1-x_5+x_6,\\
B_{01}(x)&=x_2-x_3-x_{10}+x_{11},\\
B_{10}(x)&=x_2-x_4-x_7+x_9,\\
B_{11}(x)&=-x_0+x_1+2x_2-x_3-x_4+x_5-x_7-x_{10}+x_{12},
\end{aligned}
\]

and put

\[
Q(x)=\det B(x)=B_{00}B_{11}-B_{01}B_{10}.
\]

Direct differentiation of the printed cubic gives

\[
D_eF=Q,\qquad B(e)=0,
\qquad F(x+te)=F(x)+tQ(x).
\tag{D5}
\]

Choose the printed invertible linear change of coordinates
\(x=T(t,a,b)\), with \(a\in\mathbb R^9\),
\(b=(b_{00},b_{01},b_{10},b_{11})\), such that changing \(t\)
adds \(te\), and \(b=B(x)\). Its determinant is \(-1\). Then

\[
F(T(t,a,b))=tQ(b)+C(a,b),\qquad
Q=b_{00}b_{11}-b_{01}b_{10}.
\tag{D6}
\]

The polynomial \(C\) and the full coordinate matrix \(T\) are given in
the same invariant-coordinate appendix. For precise identification of
the printed records: the cubic and matching table are the fields
`skew_cubic` and `all_matching_coordinates` of
`categorical_m8_coordinates.json`; the coordinate transformation and
split cubic are the fields `x_equals_T_y` and
`cubic_in_split_coordinates` of `categorical_m8_projection.json`.
Define

\[
J=H_Q,\quad \ell=Jb,\quad K=C_{aa},\quad
L=C_{ab},\quad M=C_{bb}.
\]

The transformed Hessian has the block form

\[
\mathcal H(t)=
\begin{pmatrix}
0&0&\ell^T\\
0&K&L\\
\ell&L^T&tJ+M
\end{pmatrix}.
\tag{D7}
\]

Since \(\det T=-1\), the determinant of this Hessian equals the
determinant in the original coordinates. On the open set \(\det K\ne0\),
the ordinary Schur-complement identity gives

\[
\det\mathcal H(t)
=-\det K\;\ell^T
\operatorname{adj}\bigl(tJ+M-L^TK^{-1}L\bigr)\ell.
\]

It has degree at most three in \(t\). Writing it as
\(h_0+h_1t+h_2t^2+h_3t^3\), the leading coefficient is

\[
h_3=-\det K\det J\;\ell^TJ^{-1}\ell=-2Q\det K,
\tag{D8}
\]

because \(\det J=1\) and \(b^TJb=2Q\). Both assertions extend
polynomially across \(\det K=0\).

Define the following explicit degree-eighteen polynomial in the thirteen
quotient coordinates:

\[
\boxed{N=Q^2h_0-CQh_1+C^2h_2+2C^3\det K.}
\tag{D9}
\]

For an actual real support cost, (D6) and \(F(c)=0\) imply
\(t=-C/Q\) whenever \(Q\ne0\). Equations (D4) and (D8) therefore give

\[
N=Q^2\det\mathcal H(-C/Q)=0.
\]

The same conclusion holds when \(Q=0\). To justify the limiting step
without discarding an entire parameter component, note that the real and
imaginary parts of the spectra and of \(\eta\) range over a real affine
space, and that the composed polynomial \(Q(c)\) is not identically
zero. For example, \(a=b=(0,1,i,2)\), \(\eta=1\), give

\[
c=(0,0,0,0,0,0,3,-4,2,-3,-4,-3,-9,2),
\qquad B(c)=\begin{pmatrix}3&1\\1&-1\end{pmatrix},
\qquad Q(c)=-4.
\]

The complement of the zero set of a nonzero real polynomial is dense.
The polynomial composition of \(N\) with the actual spectral parameters
vanishes there and hence vanishes identically. Adding an arbitrary real
constant to the support cost changes only \(t\), which has already been
eliminated. We have proved, for all finite spectra and all their
degenerations,

\[
\boxed{N(\text{actual support cost modulo constants})=0.}
\tag{D10}
\]

## 4. How the tetrahedral positivity proof uses only this necessary equation

In the tetrahedral fixed subspace, use centered class coordinates
\((x,y,k)\) with class values

\[
0,\quad x,\quad y,\quad x+y/2,\quad 3x/2+k,\quad 3x/2-k.
\]

Direct substitution in the determinant expression (D9), using the
printed coordinate transformation, gives

\[
\boxed{
N\big|_{A_4}
=-\frac1{256}
x^2(3y-4x)^4(4k^2+xy-x^2)^6.
}
\tag{D11}
\]

Thus an actual cost in this fixed subspace belongs to at least one of
the three sets

\[
x=0,\qquad 3y=4x,\qquad 4k^2=x(x-y).
\]

The two simplex theorems and the elementary minor certificates printed
in the tetrahedral chapter prove the support inequality on all three
sets. This application requires (D10)--(D11), not a theorem identifying
the full spectral variety. It also does not average an arbitrary
spectral cost onto the fixed subspace: the separately printed exact
averaging example shows why that would change the admissible set.

## 5. The stronger structural theorem and its precise role

The following is an established invariant-theory input, attributed to
Howard, Millson, Snowden, and Vakil, *The geometry of eight points in
projective space: Representation theory, Lie theory, dualities*,
Proceedings of the London Mathematical Society, DOI
10.1112/plms/pds016:

> For the degree-one invariant embedding of the quotient of eight
> ordered points of the projective line into projective thirteen-space,
> the invariant variety is the scheme-theoretic singular locus of the
> distinguished skew cubic. Its ideal is generated by the fourteen
> quadratic first derivatives. On the cubic, the Hessian divisor is
> twice the irreducible secant variety, which has projective dimension
> eleven.

This book reproduces the explicit coordinate identification, finite-chart
construction, elimination, and real-polarization arguments used in the
research. It attributes the stated structural invariant-theory theorem
to its source; an identity check on the parametrization by itself is
not offered as a proof of that theorem.

Together with the finite-chart lemma, the singular-locus assertion gives
the converse direction in the exact real membership test:

\[
\exists d:\ H_F(c)d=0,\quad \nabla F(d)=\nabla F(c)
\quad\Longrightarrow\quad
c=\Re z\text{ for a finite spectral product vector }z.
\]

Together with the Hessian-divisor assertion, the elimination above
shows that \(N=-4P_9^2\), where \(P_9\) is the irreducible projected
secant equation of degree nine in the chosen normalization. The density
argument in the spectral-geometry chapter then identifies the entire
polynomial ideal of actual centered costs with \(\langle P_9\rangle\).
Those are the precise places where the structural source theorem enters.
The elementary necessary implication (D10) and the fixed-subspace
positivity argument (D11) remain independently available.

## 6. Other standard inputs in the proof record

The elementary convex and linear-algebraic inputs are finite-dimensional
separation, compactness, the spectral theorem, Cauchy--Binet,
complementary minors, the determinant lemma, Schur complements, and the
positive-semidefinite criterion furnished by an exact positive
\(LDL^T\) factorization. Their instances are written out where used.
The profile-purification proof supplies its own extremal-effect argument;
the three-color proof supplies its own allocation dual and cut argument;
the quaternion certificates print their polynomials and rational Gram
data; and the finite-polytope proofs print their completeness procedures.
Consequently none of these campaign-specific steps is delegated to an
unavailable computational file.

The Jordan-algebra chapter explicitly takes the standard spectral and
Peirce-decomposition laws of a Euclidean Jordan algebra as its algebraic
setting. Within that setting its rank-three determinant comparison is
proved in full. The real-Gram support theorem uses the classical
Hermitian determinant comparison, whose complete elementary proof follows.
Other literature statements about previously solved MOC classes are
bibliographic background, while the support theorems proved by the
present record have their actual derivations and exact data inside this
volume.

## 7. A complete elementary proof of the classical Hermitian determinant comparison

### Theorem

Let \(A\) and \(B\) be Hermitian matrices of order \(n\), with real
eigenvalues \(a_1,\ldots,a_n\) and \(b_1,\ldots,b_n\). Then for every
unitary matrix \(U\),

\[
\boxed{
\min_{\pi\in S_n}\prod_i(a_i+b_{\pi(i)})
\ \le\ \det(A+UBU^*)\ \le\
\max_{\pi\in S_n}\prod_i(a_i+b_{\pi(i)}).
}
\tag{D12}
\]

This is the classical Hermitian case customarily associated with
Fiedler's determinant theorem. The argument here is included to make the
real-Gram application internally complete; no novelty claim is attached
to the theorem.

### Proof at a nonzero extremum

By unitary changes of basis, take \(A=\operatorname{diag}(a)\) and
\(B=\operatorname{diag}(b)\). The real continuous function

\[
f(U)=\det(A+UBU^*)
\]

attains its maximum and minimum on the compact unitary group. Let
\(U_0\) be either extremizer, write \(B_0=U_0BU_0^*\) and
\(M=A+B_0\), and first suppose \(\det M\ne0\).

For any skew-Hermitian \(K\), varying \(B_0\) as
\(e^{tK}B_0e^{-tK}\) gives

\[
0=\left.\frac{d}{dt}\det(A+e^{tK}B_0e^{-tK})\right|_{t=0}
=\det M\;\operatorname{tr}\bigl([B_0,M^{-1}]K\bigr).
\]

The commutator \(C=[B_0,M^{-1}]\) is skew-Hermitian because both of
its factors are Hermitian. We may choose \(K=-C\). Since

\[
-\operatorname{tr}(C^2)=\operatorname{tr}(C^*C)\ge0,
\]

the stationarity identity and \(\det M\ne0\) imply \(C=0\).
Therefore \(B_0\) commutes with \(M\), and hence with \(A\).
Commuting Hermitian matrices have a simultaneous orthonormal eigenbasis.
Their paired eigenvalues give

\[
\det(A+B_0)=\prod_i(a_i+b_{\pi(i)})
\]

for some permutation \(\pi\). This statement includes repeated
eigenvalues: diagonalize \(B_0\) inside each eigenspace of \(A\).
Thus every nonzero global maximum or minimum is a permutation product.

### A singular extremum cannot violate the comparison

It remains to consider a hypothetical violating extremum equal to zero.
For an upper-bound violation, every permutation product would be
strictly negative. For a lower-bound violation, every permutation product
would be strictly positive. In either situation, their common strict sign
persists under sufficiently small real diagonal perturbations of \(A\),
because there are only finitely many permutations.

At a singular extremizer let \(W=\ker M\), \(k=\dim W\ge1\).
For a Hermitian perturbation \(E\), its compression
\(E_W=P_WE|_W\) controls the leading determinant term:

\[
\det(M+\varepsilon E)
=\varepsilon^k\det(M|_{W^\perp})\det(E_W)
+O(\varepsilon^{k+1}).
\tag{D13}
\]

If \(W=\mathbb C^n\), the determinant on the zero-dimensional
complement is interpreted as one, and the formula is immediate. Otherwise,
in the orthogonal decomposition \(W\oplus W^\perp\), write

\[
M+\varepsilon E=
\begin{pmatrix}
\varepsilon E_{11}&\varepsilon E_{12}\\
\varepsilon E_{21}&M_{22}+\varepsilon E_{22}
\end{pmatrix},
\]

where \(M_{22}\) is invertible. The determinant Schur complement equals

\[
\det(M_{22}+\varepsilon E_{22})\,
\det\!\left(\varepsilon E_{11}
-\varepsilon^2E_{12}(M_{22}+\varepsilon E_{22})^{-1}E_{21}\right),
\]

which proves (D13).

There are real diagonal choices of \(E\) for which \(\det E_W\)
has either sign. For the positive sign use \(E=I\). For the negative
sign choose a coordinate vector \(e_i\) with \(w=P_We_i\ne0\), and
choose \(\lambda>\|w\|^{-2}\). Then

\[
E=I-\lambda e_ie_i^*
\quad\Longrightarrow\quad
E_W=I_W-\lambda ww^*.
\]

This compression has one negative eigenvalue
\(1-\lambda\|w\|^2\) and \(k-1\) eigenvalues equal to one.
Thus its determinant is negative. Such an index \(i\) exists because
the coordinate vectors span the space and \(W\ne\{0\}\).

The nonzero number \(\det(M|_{W^\perp})\) has a fixed sign. Choose
one of these two diagonal perturbations so that the leading coefficient
in (D13) has the outward sign: positive for the proposed upper-bound
violation, negative for the proposed lower-bound violation. For all
sufficiently small positive \(\varepsilon\), the determinant at the
same \(U_0\) is then nonzero with that sign, whereas every permutation
product for \(A+\varepsilon E\) retains the opposite strict sign.

The perturbed orbit consequently has a nonzero global maximum or minimum
violating its permutation comparison. The preceding nonzero-extremum
argument says that this extremum itself is one of its permutation
products, a contradiction. Singular extrema therefore cannot violate
(D12), and the theorem is proved. \(\square\)

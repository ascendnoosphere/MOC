# Exterior Agler kernels and reciprocal defect-one disks

This note supplies two exact all-dimensional structures for the defect-one
induction problem. It does not establish the missing scalar disk budget.
The distinction between positivity before and after spectral evaluation is
explicit throughout.

## 1. A constant projection is the exact Agler kernel in every exterior sector

Let \(D_0:y^\perp\to x^\perp\) be unitary between two codimension-one
subspaces, with \(D_0y=0\), \(D_0^*x=0\), and \(\|x\|=\|y\|=1\). Set

\[
D(z)=D_0+zxy^*,\qquad |z|\le1.
\]

For every \(0\le k\le m\), there are operators \(C_k,E_k\) such that

\[
\bigwedge^kD(z)=C_k+zE_k.
\tag{1}
\]

The source exterior space splits orthogonally as

\[
\bigwedge^k\mathbb C^m
=\bigwedge^k y^\perp
 \oplus\bigl(y\wedge\bigwedge^{k-1}y^\perp\bigr).
\]

On the first summand, (1) is the exterior power of \(D_0\), independently
of \(z\); on the second it is \(z\) times the corresponding isometry
with the factor \(y\) replaced by \(x\). Their ranges are the analogous
orthogonal summands for \(x\). Thus \(C_k,E_k\) are partial isometries and

\[
C_k^*E_k=0,quad C_kE_k^*=0,
\quad C_k^*C_k+E_k^*E_k=I,
\quad C_kC_k^*+E_kE_k^*=I.
\tag{2}
\]

In particular, the two-variable defect identity is exact:

\[
\boxed{I-(\bigwedge^kD(w))^*\bigwedge^kD(z)
       =(1-\bar wz)E_k^*E_k.}
\tag{3}
\]

The quotient by \(1-\bar wz\) is a constant positive projection, of rank
\(\binom{m-1}{k-1}\). The corresponding range-side identity has projection
\(E_kE_k^*\). This is a fully positive operator-valued Schur/Agler
construction; no scalar support inequality has been assumed.

## 2. A completely positive kernel retaining each minor's coherence

In the subset bases, write

\[
c_{IJ}=(C_k)_{IJ},\qquad e_{IJ}=(E_k)_{IJ},
\qquad\det D(z)[I,J]=c_{IJ}+ze_{IJ}.
\]

Each pair of subsets has a positive two-by-two coefficient matrix

\[
G_{IJ}=\begin{pmatrix}
|c_{IJ}|^2&\bar c_{IJ}e_{IJ}\\
c_{IJ}\bar e_{IJ}&|e_{IJ}|^2
\end{pmatrix}\succeq0,
\qquad \det G_{IJ}=0.
\tag{4}
\]

Equivalently, the maps

\[
\Phi_{z,w}(X)
 =\sum_{I,J}(c_{IJ}+ze_{IJ})
       \overline{(c_{IJ}+we_{IJ})}\,
       |I\rangle\langle J|X|J\rangle\langle I|
\tag{5}
\]

form a completely positive kernel in \(z,w\): for every finite collection
of parameters, their block Choi matrix is a direct sum of Gram matrices
of the scalar features \(c_{IJ}+ze_{IJ}\). At \(z=w\), this is the
entanglement-breaking map associated with the compound-minor probability
matrix. In particular it retains the phase-linear cross terms before any
spectral pairing.

Equations (2) also show, for every subset row and column,

\[
\sum_J\bar c_{IJ}e_{IJ}=0,\qquad
\sum_I\bar c_{IJ}e_{IJ}=0,
\]

\[
1-\sum_J|c_{IJ}+ze_{IJ}|^2
 =(1-|z|^2)(E_kE_k^*)_{II},
\]

\[
1-\sum_I|c_{IJ}+ze_{IJ}|^2
 =(1-|z|^2)(E_k^*E_k)_{JJ}.
\tag{6}
\]

Thus the loss of bistochasticity is exactly a positive projection marginal,
while each cross term has zero unweighted row and column sum. These are
additional identities beyond entrywise nonnegativity.

## 3. Why the positive operator kernel has not supplied the scalar bound

The determinant test uses the complex coefficients

\[
t_{IJ}=a_{I^c}b_J,
\qquad
Q(z)=\sum_{I,J}t_{IJ}|c_{IJ}+ze_{IJ}|^2.
\]

For a real support direction \(\eta\), its coefficient matrix is the
signed combination

\[
\sum_{I,J}\Re(\eta t_{IJ})G_{IJ}.
\tag{7}
\]

The individual matrices (4) are positive, but the weights in (7) have no
fixed sign for unrestricted complex spectra. Consequently (7) need not
be positive. Complete positivity of (5), strict contraction in (3), and
boundary bistochasticity do not by themselves make the evaluated support
function subharmonic.

For the scalar disk function
\(f(z)=c+2\Re(bz)+q|z|^2\), the prescribed-height condition is the existence of \(\lambda\ge0\) with

\[
\begin{pmatrix}
h-c-\lambda&-b\\-\bar b&\lambda-q
\end{pmatrix}\succeq0,
\]

where \(h\) is the maximum of all ordinary and one-edge-deleted permutation
products in the chosen support direction. The operator positivity above
is proved; a universal conversion into this spectral budget remains open.

## 4. Exact reciprocal inversion of the determinant disk

Set

\[
\widetilde D(w)=D_0^*+wyx^*,\qquad
\widetilde Q(w)=\det(B+\widetilde D(w)A\widetilde D(w)^*).
\]

For \(z\ne0\), the orthogonal decompositions give

\[
D(z)^{-1}=D_0^*+z^{-1}yx^*=\widetilde D(1/z),
\qquad |\det D(z)|^2=|z|^2.
\]

Factoring \(D(z)\) and \(D(z)^*\) from the determinant therefore proves

\[
\boxed{Q(z)=|z|^2\widetilde Q(1/z).}
\tag{8}
\]

If

\[
Q(z)=C+Hz+H'\bar z+L|z|^2,
\]

comparison in (8) gives

\[
\widetilde Q(w)=L+H'w+H\bar w+C|w|^2.
\tag{9}
\]

In particular the center and radial coefficient are exchanged:

\[
C=\det(A+D_0BD_0^*),\qquad
L=\det(B+D_0^*AD_0).
\]

The complex coefficients \(H,H'\) are exchanged, not individually
conjugated. After applying \(\Re\eta\), the real support polynomials obey

\[
f(z)=c+2\Re(bz)+q|z|^2,
\qquad
\widetilde f(w)=q+2\Re(\bar b w)+c|w|^2,
\qquad f(z)=|z|^2\widetilde f(1/z).
\tag{10}
\]

This is an exact involution and explains the reciprocal-center formula.
It also identifies a limitation: an interior disk point maps outside the
reciprocal unit disk. Thus (8) does not replace the unresolved interior
bound by a previously proved contraction bound. Any use of reciprocal
centers must transport the domain and the partial-matching comparison
height together.

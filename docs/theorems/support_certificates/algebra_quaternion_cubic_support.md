# A direct full-unitary support theorem beyond the quadratic certificate cones

## The proved result

A positive norm multiplier gives a quaternion sum-of-squares certificate for the actual complex spectral direction below. The resulting
certificate proves its scalar support inequality for **every matrix in
`U(4)`**. Strictly positive rational Gram matrices also prove a full open
neighborhood of real common-minor support costs around this example.

This is a theorem about one specified supporting phase and a neighborhood
of supporting directions. It is not a proof of unrestricted complex MOC,
and it does not establish every supporting phase for the displayed pair.
Its significance is that this actual direction was already separated
exactly from the finite `C130+Q54` certificate cone, from the complete
quadratic quaternion SOS cone, and from that quaternion cone supplemented
by all the previously proved hard and border rays. The present certificate
proves the underlying support inequality despite those exact failures.

## 1. Actual spectra and supporting direction

Use the following spectra, with the last two entries of the previously
recorded column spectrum already interchanged:

\[
a=\left(0,\frac12,1,
 \frac{27223}{109707}+i\frac{24421}{36569}\right),
\tag{1}
\]

\[
b=\left(\frac{352}{3},
 \frac{-19103+16810i}{51493},
 \frac{-836163-439684i}{1331525},
 \frac{-501033-262235i}{1603673}\right),
\tag{2}
\]

\[
\eta=\frac{500249382399}{125000000000000}
       -i\frac{997971562341}{62500000000000},
\qquad
h=\frac{111645445527}{976562500000}.
\tag{3}
\]

Let `D_a,D_b` be the corresponding diagonal matrices. Direct rational
complex multiplication of all 24 products gives

\[
h=\max_{\pi\in S_4}
  \Re\left\{\eta\prod_{i=1}^4(a_i+b_{\pi(i)})\right\}.
\tag{4}
\]

For the ordering (2), the identity is the unique maximizing permutation.
Its gap to the closest other permutation is exactly
`34690763097/250000000000000`. Reordering the column spectrum is harmless
to a theorem quantified over every unitary matrix.

### Theorem 1

For (1)--(3),

\[
\boxed{\quad
\Re\{\eta\det(D_a+U D_bU^*)\}\le h
\quad\text{for every }U\in U(4).
\quad}
\tag{5}
\]

Equality holds exactly when `U` is diagonal, with arbitrary unit-modulus
diagonal entries. In the original column ordering, these are the
corresponding maximizing monomial matrices.

## 2. Quaternion expression for the actual support deficit

Write the real quaternion coordinates as
`q=(q_0,q_1,q_2,q_3)` and `r=(r_0,r_1,r_2,r_3)`. Set

\[
Q=\sum_iq_i^2,\qquad R=\sum_ir_i^2,
\qquad D=Q-R,\qquad N=(Q+R)/2.
\tag{6}
\]

The left and right multiplication matrices used throughout the exact
certificate are

\[
L(q)=\begin{pmatrix}
q_0&-q_1&-q_2&-q_3\\
q_1&q_0&-q_3&q_2\\
q_2&q_3&q_0&-q_1\\
q_3&-q_2&q_1&q_0
\end{pmatrix},\qquad
R(r)=\begin{pmatrix}
r_0&-r_1&-r_2&-r_3\\
r_1&r_0&r_3&-r_2\\
r_2&-r_3&r_0&r_1\\
r_3&r_2&-r_1&r_0
\end{pmatrix}.
\tag{7}
\]

Put `O=L(q)R(r)`. Then `OO^T=QR I` identically. On `Q=R=1`, these
matrices cover `SO(4)`. The Hodge decomposition of the second compound
provides homogeneous quadratic polynomials `M_{I,J}(q,r)` such that

\[
\det O_{I,J}\equiv Q M_{I,J}\pmod D
\tag{8}
\]

for all 36 pairs of two-element row and column sets. Thus, on the two
unit spheres, the following twenty profile coordinates are homogeneous
quartics:

\[
\phi(O)=\bigl(
 O_{0j}^{\,2},\ M_{\{0,1\},J}^{\,2},\
 O_{2j}^{\,2},\ M_{\{1,2\},J}^{\,2}
\bigr).
\tag{9}
\]

Here `j=0,1,2,3`, and the two-element column sets are ordered
`01,02,03,12,13,23`. Write `Phi(q,r)` for the homogeneous quartic
representative in (9). The exact actual cost coefficients are

\[
w_0=\frac{1}{250000000000000}\begin{pmatrix}
141584483680242\\84184743403762\\-28865636276708\\28513079465452\\
-113003249625330\\-113055097018290\\-113067642322930\\1049600052565\\-56304445892920\\0\\
-56699119763067\\-5828016832\\0\\-56687800164512\\
112992212718890\\0\\220433142005\\0\\0\\0
\end{pmatrix}.
\tag{10}
\]

The support deficit quartic is

\[
f(q,r)=hQR-w_0\cdot\Phi(q,r).
\tag{11}
\]

The exact verifier does more than match costs at permutation matrices.
It reconstructs all actual products from (1)--(3), proves (8), and
expands the actual determinant by its 24 Leibniz terms. With
`C_{ij}=a_i+b_j`, it verifies the degree-eight identity

\[
h\det O-\Re\{\eta\det(C\circ O)\}
\equiv Q^2 f(q,r)\pmod D.
\tag{12}
\]

On the two unit spheres, `det O=1` and
`C\circ O=D_aO+OD_b`. Consequently (12) says exactly that

\[
f(q,r)=h-\Re\{\eta\det(D_a+OD_bO^T)\}.
\tag{13}
\]

There is no numerical scaling or rescaling of `eta` in (10)--(13).

## 3. The degree-six certificate

### Lemma 2: exact polynomial identity

There are eight explicitly recorded vectors `v_b(q,r)` of thirteen
homogeneous cubics and eight rational symmetric positive definite
`13 x 13` matrices `G_b` such that

\[
\boxed{\qquad
Nf=\sum_{b=0}^7 v_b^T G_bv_b\pmod D.
\qquad}
\tag{14}
\]

All cubic coefficients and all 1,352 Gram entries are supplied in
`algebra_quaternion_cubic_exact.json`. Its `exact_ldlt` field supplies a
rational factorization of every matrix, with all 104 diagonal pivots
strictly positive. These data are part of the finite certificate.

The common denominator of all Gram entries is exactly
`500000000000000`. Equivalently, writing `G_b=M_b/500000000000000`
gives integer matrices and the exact identity

\[
500000000000000\,Nf
\equiv\sum_b v_b^TM_bv_b\pmod D.
\tag{15}
\]

The free Gram parameters used for rational extraction were rounded to
denominator `100000000`; the affine coefficient equations were then
solved in rational arithmetic. The final denominator in (15) also
incorporates the original rational spectral coefficients. Positivity is
established by the saved exact LDL factorizations, rather than by the
floating-point search that discovered the matrices.

For clarity, the first cubic block in the certificate is

\[
\begin{split}
v_0=(&q_0q_1r_1,q_0q_2r_2,q_0q_3r_3,
q_1^2r_0,q_1q_2r_3,q_1q_3r_2,\\
&q_2^2r_0,q_2q_3r_1,q_3^2r_0,
r_0^3-q_0^2r_0,r_0r_1^2,r_0r_2^2,r_1r_2r_3)^T.
\end{split}
\tag{16}
\]

The complete basis construction is also exact and finite. Reduce all
homogeneous cubic monomials by

\[
r_3^2=q_0^2+q_1^2+q_2^2+q_3^2-r_0^2-r_1^2-r_2^2.
\tag{17}
\]

There are 112 normal monomials. Split them by whole-quaternion parity
`q -> -q` and simultaneous even coordinate sign changes on `q,r`.
The eight character blocks each contain fourteen monomials. In each
block, impose vanishing at `q=r=e_i`, `i=0,1,2,3`. The resulting
thirteen-dimensional space supplies its saved basis. These points are
signed diagonal orthogonal maximizers, so forcing these zeros is natural.
The affine Gram coefficient map has rank 178 and 550 free parameters.

**Verification of the lemma.** Multiply each pair of saved cubics,
weight by the corresponding rational Gram entry, sum, and use the
substitution (17). The result is exactly the normal form of `Nf`; there
is no residual coefficient. This establishes (14), since division by
the monic polynomial associated with (17) computes reduction modulo the
principal ideal generated by `D`. The exact LDL factorizations establish
`G_b>0`. The verification-only program reconstructs the source spectra,
quaternion geometry, degree-eight determinant identity, and all terms of
(14) without running an optimizer or using a floating-point tolerance.

On `Q=R=1`, the multiplier `N` is exactly one. Equation (14) therefore
proves `f>=0` there. More generally it proves `f>=0` on every nonzero
equal-norm quaternion pair, because `N>0` on that cone. The origin is
handled by homogeneity. This proves (5) on `SO(4)`. Row signs preserve
the full squared-minor profile and the diagonal spectral determinant,
so the support inequality holds on all of `O(4)`.

## 4. Why the real proof covers every complex unitary matrix

The following dimension-four purification supplies the passage to
`U(4)`; no averaging of actual spectral costs is used.

Make row 1 of a given unitary matrix real by column phases, calling it
`v`. Its other three rows, written `r_alpha=x_alpha+i y_alpha`, define
real symmetric matrices on the three-dimensional space `v^perp`:

\[
E_\alpha=x_\alpha x_\alpha^T+y_\alpha y_\alpha^T.
\tag{18}
\]

They are positive semidefinite, each has trace one, and their sum is the
identity. Every singleton and wedge coordinate anchored at `v` is
linear in the corresponding effect. In particular,

\[
|r_{\alpha j}|^2=(E_\alpha)_{jj},
\]

\[
|v_i r_{\alpha j}-v_jr_{\alpha i}|^2
=v_i^2(E_\alpha)_{jj}+v_j^2(E_\alpha)_{ii}
 -2v_iv_j(E_\alpha)_{ij}.
\tag{19}
\]

Every trace-one positive triple summing to the identity in real dimension
three is a convex combination of ordered rank-one orthogonal frames.
To prove this, consider an extreme triple. If every rank is at least two,
the supported symmetric perturbation spaces have total dimension at
least nine. Requiring zero individual traces and zero sum imposes at
most eight independent linear conditions. A nonzero supported
perturbation then preserves all constraints and positivity for a small
interval in both signs, contradicting extremality.

Hence an extreme triple has a rank-one effect `ww^T`. Its other effects
vanish on `w` and sum to the identity on a two-dimensional complement.
They commute, so simultaneous diagonalization expresses them as a
convex combination of the two ordered rank-one orthogonal frames of
that complement. Extremality forces a frame. Compactness now gives the
claimed convex decomposition of every triple.

The frames, with the same anchor `v`, are rows of real orthogonal
matrices. Equation (19) shows that their averaged twenty profiles equal
the original complex profile. Thus

\[
\phi(U)\in\operatorname{conv}\{\phi(O):O\in O(4)\}.
\tag{20}
\]

These twenty coordinates determine every squared minor coordinate
linearly. For completeness, complementary minors give the complementary
row pairs and all three-by-three minors. Wedge marginals recover the
anchor row singleton coordinates; column sums recover the remaining
row. The only missing row pair is `02` and its complement `13`.
Its six coordinates are determined by their four singleton marginals
and the three complementary-pair sums supplied by compound column sums.
This linear system has rank six: a homogeneous solution satisfies
`d_01=-d_23`, `d_02=-d_13`, `d_03=-d_12`, and its four vertex sums
then force all six entries to vanish.

The determinant expansion

\[
\det(D_a+UD_bU^*)=
\sum_{|I|=|J|}
 \left(\prod_{i\notin I}a_i\right)
 \left(\prod_{j\in J}b_j\right)|\det U_{I,J}|^2
\tag{21}
\]

is therefore affine in the twenty profiles. The constant is itself a
singleton row sum, so it may be represented linearly. Identity (13) on
all real orthogonal profiles and (20) show that its real supporting
functional equals `w_0 dot phi(U)` on every complex unitary profile.
Averaging the real support inequality proves Theorem 1 on `U(4)`.

This purification is special to dimension four. It does not establish
the analogous assertion in arbitrary dimension.

## 5. An exact open neighborhood, with a quantified radius

Strictly positive Gram blocks give an immediate but nontrivial
robustness result. It requires checking that perturbations of the
actual target remain in the same Gram image; positivity alone would
not establish that condition.

For every profile coordinate `j=1,...,20`, put

\[
t_j=N\bigl(\phi_j(I)QR-\Phi_j(q,r)\bigr)\pmod D.
\tag{22}
\]

The exact simultaneous linear solve in
`algebra_quaternion_cubic_neighborhood_exact.py` constructs rational
symmetric matrices `H_{jb}` with

\[
t_j=\sum_b v_b^TH_{jb}v_b\pmod D
\quad\text{for every }j.
\tag{23}
\]

All twenty identities are checked coefficient by coefficient. Their
span has dimension thirteen. The sparse upper-triangular entries of
every signed correction matrix are saved in
`algebra_quaternion_cubic_neighborhood_exact.json`.

### Theorem 3: open support region

For any real twenty-vector `w` satisfying

\[
\max_j|w_j-(w_0)_j|\le\frac1{100000000000},
\tag{24}
\]

one has

\[
\boxed{\qquad
w\cdot\phi(U)\le w\cdot\phi(I)
\quad\text{for every }U\in U(4).
\qquad}
\tag{25}
\]

The height in this statement moves with `w`: it is the identity value,
not the fixed rational number (3). The identity is consequently a
maximizing permutation throughout this neighborhood. The neighborhood
contains a relatively open region of actual complex spectral support
directions, and continuity of the spectral coefficients gives an open
set of source parameters around (1)--(3).

**Proof.** Set

\[
G_b(w)=G_b+\sum_j(w_j-(w_0)_j)H_{jb}.
\tag{26}
\]

Equations (14) and (23) give the required perturbed sextic identity.
Let

\[
T_b=\operatorname{tr}(G_b^{-1}),\qquad
B_b=\sum_j\sum_{k,l}|(H_{jb})_{kl}|.
\tag{27}
\]

All `T_b` are positive rationals, computed exactly from the rational
LDL factors. The eight exact `B_b` values are

\[
(756,392,188,104,0,0,0,0).
\tag{28}
\]

The saved rational calculation proves

\[
2\cdot10^{-11}T_bB_b\le1
\quad\text{for every }b.
\tag{29}
\]

Indeed, the smallest conservative bound `1/(2 T_b B_b)` over nonzero
`B_b` is approximately `1.2568666857717292e-11`, with its complete
rational value saved. Using
`lambda_min(G_b)>=1/trace(G_b^{-1})` and the entrywise bound on the
operator norm of (26), (24) and (29) imply

\[
G_b(w)\succeq\tfrac12G_b\succ0.
\tag{30}
\]

Thus the perturbed support deficit has the same positive norm-multiplied
SOS certificate. The argument of Sections 3--4 proves (25).

For the spectral corollary, the minor expansion (21) and the fixed
linear profile relations give coefficients continuous in the actual
spectra and the supporting phase. A fixed element of the profile
coefficient kernel can align the coefficient choice with (10) at the
center. Hence sufficiently small actual source perturbations satisfy
(24). The radius in (24) is a radius in the displayed coefficient
coordinates; it is not asserted to be a radius in raw spectral entries.

### Equality and strictness

Since every `G_b(w)` is positive definite, equality at a real orthogonal
matrix forces all saved cubics to vanish. Equation (23) then forces all
twenty deficits `t_j` to vanish, so its profile equals `phi(I)`. The
singleton coordinates of rows 0 and 2 and the minor `01,01` then force
that matrix to be signed diagonal.

For a complex equality case, (20) represents its profile by real
orthogonal profiles. Every term in that mixture must also be an equality
case, because each support deficit is nonnegative. Its profile is
therefore `phi(I)`, which forces the complex matrix to be diagonal with
unit-modulus diagonal entries. This proves the equality assertion of
Theorem 1 and the same assertion throughout the neighborhood (24).

## 6. Exact records and independent audit

The reproducible finite proof consists of:

* `algebra_quaternion_cubic_exact.json`: actual source, all 24 costs,
  twenty coefficients, 104 cubics, eight rational Gram matrices, and
  all 104 strictly positive LDL pivots.
* `algebra_quaternion_cubic_exact.py --verify-only`: exact reconstruction
  of (1)--(15), including the actual determinant identity.
* `algebra_quaternion_cubic_neighborhood_exact.py/.json`: exact linear
  corrections, all twenty identities (23), and the rational radius
  proof (27)--(30), with no optimization.

An independent reviewer rebuilt the quaternion arithmetic, actual
complex products, all 36 Hodge identities, degree-eight determinant
support identity, and eight cubic Gram forms without importing this
certificate builder. The independent audit accepted all 104 positive
LDL pivots and the exact polynomial equality. Its files are
`review_campaign3_fifth_exact.py/.json`.

The same reviewer subsequently expanded all twenty neighborhood
correction identities independently, recomputed inverse traces by
direct rational inversion, checked ranks thirteen and 178, and accepted
the radius `10^-11` and the equality classification. This is audit 035
in `review_campaign3_fifth_proofs.md`.


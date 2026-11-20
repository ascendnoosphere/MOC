## 1. Allocation signs and the full coupled problem

Order the edges as \(12,13,14,23,24,34\). Write \(a=(a_e)\) for special-atom weights and \(r=(\alpha,\beta,\gamma)\) for the three residual Laplacian coefficients. The legal allocation polytope is
\[
P(z)=\{a:0\le a\le w,\quad r+Ca\ge0\},
\]
where
\[
C=
\begin{pmatrix}
-2&-2& 2& 2&-2&-2\\
-2& 2&-2&-2& 2&-2\\
 2&-2&-2&-2&-2& 2
\end{pmatrix}.
\]

Thus the **residual changes** are:

| Special-atom edge group | Change |
|---|---|
| \(12,34\), special \(d_1\) | \(2s(-1,-1,+1)\) |
| \(13,24\), special \(d_2\) | \(2s(-1,+1,-1)\) |
| \(14,23\), special \(d_3\) | \(2s(+1,-1,-1)\) |

These are the negatives of the contributions removed by the special atoms.

Throughout I used
\[
u=\sum_e(2a_e-w_e)\ell_e
\]
and **one shared full \(19\times19\) Gram**, with six allocations and eight cubic gauges. The two parity blocks were not completed independently. The coordinate and gauge conventions are those in `organized/research/rational_sinkhorn_certificates.py:105–150` and `organized/research/verify_parity_reduced_completion.py:11–23`.

## 2. A general actual-spectral interpolation mechanism

### Proposition

Fix the support direction, the supporting permutation, and all but one complex eigenvalue. Let \(Q\) be a finite convex polygon of values of the remaining eigenvalue.

If every vertex of \(Q\):

* has the same supporting permutation;
* has a legal atom allocation;
* admits a PSD completion using the eight allowed cubic gauges;

then **every point of \(Q\)** admits such an allocation and completion.

### Proof

Along this actual spectral fiber, the contact height, all 24 original product comparisons, and every compound coefficient are real-affine in the varying complex eigenvalue. Consequently the canonical Gram blocks, \(w\), and \(r\) are affine too.

For barycentric weights \(\lambda_v\), use
\[
a=\sum_v\lambda_v a^{(v)},\qquad
k=\sum_v\lambda_v k^{(v)}.
\]
The capacity and residual inequalities interpolate, and the complete Gram satisfies
\[
X=\sum_v\lambda_vX^{(v)}\succeq0.
\]

This uses **affineness along actual spectra**, not an assertion that arbitrary convex combinations of formal profiles are actual. In particular, the same interpolated \(u\) and \(K\) satisfy both parity blocks.

There is a multivariable version: for a product of finite spectral polytopes, check every corner and use product barycentric weights. Actual coefficients are separately affine in each complex eigenvalue. **The common-contact hypothesis at all corners is essential.**

## 3. Exact completion of an entire maximal contact fiber

Fix
\[
\begin{aligned}
a&=(-4-4i,\,-2,\;1/100+x+i(-3+y),\,-1),\\
b&=(3i,\;4-i,\;-4+2i,\;1-3i),\qquad \eta=1.
\end{aligned}
\]
The identity contact height is
\[
h=\frac{153}{50}+6x-27y.
\]

I certified that the identity maximizes **all 24 original products exactly on the following bounded hexagon**:
\[
\begin{array}{rcl}
18-700x-475y&\ge&0,\\
5203+5300x-1350y&\ge&0,\\
241-5900x-8200y&\ge&0,\\
49-100x+450y&\ge&0,\\
137-1300x+2450y&\ge&0,\\
87-6300x+2450y&\ge&0.
\end{array}
\]

Its vertices, listed lexicographically rather than cyclically, are
\[
\begin{gathered}
(-107/100,-26/75),\\
(-169357/205700,\;1279/2057),\\
(-73/425,-5/34),\\
(-1/100,-3/49),\\
(53/4700,1/47),\\
(3417/188300,3/269).
\end{gathered}
\]

### What was checked exactly

For each of the six vertices, the certificate contains:

* six rational special-atom weights and eight rational cubic gauges;
* the complete rational \(19\times19\) Gram;
* two independent exact kernel vectors;
* an exact positive LDL factorization on a 17-dimensional principal submatrix.

Each full Gram is PSD of rank 17. The kernel coordinates deleted from the positive principal submatrix form an invertible \(2\times2\) matrix, so the principal-factorization certificate proves positivity of the **whole** Gram.

The verifier additionally checks:

* every original product comparison;
* every allocation capacity and residual inequality;
* all **838 polynomial coefficient positions**;
* exact coverage of all six distinct vertices;
* exact redundancy certificates deriving every original comparison from the six displayed halfplanes;
* boundedness and both endpoints of every hexagon edge.

These checks are implemented in `../../code/research/actual_fiber_allocation/verify_polygon.py`.

I also checked the triangle comparison identities and the actual Segre/discriminant linkage **symbolically throughout the complex fiber**, not merely at the vertices. Thus the construction retains the actual nonlinear spectral linkage.

### Constructive completion throughout the hexagon

Given any point in the hexagon, express it using nonnegative barycentric weights on its vertices. Apply those same weights to the six stored allocation vectors and eight-gauge vectors.

The interpolation proposition then proves full Gram positivity, **including on the boundary**.

This establishes a continuum theorem covering the **entire identity-support region for these seven fixed eigenvalues and this direction**. It is not a claim about all directions for each spectral pair.

### A short certificate at the original strict witness

Independently, at \(x=y=0\), one simple exact allocation is
\[
a=
\left(
\frac{419}{10},\frac3{10},\frac{223}{10},
\frac{461}{10},\frac15,\frac1{100}
\right),
\]
with raw cubic-gauge coefficients
\[
k=(371,118,-75,-414,18,176,-30,66)
\]
in the project’s ordered eight-gauge basis.

The residual Laplacian coefficients are
\[
\left(\frac58,\frac{10149}{200},\frac{23}{200}\right).
\]
Both parity blocks are strictly positive definite, with exact LDL certificates in `seed_certificate.json`.


## 4. A general rational criterion adaptive to actual odd data

The second result applies beyond the preceding fiber.

Use the actual profile
\[
z=(w_{12},w_{13},w_{14},w_{23},w_{24},w_{34},
d_1,d_2,d_3,J_{012},J_{013},J_{023},J_{123}).
\]
All matrices below are stored exactly in **`criterion.json`**.

Construct rational matrices \(F_j,V_i\) such that
\[
X(z,x)=\sum_{j=1}^{13}z_jF_j+\sum_{i=1}^{14}x_iV_i.
\]
The first six entries of \(x\) are the special weights; the remaining eight are cubic gauges in a fixed representative.

The verifier checks on **all 70 compound directions** that this representative differs from the raw actual cubic block by exactly the eight permitted gauges—no enlargement of the completion family. See `../../code/research/actual_fiber_allocation/verify_criterion.py`.

Let \(X_*>0,z_*,x_*\) be the exact seed certificate, and put \(W=X_*^{-1}\). Define
\[
\langle P,Q\rangle_W=\operatorname{tr}(WPWQ),
\]
\[
H_{ij}=\langle V_i,V_j\rangle_W,\qquad
N_{ij}=\langle V_i,F_j\rangle_W,\qquad
T=-H^{-1}N,
\]
\[
E_j=F_j+\sum_iT_{ij}V_i,\qquad
\mathcal C_{ij}=\langle E_i,E_j\rangle_W.
\]

The 14 directions are independent, hence \(H>0\). These arrays are rational and computed once.

For an **actual supported input** with
\[
g=\sum_e w_e>0,
\]
set
\[
\rho=\frac{g}{g_*},\qquad
\delta=z-\rho z_*,\qquad
x=\rho x_*+T\delta.
\]

### Sufficient criterion

A full completion is guaranteed if
\[
\boxed{
\quad x_{1:6}\in P(z),
\qquad
\delta^{T}\mathcal C\delta\le\rho^2.
\quad}
\]

This is a fixed rational linear/quadratic test, **not another SDP feasibility problem**.

### Proof

The resulting full Gram is
\[
X=\rho X_*+\Delta,\qquad \Delta=\sum_j\delta_jE_j.
\]
Moreover,
\[
\left\|X_*^{-1/2}\Delta X_*^{-1/2}\right\|_F^2
=\delta^T\mathcal C\delta\le\rho^2.
\]
Its most negative eigenvalue is therefore at least \(-\rho\), proving \(X\succeq0\).

This checks the full coupled matrix by congruence; it does not invoke a completion theorem after separately checking diagonal blocks.

The response \(T\) minimizes this relative Frobenius residual over all 14 parameters. Importantly, **all 24 entries coupling the six allocation responses to the four odd coordinates are nonzero**. The allocation therefore responds to the actual odd data.

The seed satisfies the inequalities strictly, so this gives a nonempty open sufficient region even when all spectra vary.


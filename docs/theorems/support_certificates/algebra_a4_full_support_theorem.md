# Full MOC for every actual tetrahedrally symmetric order-four cost

**Stronger closure theorem.** The subsequent proof in
algebra_border_simplex_inequality.md establishes \(Y+|Z|\le1\) for every
unitary profile. Consequently the theorem below holds for every real
tetrahedrally symmetric cost on the projected spectral secant closure,
including its border-only components. Actual spectral costs are a
special case. The complete three-branch proof remains organized below.

## The theorem

Let \(a,b\in\mathbb C^4\), let \(\eta\in\mathbb C\), and put

\[
c_\pi=\operatorname{Re}\left(\eta\prod_{i=1}^4(a_i+b_{\pi(i)})\right).
\]

Suppose \(c_{\sigma\pi\sigma^{-1}}=c_\pi\) for every
\(\sigma\in A_4\). Then, for every \(U\in U(4)\),

\[
\boxed{\operatorname{Re}\left(
\eta\det(D_a+UD_bU^*)\right)\le\max_{\pi\in S_4}c_\pi.}
\tag{1}
\]

This is a full-unitary theorem for every actual spectral support direction
with the stated tetrahedral symmetry. It does not assume that the spectrum
is real or collinear. It does not cover arbitrary nonsymmetric costs:
averaging an arbitrary actual cost over \(A_4\) need not preserve its
spectral realization or the projected secant nonic.

The proof combines the exact nonic factorization, the simplex theorem,
and the elementary minor certificates below. All computations used for the
factorization and finite-versus-border distinction are recorded in
algebra_a4_fixed_geometry.py and algebra_a4_fixed_geometry.json.
The complete simplex proof is in algebra_tetrahedral_simplex_inequality.md.

## 1. Three scalar profile coordinates

After subtracting the identity cost \(c_{\mathrm{id}}\), the class values
are

| Conjugacy class under \(A_4\) | Centered cost |
|---|---:|
| Identity | \(0\) |
| Transpositions | \(x\) |
| Double transpositions | \(y\) |
| Four-cycles | \(x+y/2\) |
| Two three-cycle classes | \(3x/2\pm k\) |

The relative support height is

\[
h=\max\{0,x,y,x+y/2,3x/2+|k|\}.
\tag{2}
\]

Use the squared-minor sums \(s_1,s_2,s_+,s_-,s_c\) defined in the companion
notes: diagonal one-minors, principal two-minors, the two oriented
twelve-element off-diagonal two-minor orbits, and complementary two-minors.

The centered cost on a unitary profile is

\[
c(U)-c_{\mathrm{id}}=xX(U)+yY(U)+kZ(U),
\tag{3}
\]

where the following identities all hold exactly:

\[
X=1+\frac{s_1-s_2}{2}=\frac{s_++s_-}{4},
\qquad
Y=\frac{s_c}{4},
\qquad
Z=\frac{s_--s_+}{6}.
\tag{4}
\]

Also

\[
s_2+s_++s_-+s_c=6,\qquad
s_c=2-2s_1+s_2,
\tag{5}
\]

and consequently

\[
X+2Y=2-\frac{s_1}{2}.
\tag{6}
\]

The identities are verified on the twenty-four permutation profiles, which
span the full common-minor profile space. Alternatively (5) follows from
compound-matrix unitarity and the ordinary row/column identities.

Since all five minor sums are nonnegative,

\[
X\ge0,\qquad 0\le Y\le1,\qquad |Z|\le1.
\tag{7}
\]

For the last inequality, use
\(|s_--s_+|\le s_-+s_+\le6\). Thus no quaternion argument is needed
for these elementary bounds.

## 2. The exact three-branch restriction

The projected M8 secant nonic restricts to

\[
P_9=\pm\frac1{32}
x(3y-4x)^2(4k^2+xy-x^2)^3.
\tag{8}
\]

Every actual centered spectral cost satisfies \(P_9=0\), so it lies on

\[
x=0,\qquad y=4x/3,\qquad
4k^2=x(x-y).
\tag{9}
\]

The derivation, including the three isotypic Hessian blocks, is in
algebra_a4_spectral_support.md.

The plane \(y=4x/3\) satisfies the full scalar support inequality by the
simplex theorem and its quaternion application in
algebra_tetrahedral_simplex_inequality.md. Its four polygonal support rays
have the explicit gaps

\[
s_++\frac23s_c,\quad s_-+\frac23s_c,\quad
\frac{-2+2s_1+4s_2+s_+}{3},\quad
\frac{-2+2s_1+4s_2+s_-}{3}.
\tag{10}
\]

The first two are elementary; the last two are the simplex theorem.

## 3. The entire quadratic branch has elementary certificates

Assume

\[
4k^2=x(x-y).
\tag{11}
\]

If \(x=0\), then \(k=0\), and Section 4 applies.
For \(x\ne0\), put \(r=2|k|/|x|\). Transposition exchanges \(s_+,s_-\)
and changes the sign of \(k\), so it is enough to assume \(k\ge0\).

### 3.1 Positive \(x\)

Now \(y=x(1-r^2)\), \(k=xr/2\), and direct comparison of the entries in
(2) gives

\[
h=x(3+r)/2.
\]

The support gap has the exact certificate

\[
\boxed{
\frac{h-xX-yY-kZ}{x}
=\frac{3+r}{12}s_2+\frac r6s_+
+\frac{r(3r+1)}{12}s_c\ge0.
}
\tag{12}
\]

One derivation starts with

\[
\frac{h-xX-yY-kZ}{x}
=\frac{s_2}{4}+r^2Y+\frac r2(1-Z),
\]

then uses \(1-Z=(s_2+s_c+2s_+)/6\).
All coefficients in (12) are nonnegative for every \(r\ge0\).

### 3.2 Negative \(x\), with \(0\le r\le1\)

Write \(x=-u\), \(u>0\). Then \(y=u(r^2-1)\), \(k=ur/2\).
In this range \(h=0\). Equations (3)--(4) give

\[
\boxed{
\frac{h-xX-yY-kZ}{u}
=\frac{3+r}{12}s_+
+\frac{3-r}{12}s_-
+\frac{1-r^2}{4}s_c\ge0.
}
\tag{13}
\]

### 3.3 Negative \(x\), with \(r\ge1\)

Here \(h=u(r^2-1)\). Using
\(1-Y=X/2+s_1/4\), which follows from (6), gives

\[
\boxed{
\frac{h-xX-yY-kZ}{u}
=\frac{3r^2+2r+3}{24}s_+
+\frac{3r^2-2r+3}{24}s_-
+\frac{r^2-1}{4}s_1\ge0.
}
\tag{14}
\]

The middle coefficient is strictly positive:
\(3r^2-2r+3=3(r-1/3)^2+8/3\).
This proves the entire quadratic branch without requiring finite actual
spectral realizability.

## 4. The remaining \(x=0\) component

The stronger argument now covers this entire component. The complementary
simplex theorem gives \(Y+|Z|\le1\), and here
\(h=\max(0,y,|k|)\). Therefore

\[
yY+kZ\le hY+h|Z|\le h.
\tag{15a}
\]

Equivalently, the new pair of minor inequalities is

\[
s_c\le2s_2+4s_+,
\qquad s_c\le2s_2+4s_-.
\tag{15b}
\]

This removes every finite-realizability requirement from the support
proof on this component. The following algebraic distinction is still
valid and records why the original actual-cost theorem had already
closed before the stronger inequality was found.

The exact finite-secant calculation in
algebra_a4_real_form_and_full_unitary_target.md proves that a point with

\[
x=0,\qquad yk\ne0
\]

cannot be an actual spectral cost. Its unique cubic lift has a
two-dimensional Hessian kernel on which the gradient is supported in
coordinate 0, whereas the required target gradient has coordinate 1
equal to \(k^2\ne0\). This excludes a finite secant representation,
even over the complexes.

Thus every actual point on \(x=0\) belongs to one of its axes:

* If \(k=0\), its cost is \(yY\), and \(0\le Y\le1\) proves
  \(yY\le\max(0,y)=h\).
* If \(y=0\), its cost is \(kZ\), and \(|Z|\le1\) proves
  \(kZ\le|k|=h\).

No assertion about the generic border-only part of \(x=0\) is needed.

Every branch in (9) that can contain actual costs is now proved.
This establishes Theorem (1).

## 5. A finite complex pair covered in every support direction

Let \(\omega=(-1+i\sqrt3)/2\) and

\[
a=(0,1/2,-\omega^2,-\omega),\qquad
b=\left(-1,1,\frac{2\omega-1}{7},\frac{2\omega^2-1}{7}\right).
\]

Every support cost of this pair belongs to the plane \(y=4x/3\), so
Theorem (1) proves full complex MOC for this pair. The twenty-four
products, after multiplication by \(7/9\), have convex hull

\[
\operatorname{conv}\left\{-\frac32,\frac16,
\frac{i}{\sqrt{12}},-\frac{i}{\sqrt{12}}\right\}.
\]

The exact products and the full support proof are in the companion
simplex note. The pair illustrates that the theorem includes genuinely
complex, noncollinear finite spectra.

### Projective covariance gives a continuous family of spectral pairs

The same conclusion holds throughout the following fractional-linear
orbit of this pair. Let

\[
f(z)=\frac{\alpha z+\beta}{\gamma z+\delta},
\qquad \Delta=\alpha\delta-\beta\gamma\ne0,
\]

and assume that none of the displayed spectral values is a pole. Set

\[
a'_i=f(a_i),\qquad b'_j=-f(-b_j).
\]

Then

\[
a'_i+b'_j=
\frac{\Delta(a_i+b_j)}{(\gamma a_i+\delta)(\delta-\gamma b_j)}.
\tag{15}
\]

For every unitary \(U\),

\[
\det(D_a+UD_bU^*)=\frac{\det[(a_i+b_j)U_{ij}]}{\det U}.
\tag{16}
\]

Equation (15) multiplies every row and every column of the determinant
in (16) by fixed scalars. Therefore every determinant value and every
permutation product is multiplied by the same nonzero scalar

\[
\kappa=\frac{\Delta^4}
{\prod_i(\gamma a_i+\delta)\prod_j(\delta-\gamma b_j)}.
\tag{17}
\]

Convex containment is preserved under multiplication by \(\kappa\).
The explicit pair theorem thus transports to its entire finite
fractional-linear orbit. This covariance is a direct algebraic identity;
it does not assert that arbitrary configurations belong to that orbit.

## Remaining obstruction

For a general actual cost \(c\), the \(A_4\)-average of \(c\) is a valid
linear profile functional, but it may leave the projected secant nonic.
The theorem therefore cannot be applied to that average without an
additional estimate. One proposed missing estimate compares the full
twenty-four-entry support height with the three averaged coordinates;
it remains unproved.


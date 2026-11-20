# Coefficient descent, characteristic two, and the positivity obstruction

**Status.** The statements proved below are algebraic/valuation analogues, not a proof of complex Marcus–de Oliveira (MOC). They distinguish a genuine removal of middle-minor interference from the loss of the order needed for convexity. No publication-priority claim is made. The affine identity extends the existing finite-field treatment in `../finite/finite_field_theorems.md`; the new applications here include integral coefficient descent in every dimension and the explicit characteristic-two/Frobenius distinction.

Let D_a=diag(a_1,...,a_n), D_b=diag(b_1,...,b_n), and

\[
z_\pi(a,b)=\prod_i(a_i+b_{\pi(i)}).
\]

## 1. An all-dimensional coefficient-descent theorem

Let S be a commutative ring with involution, R a subring of its fixed ring, and suppose there is an R-linear retraction

\[
\rho:S\longrightarrow R,\qquad \rho(r)=r\quad(r\in R).
\]

Let U be an invertible matrix over S satisfying U^{-1}=U^*. Assume every minor norm

\[
q_{I,J}=\det U[I,J]\,\overline{\det U[I,J]}
\]

belongs to R. Define the determinant amplitudes and their descended coefficients by

\[
c_\pi=\frac{\operatorname{sgn}(\pi)\prod_i u_{i,\pi(i)}}{\det U},
\qquad p_\pi=\rho(c_\pi).
\]

Then, simultaneously for all equal-cardinality I,J,

\[
\boxed{\sum_{\pi:\pi(I)=J}p_\pi=q_{I,J},\qquad
\sum_\pi p_\pi=1.}                                      \tag{1}
\]

Consequently, for arbitrary spectra in S,

\[
\boxed{\det(D_a+UD_bU^*)=\sum_\pi p_\pi z_\pi(a,b).}       \tag{2}
\]

These identities impose no positivity on p.

### Proof

For any invertible U, not necessarily unitary,

\[
(D_a+UD_bU^{-1})U=D_aU+UD_b.
\]

The ij entry on the right is (a_i+b_j)u_{ij}. Leibniz expansion therefore gives

\[
\det(D_a+UD_bU^{-1})=\sum_\pi c_\pi z_\pi.                \tag{3}
\]

Its coefficient of the monomial a_{I^c}b_J is, by principal-minor expansion and Cauchy–Binet,

\[
\sum_{\pi:\pi(I)=J}c_\pi
 =\det U[I,J]\det U^{-1}[J,I].                           \tag{4}
\]

For unitary U the right side is q_{I,J}. Apply rho to (4); since rho fixes each q_{I,J}, this proves (1). Reassemble the determinant from its minor coefficients to obtain (2).

It would be incorrect to obtain (2) simply by applying rho to (3): the spectral products need not belong to R, and rho need not be multiplicative. Descent takes place on the minor coefficients first.

## 2. Integral-unitary affine containment over every quadratic local field

Let L/K be any separable quadratic extension of non-Archimedean local fields, with integral rings O_L and O_K, including ramified extensions in residue characteristic two. For

\[
U\in U_n(O_L),\qquad a,b\in L^n,
\]

there exist coefficients p_pi in O_K with sum one such that

\[
\boxed{\det(D_a+UD_bU^*)=\sum_\pi p_\pi z_\pi.}           \tag{5}
\]

Thus the determinant lies in the O_K-affine hull of the permutation products, in every dimension.

### Integral retraction without dividing by two

O_L is a finite free O_K-module. The element 1 is primitive: it does not belong to varpi_K O_L, because it is a unit. Over the DVR O_K, it therefore extends to an O_K-basis of O_L. Projection onto its coordinate gives an O_K-linear retraction rho:O_L -> O_K.

The determinant of an integral unitary matrix is a unit, since its inverse is its conjugate. Hence every c_pi is integral. Minor norms lie in O_L intersect K = O_K, so Section 1 applies to the coefficients. Formula (5) then holds for all spectra in L, by its polynomial coefficient identity.

This proof does not assume that the integral trace is onto. For example, in L=Q_2(i), the trace on Z_2[i] has image 2 Z_2, while the coordinate retraction a+bi -> a is integral. In this particular extension the retraction happens to equal half-trace. Half-trace is not uniformly integral: in the unramified quadratic extension Q_2(sqrt(5)), the integral element alpha=(1+sqrt(5))/2 has trace 1, so its half-trace is 1/2, not integral. Coordinate projection onto an integral basis containing 1 avoids both issues.

For the extended non-Archimedean absolute value on L, (5) gives the concrete bound

\[
\boxed{|\det(D_a+UD_bU^*)-z_{\pi_0}|
 \le \max_\pi |z_\pi-z_{\pi_0}|.}                        \tag{6}
\]

Indeed subtract z_pi0 and use |p_pi|<=1 and the ultrametric triangle inequality. This is containment, not an exact image assertion. The order-two norm restrictions in `../adeles/padic_integral_unitary_ranges.md` show why equality need not hold.

## 3. Exact characteristic-two orthogonal formula

Let K be a field of characteristic two and U^T U=I. Then det U=1, because (det U)^2=1 and a field has no nonzero nilpotents. Set

\[
c_\pi=\prod_i u_{i,\pi(i)}.
\]

For all I,J of equal size,

\[
\boxed{\sum_{\pi:\pi(I)=J}c_\pi=(\det U[I,J])^2.}         \tag{7}
\]

A direct proof groups permutations into independent bijections I->J and I^c->J^c:

\[
\sum_{\pi:\pi(I)=J}c_\pi
 =\operatorname{per}U[I,J]\operatorname{per}U[I^c,J^c]
 =\det U[I,J]\det U[I^c,J^c]
 =(\det U[I,J])^2.
\]

Here permanent equals determinant, and the last equality is Jacobi's complementary-minor identity for an orthogonal matrix with determinant one.

There is also a literal elimination of independent middle coefficients. If P=(u_ij^2), Frobenius gives

\[
\boxed{q_{I,J}=(\det U[I,J])^2=\det P[I,J].}              \tag{8}
\]

Thus the singleton table P determines every minor coefficient algebraically. In characteristic zero the interference must be measured relative to the permanent of the squared entries, not just their determinant. For a two-by-two submatrix with entries x,y,z,w in row order, the exact identity is

\[
(xw-yz)^2=x^2w^2+y^2z^2-2xyzw
=\det\begin{pmatrix}x^2&y^2\\z^2&w^2\end{pmatrix}
 +2y^2z^2-2xyzw.
\]

The cross term -2xyzw is not determined by the squared-entry table. Characteristic two annihilates both corrections to the determinant in this display.

### Important correction: do not square the permutation amplitudes

The proposed weights w_pi=product_i u_i,pi(i)^2 give

\[
\sum_{\pi:\pi(I)=J}w_\pi=q_{I,J}^2,
\]

not q_{I,J}. They reproduce all the requested marginals if and only if every entry of U lies in F_2. Necessity follows from singleton equations u_ij^4=u_ij^2; sufficiency follows from (7).

For example, over F_2(t),

\[
U=\begin{pmatrix}t&1+t\\1+t&t\end{pmatrix}
\]

is orthogonal. Its singleton coefficient is t^2, whereas the squared-amplitude prescription gives t^4. This is an algebraic failure, not just a missing notion of positivity.

## 4. A nontrivial involution retains interference in characteristic two

Let L have characteristic two and a nontrivial involution, with fixed field K. For unitary U use

\[
c_\pi=\frac{\prod_i u_{i,\pi(i)}}{\det U}.
\]

Choose theta with theta+bar(theta)=1. The retraction

\[
\rho(x)=\theta x+\bar\theta\bar x
\]

gives fixed-field coefficients p_pi=rho(c_pi) and all the identities in (1). Such theta exists: for beta outside K, take theta=beta/(beta+bar(beta)).

In contrast, the norm-product weights w_pi=N(c_pi) obey, for E={pi:pi(I)=J},

\[
q_{I,J}^2=\sum_{\pi\in E}w_\pi+
\sum_{\{\pi,\sigma\}\subset E}
(c_\pi\bar c_\sigma+c_\sigma\bar c_\pi).                 \tag{9}
\]

The mixed trace x bar(y)+y bar(x) need not vanish in characteristic two.

An exact counterexample is the unitary Fourier matrix over F_4:

\[
F=\begin{pmatrix}1&1&1\\1&\omega&\omega^2\\1&\omega^2&\omega\end{pmatrix},
\qquad\omega^2+\omega+1=0,\quad\bar x=x^2.
\]

Every nonzero entry has norm one. All six permutation norm-products equal one, and their sum is 6=0, not 1. Thus they cannot even be normalized by their total mass. The affine descent theorem remains valid.

## 5. What happens over ordered fields

For C/R, rho=Re produces real coefficients but not necessarily nonnegative ones. For every real-closed extension R of the ordered real field, the fixed-dimensional MOC statement over R(i) is first-order and has the same truth value as over C. This equivalence, already established in `../README.md`, does not prove either statement.

There is a stronger obstruction than the absence of an order in characteristic two. The rational path in

`../../theorems/profile_geometry/algebra_local_marginal_obstruction.md`

lies in SO(4), tends to the identity, and violates a universal positive pair-marginal inequality by

\[
\frac{2t^4(1-2t^2-t^4)}{(1+t^2)^4}>0
\quad(0<t^2<\sqrt2-1).
\]

Its obstruction is annihilated in characteristic two. Thus a positive lift preserving the full determinant polynomial fails even arbitrarily close to the identity. The problem is not fixed by replacing real numbers by ordered infinitesimals.

## 6. A concrete framework: descend coefficients, then impose the right coefficient set

The common object is the linear incidence map

\[
(Tp)_{I,J}=\sum_{\pi:\pi(I)=J}p_\pi.
\]

The computations above distinguish three actual coefficient problems:

1. Over a fixed field K, solve Tp=q with sum p=1: the retraction theorem solves it.
2. Over O_K, impose integral coefficients: the integral-retraction theorem solves it for integral unitaries.
3. Over an ordered real field, impose p>=0: this stronger simultaneous problem is false already in dimension four.

Original MOC is weaker than problem 3. After fixing a,b it requires only

\[
\sum_\pi p_\pi=1,\qquad p_\pi\ge0,\qquad
\sum_\pi p_\pi z_\pi(a,b)=\det(D_a+UD_bU^*).
\]

The kernel available after this spectral evaluation is larger than the kernel of T. A successful characteristic-zero proof must exploit that enlargement, or prove the support inequalities directly. The field changes above solve the affine/integral coefficient questions and expose an exact obstruction to universal positive descent; they do not establish that remaining evaluated positivity assertion.

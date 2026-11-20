# A dimension-four transpose theorem and its dimension-five boundary

## 1. Statements and scope

Let

\[
 R(U)_{I,J}=|\det U[I,J]|^2,\qquad |I|=|J|,
\]

and let \(\mathcal P_n\) be the convex hull of the profiles of the \(n!\) permutation matrices. Write \(v_0=R(I)\). A real common-minor cost is a real linear functional \(F\) of the graded profile; write \(c_\pi=F(R(P_\pi))\), with the convention \((P_\pi)_{i,\pi(i)}=1\).

The following two theorems hold in dimension four:

**Theorem A.** If \(c_{\mathrm{id}}=\max_\pi c_\pi\), then
\[
 F(R)\le c_{\mathrm{id}}
\]
for every Hermitian unitary matrix \(R\in U(4)\).

**Theorem B.** Suppose in addition that \(c_\pi=c_{\pi^{-1}}\) for every permutation. Then
\[
 F(U)\le c_{\mathrm{id}}
\]
for every \(U\in U(4)\).

In these statements, \(F(U)\) abbreviates evaluation on the common-minor profile. Both theorems keep the maximizing identity assumption. Theorem B gives an actual scalar MOC support theorem for every inversion-even spectral cost in a support direction whose identity pairing is maximal. It does not settle directions maximized by another pairing.

These statements are restricted to dimension four and to the maximizing-identity hypothesis; no higher-dimensional extension for arbitrary common-minor costs is asserted.

## 2. Every linear vertex identity holds for actual unitary profiles

For a unitary \(U\), define complex coefficients

\[
 w_\pi(U)=\frac{\operatorname{sgn}(\pi)}{\det U}
                 \prod_iU_{i,\pi(i)}.
\]

Then

\[
 \sum_\pi w_\pi=1,\qquad
 R(U)_{I,J}=\sum_{\pi:\pi(I)=J}w_\pi.
 \tag{1}
\]

To prove the second identity, group the determinant expansion by the bijections \(I\to J\) and \(I^c\to J^c\). The grouped numerator is the shuffle sign times
\(\det U[I,J]\det U[I^c,J^c]\). The complementary-minor identity for \(U^{-1}=U^*\) says

\[
 \det U[I^c,J^c]
 =(-1)^{\sum I+\sum J}\det U\,
    \overline{\det U[I,J]}.
\]

The shuffle signs cancel, giving (1). Since its left side is real, one may replace every \(w_\pi\) by \(\Re w_\pi\). These real coefficients sum to one, but need not be nonnegative.

Consequently all actual profiles lie in the affine hull of permutation profiles. More particularly, every linear identity checked on all permutation profiles holds on every unitary profile. This is why exact integer checks on 24 vertices certify the squared-minor identities used below.

Transpose acts on profiles by \(R(U^T)_{I,J}=R(U)_{J,I}\) and sends \(P_\pi\) to \(P_{\pi^{-1}}\). If \(c_\pi=c_{\pi^{-1}}\), (1) implies

\[
 F(U)=F(U^T)
 \tag{2}
\]

for every unitary \(U\), whether or not a common positive permutation law exists.

## 3. Exact active-facet certificates

The complete dimension-four facet theorem in COMMON_MINOR_POLYTOPE.md establishes that the 13-dimensional affine polytope \(\mathcal P_4\) has 82 facets:

1. sixteen nonnegativity inequalities for level-one entries;
2. eighteen distinct nonnegativity inequalities for level-two entries, after complementary pairs are identified;
3. forty-eight independent row/column relabelings of
   \[
   R_{33}+R_{24}+R_{12,13}-R_{13,23}\ge0.
   \tag{3}
   \]

The separate integer boundary-chain certificate proves completeness; floating-point facet discovery is not being used as a completeness argument.

Of the forty-eight facets in (3), exactly twenty-six vanish at \(v_0\). For each such facet \(f\), the accompanying exact certificate records an identity

\[
 f(U)+f(U^T)=\sum_{I\ne J}k_{I,J}R(U)_{I,J},
 \qquad k_{I,J}\in\mathbb Z_{\ge0}.
 \tag{4}
\]

The coefficients are checked by code/theorems/finite_and_spin_geometry/continuous_reversible_tangent_cone_exact.py. The verifier constructs all row/column relabelings of (3), deduplicates their vertex vectors to get forty-eight facets, selects precisely those with value zero at identity, and checks every coefficient and every identity in (4) by integer arithmetic on all twenty-four vertices. Equation (1) then proves (4) for all actual unitaries. The default verification uses only the Python standard library; the fixed certificate does not require a numerical optimization routine.

For example, one active facet has the particularly short identity

\[
 \begin{aligned}
 f(U)&=R_{31}+R_{24}+R_{12,13}-R_{13,12},\\
 f(U)+f(U^T)&=R_{31}+R_{13}+R_{24}+R_{42}.
 \tag{5}
 \end{aligned}
\]

Every term on the right side of (4) is nonnegative for an actual unitary. It vanishes at identity, as required for an active tangent-cone certificate.

## 4. Tangent-cone proof of Theorems A and B

Use the affine tangent cone

\[
 \mathcal T_0=v_0+\operatorname{cone}\{v_\pi-v_0:\pi\in S_4\}.
\]

For a polytope given by a complete facet system, this cone is characterized within the affine hull by the inequalities of exactly the facets active at \(v_0\). Indeed an active facet must remain nonnegative along a feasible ray. Conversely, a vector satisfying all active inequalities gives a feasible small step from \(v_0\), because the finitely many inactive inequalities have strictly positive slack there.

For any \(U\in U(4)\), let

\[
 X=\frac12(R(U)+R(U^T)).
\]

This lies in the correct affine hull by (1). Its entries are nonnegative, so the active basic facets hold. Its twenty-six active mixed facets are nonnegative by (4). Therefore

\[
 \boxed{
 \frac12(R(U)+R(U^T))\in\mathcal T_0
 \qquad\hbox{for every }U\in U(4).}
 \tag{6}
\]

If identity maximizes \(F\) on the permutation vertices, then
\(F(v_\pi-v_0)\le0\) for every generator of the cone. Thus \(F(X)\le F(v_0)\).

When \(R=R^*\), complementary transpose minors are complex conjugates and have the same squared modulus. Hence \(R(R)=R(R^T)\), so (6) proves Theorem A. This covers all Hermitian unitaries of order four, with any multiplicity of the eigenvalues \(+1,-1\).

When the cost is inversion-even, (2) gives \(F(X)=F(U)\). Applying the same cone bound proves Theorem B.

Notice that the conclusion is tangent-cone membership. It does not assert \(R(R)\in\mathcal P_4\). In fact an earlier exact rank-two reflection has no common permutation law. A point can leave a polytope while remaining in its tangent cone at one vertex.

## 5. Actual spectral support consequences

For diagonal spectra \(a,b\), the determinant is a common-minor linear cost:

\[
 \det(A+UBU^*)
 =\sum_{|I|=|J|}a_{I^c}b_JR(U)_{I,J}.
 \tag{7}
\]

Here \(a_{I^c}=\prod_{i\notin I}a_i\) and \(b_J=\prod_{j\in J}b_j\). This follows by expanding the determinant in the diagonal \(A\), then using Cauchy–Binet on the selected principal minor of \(UBU^*\). For the stated row convention on a permutation matrix, (7) evaluates to \(\prod_i(a_i+b_{\pi(i)})\), so no inverse-permutation convention is hidden in the application.

Take the real part after multiplying by any complex \(\eta\). If the resulting spectral vertex cost obeys \(c_\pi=c_{\pi^{-1}}\), Theorem B proves its support inequality on all \(U(4)\), provided identity is a support maximizer.

In particular, if \(a=b\), the products satisfy

\[
 \prod_i(a_i+a_{\pi(i)})
 =\prod_i(a_i+a_{\pi^{-1}(i)}).
\]

Thus every support direction of the isospectral four-dimensional problem whose identity vertex is maximal is solved by Theorem B. A proof for every support direction would require an additional argument controlling a maximizing nonidentity base.

That qualification is substantial. For the already elementary three-dimensional example

\[
 a=b=(1,\omega,\omega^2),\qquad \omega^3=1,\quad \omega\ne1,
\]

the identity product is \(8\), each transposition product is \(2\), and each three-cycle product is \(-1\). In direction \(\eta=-1\), a three-cycle is maximal and identity is not. Reordering only one spectrum to make such a pairing the identity does not preserve the displayed isospectral pairing. This example does not challenge MOC; it shows exactly why the hypothesis of Theorem B cannot be silently discarded.

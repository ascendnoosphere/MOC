# Every order-four rank-two reflection contact has zero cubic covector

Direct track, campaign 3. This is a boundary theorem for the actual complex
MOC support problem. It does not prove the positive-gap energy inequality or
unrestricted MOC.

## 1. Statement and inputs

Let

\[
F(U)=\Re\!\left\{\eta\det(D_a+UD_bU^*)\right\},\qquad
h=F(I)=\max_{\pi\in S_4}\Re\!\left\{\eta\prod_i(a_i+b_{\pi(i)})\right\}.
\]

Let \(Y:\mathbb C^2\longrightarrow\mathbb C^4\) be an isometry, put
\(P=YY^*\), and let \(R=I-2P\). Thus \(R\) is Hermitian unitary,
\(\operatorname{tr}R=0\), and \(\det R=1\).

**Theorem.** If \(F(R)=h\), the cubic covector \(\ell\) of this full
complex two-plane orbit is zero. Consequently

\[
\boxed{F\bigl(I+Y(V-I)Y^*\bigr)\le h\quad\text{for every }V\in U(2).}
\tag{1}
\]

The proof uses three established results in the second campaign:

1. The common squared-minor permutation polytope in order four has 82
   facets: 16 singleton facets, 18 complementary two-minor facets, and 48
   mixed facets. Identities among these functions on all permutations hold
   on all actual unitary squared-minor profiles.
2. Exactly 26 mixed facets are active at the identity. For each such facet
   \(f\), the identity \(f(U)+f(U^T)=\sum k_{I,J}|\det U[I,J]|^2\), with
   \(k_{I,J}\ge0\), is exact. Hence every active facet has nonnegative
   value at every Hermitian unitary.
3. **Derangement-face classification.** If a nonnegative spectral support
   deficit vanishes on all nine derangements relative to a permutation
   \(\pi_0\), then it equals
   \(\sum_i w_i\mathbf1_{\{\pi(i)=\pi_0(i)\}}\), with nonnegative weights
   and at most two positive weights. Its unitary extension is
   \(\sum_iw_i|U_{i,\pi_0(i)}|^2\).

The third input is where the nonlinear spectral geometry enters. In the
prior proof the projected degree-nine equation restricts on this face to
the cube of a cubic. Positivity forces that cubic to vanish only on the
two-weight assignment cones. The classification holds on the real points
of the entire projected complex secant closure, so the exact Hessian test
for the actual real spectral branch is not additionally required here.
Actual complex spectral costs satisfy the projected equation and are
therefore covered. No claim that the nonic alone proves MOC away from this
face is used.

References within the work record:

- `../moc200/continuous_reversible_dimension_boundary.md`;
- `../moc200/continuous_reversible_tangent_cone_exact.py` / `.json`;
- `../moc200/dual_derangement_secant_rigidity.md`;
- `../moc200/continuous_full_rank_two_geometry.md`;
- `../moc200/continuous_spectral_rank_two_budget.md`.

This note supplies the geometric classification needed to pass from the
previous single-reflection result to **all** rank-two reflection contacts.

## 2. Reduce a zero gap to individual active facet contacts

Write \(g(U)=h-F(U)\). Its permutation values are nonnegative and
\(g(I)=0\). By the facet description, within the common-minor linear space
there is a nonnegative decomposition

\[
g(U)=\sum_\alpha r_\alpha\rho_\alpha(U)
       +\sum_{k=1}^{26}t_k f_k(U),\qquad r_\alpha,t_k\ge0.
\tag{2}
\]

Here the \(\rho_\alpha\) are singleton or two-minor facets active at the
identity, and \(\rho_{I,J}(U)=|\det U[I,J]|^2\). Constants and complementary
duplicates are handled in the affine span of the polytope. This is the
usual dual description of its tangent cone at the identity.

Every summand in (2) has nonnegative value at \(R\). Thus \(g(R)=0\)
implies that every summand having a positive coefficient vanishes at \(R\).
A basic squared-minor summand that vanishes at \(R\) has zero differential
there, since it is the squared modulus of a differentiable complex
function whose value is zero. The endpoint derivative identity from the
full-plane theorem then gives zero cubic covector for this summand.

Only zero contacts of the mixed facets need analysis.

## 3. The 26 mixed facets have three conjugation orbits

Use one-based labels in this note. Simultaneously permuting rows and
columns preserves the identity and the reflection condition. The exact
26-facet catalog splits into three orbits, of sizes 8, 12, and 6.

Representatives are

\[
\begin{aligned}
f_A&=\rho_{3,4}+\rho_{2,3}+\rho_{12,14}-\rho_{13,24},\\
f_B&=\rho_{3,4}+\rho_{2,3}+\rho_{12,24}-\rho_{13,14},\\
f_C&=\rho_{3,4}+\rho_{2,1}+\rho_{12,24}-\rho_{13,34}.
\end{aligned}
\tag{3}
\]

The finite orbit computation is exact integer permutation arithmetic in
`direct_reflection_contact_exact.py`. Its indices refer to the existing
zero-based JSON catalog. The orbits of catalog representatives 0, 2, 4
have respectively 8, 12, 6 elements and exhaust the catalog.

Their transpose symmetrizations are

\[
\begin{aligned}
f_A(U)+f_A(U^T)
={}&\rho_{13,12}+\rho_{13,14}+\rho_{23,24}
 +\rho_{23,34}+\rho_{34,23}+\rho_{34,24},\\
f_B(U)+f_B(U^T)
={}&2\rho_{13,24}+\rho_{24,12}+\rho_{24,34}
 +\rho_{34,13}+\rho_{34,24},\\
f_C(U)+f_C(U^T)
={}&\rho_{1,2}+\rho_{2,1}+\rho_{3,4}+\rho_{4,3}.
\end{aligned}
\tag{4}
\]

For Hermitian \(R\), its squared-minor profile is symmetric, so the left
side of each line is \(2f(R)\). A zero contact therefore makes every
displayed squared minor zero.

## 4. Orbit A contacts force two-coordinate blocks

Suppose \(f_A(R)=0\). Complementary minors of a determinant-one unitary
satisfy the Jacobi relation

\[
\det R[I,J]=(-1)^{\sum I+\sum J}
\overline{\det R[I^c,J^c]}.
\tag{5}
\]

The zero minors in the first line of (4), using (5) and Hermitian
symmetry, imply

\[
\det R[\{1,i\},\{1,j\}]=0
\quad(2\le i\ne j\le4).
\tag{6}
\]

Write

\[
R=\begin{pmatrix}r&v^*\\v&H\end{pmatrix},\qquad r\in\mathbb R.
\]

Equation (6) says \(rH-vv^*\) is diagonal.

If \(r=0\), then \(vv^*\) is diagonal, so at most one coordinate of
\(v\) is nonzero. If \(r\ne0\), write
\(H=D+vv^*/r\) with real diagonal \(D\). From \(R^2=I\),
\(\|v\|^2=1-r^2\) and \((rI+H)v=0\). On every nonzero coordinate of
\(v\) this gives \(D_{ii}=-1/r\).

If at least two coordinates of \(v\) were nonzero, choose a nonzero
vector \(w\) supported on those coordinates and orthogonal to \(v\).
Then \(R(0,w)=-(0,w)/r\). Since all eigenvalues of \(R\) are \(\pm1\),
this forces \(r^2=1\), contradicting \(\|v\|^2>0\). Hence again at most
one coordinate of \(v\) is nonzero.

When \(v=0\), necessarily \(r=\pm1\), and (6) makes \(H\) diagonal.
When exactly one coordinate is nonzero, the corresponding two coordinate
positions form an invariant block: the remaining off-block entries vanish
by the first row of \(R^2=I\). The remaining two coordinates form another
block. Thus \(R\) is block diagonal, after a coordinate permutation, with
blocks of size at most two.

## 5. Orbit B contacts force the same blocks

Suppose \(f_B(R)=0\). Use the ordered partition
\(E=\{1,3\}\), \(F=\{2,4\}\), and write

\[
R=\begin{pmatrix}A&X\\X^*&D\end{pmatrix}.
\]

The first term of the second line of (4) gives \(\det X=0\). If \(X=0\),
the required coordinate-block form already holds.

Otherwise write \(X=suv^*\), with \(s>0\) and unit vectors
\(u,v\in\mathbb C^2\). The equations \(R^2=I\) give

\[
A^2=I-s^2uu^*,\quad D^2=I-s^2vv^*,\quad AX+XD=0.
\]

Since \(s>0\), \(A\) preserves \(\mathbb Cu\) and its orthogonal
complement, and similarly for \(D\). Together with \(\operatorname{tr}R=0\),
these equations give real \(a\) and \(\varepsilon\in\{1,-1\}\) such that

\[
A=\varepsilon I+(a-\varepsilon)uu^*,\qquad
D=-\varepsilon I+(\varepsilon-a)vv^*,\qquad a^2+s^2=1.
\tag{7}
\]

Two more zero minors in (4), with the orders of \(E,F\) above, are

\[
\begin{aligned}
\det R[F,\{1,2\}]&=s\varepsilon\overline{u_1}v_2=0,\\
\det R[F,\{3,4\}]&=-s\varepsilon\overline{u_2}v_1=0.
\end{aligned}
\tag{8}
\]

Because \(u,v\) are unit vectors, (8) forces both to be coordinate
vectors, with the same coordinate position. The only nontrivial coupling
in \(X\) then joins two individual coordinate positions. The other two
positions are eigenvectors. This is again the required block form.

## 6. Such blocks annihilate every cubic covector

If a rank-two reflection in four dimensions splits into coordinate blocks
of size at most two, choose a basis of its negative eigenspace separately
on those blocks. Every frame row is then a multiple of one of at most two
orthogonal vectors. Thus every rank-one effect
\(W_i=y_i^*y_i\) is a nonnegative multiple of either \(E_{11}\) or
\(E_{22}\).

For every Hermitian \(T\),

\[
C_{ijk}(T)=-\Im\operatorname{tr}
  \bigl(\operatorname{adj}(W_i)W_jTW_k\bigr)=0.
\tag{9}
\]

Indeed the trace is either zero or a real multiple of a diagonal entry
of \(T\). Therefore \(\ell=4\sum s_{ijk}C_{ijk}\) is zero for **every**
common-minor cost, without invoking a spectral restriction.

This completes both the 8-element and 12-element facet orbits.

## 7. Orbit C: classify reflections with opposite entry zeros

Suppose \(f_C(R)=0\). The last line of (4) gives
\(R_{12}=R_{34}=0\). Thus

\[
R=\begin{pmatrix}
a_1&0&x&y\\
0&a_2&z&w\\
\bar x&\bar z&a_3&0\\
\bar y&\bar w&0&a_4
\end{pmatrix}.
\tag{10}
\]

If all four of \(x,y,z,w\) are nonzero, the cross-block equations in
\(R^2=I\) give
\(a_1=a_2=-a_3=-a_4=a\). The cross block is consequently
\(\sqrt{1-a^2}\,Q\) for a two-by-two unitary \(Q\).

If a cross entry is zero, the equations making the two rows and the two
columns of this cross block orthogonal show that its nonzero entries form
a partial matching. To see the only potentially problematic case, three
nonzero entries connect all four vertices, forcing the same diagonal
equalities as above; a two-by-two unitary cannot have exactly three
nonzero entries. Two entries sharing a row or a column violate the other
orthogonality equation. Thus the reflection already splits into coordinate
blocks of size at most two.

In the remaining nonblock case, diagonal phase conjugation makes \(Q\)
real orthogonal. Such conjugation preserves the actual determinant support
because both original spectral matrices are diagonal. After harmless signs
and coordinate permutations, the reflection has the form

\[
\boxed{
R(a,b,c)=\begin{pmatrix}
a&0&b&c\\
0&a&-c&b\\
b&-c&-a&0\\
c&b&0&-a
\end{pmatrix},\qquad a^2+b^2+c^2=1.
}
\tag{11}
\]

Here \(bc\ne0\). Cases with \(bc=0\) have the preceding coordinate-block
form.

## 8. The nonbalanced family: the full spectral deficit is an assignment cost

Assume \(abc\ne0\). On the reflection family (11), the exact homogeneous
slack calculation proves:

- Only two of the 26 active mixed facets vanish, catalog facets 4 and 17.
- Every other active mixed-facet slack is a nonzero polynomial in
  \(a^2,b^2,c^2\), homogeneous of degree two in those variables, with
  nonnegative coefficients.
- Among basic active singleton and two-minor facets, exactly the four
  singleton entries \((1,2),(2,1),(3,4),(4,3)\) vanish. Every other basic
  slack is a nonzero polynomial with nonnegative coefficients.

The single-entry terms in the mixed facets have been homogenized by
\(a^2+b^2+c^2=1\). All polynomial coefficients and all finite zero-set
claims are checked by `direct_reflection_contact_exact.py`.

The common-zero permutation vertices of these six generators are exactly
the nine derangements relative to
\(\pi_0=(12)(34)\). Therefore (2) forces \(g\) to vanish on those nine
vertices. The derangement-face classification from the nonlinear spectral
geometry applies and gives

\[
\boxed{g(U)=\sum_iw_i|U_{i,\pi_0(i)}|^2,
\quad w_i\ge0,\quad\#\{i:w_i>0\}\le2.}
\tag{12}
\]

In this branch the conclusion is stronger than (1): the support is bounded
on all of \(U(4)\). Every entry in (12) vanishes at \(R\), so the full
gradient at \(R\), and consequently \(\ell\), is zero.

## 9. The balanced family: the two mixed covectors vanish directly

It remains to handle \(a=0\), \(bc\ne0\). The same exact polynomial
calculation shows that the only zero mixed facets are still catalog
facets 4 and 17: each other mixed slack has a positive monomial not
involving \(a\). Additional basic minor zeros can occur, but their
differentials are zero as noted in Section 2.

For completeness the two mixed covectors can be computed throughout
the entire real family. A normalized negative-eigenspace frame has
Pluecker coordinates

\[
p_{12}=\frac{1-a}{2},\quad p_{13}=\frac c2,\quad
p_{14}=-\frac b2,\quad p_{23}=\frac b2,\quad
p_{24}=\frac c2,\quad p_{34}=\frac{1+a}{2}.
\tag{13}
\]

On a real frame, for
\(T=\left(\begin{smallmatrix}s&x+iy\\x-iy&t\end{smallmatrix}\right)\),
one has \(C_{ijk}(T)=-p_{ij}p_{ik}p_{jk}y\). The two zero mixed facets
have opposite triple-orientation coefficient vectors
\((1,-1,1,-1)\). Substituting (13) gives their covectors, in the convention
\(F=-f\), as

\[
\boxed{\ell_4(T)=2abc\,y,\qquad\ell_{17}(T)=-2abc\,y.}
\tag{14}
\]

Both vanish at \(a=0\). Hence every active zero-gap summand has zero
covector in this final branch, even for an arbitrary common-minor cost.

## 10. Finish the theorem and delimit its scope

The cases exhaust every possible active mixed facet in (2), so
\(\ell=0\). At the maximizing commuting base the exact Cayley identity is

\[
\bigl(h-F(I+Y(V(T)-I)Y^*)\bigr)\det(I+T^2)
 =4\mathcal A(T)-2\det(T)\ell(T)+g(R)\det(T)^2,
\]

with

\[
\mathcal A(T)=\sum_{i<j}\delta_{ij}|y_iTy_j^*|^2\ge0.
\]

Under the zero-gap hypothesis the last two terms vanish. The denominator
is strictly positive, giving (1) on the Cayley chart, and continuity
includes the entire \(U(2)\) orbit.

The proof in fact applies to any nonnegative common-minor cost whose
centered cost lies in the projected spectral secant closure, because that
is sufficient for the only nonlinear step, Section 8. It does not apply to
arbitrary common-minor costs: the spectral face restriction used in Section 8 is an essential hypothesis.

The remaining positive-gap obligation is unchanged:

\[
g(R)\ge\tfrac14\ell^T\mathcal A^+\ell.
\]

We have now established its zero-gap compatibility at **every** order-four
rank-two reflection, rather than at one selected reflection. No universal
quantitative rate or positive-gap inequality is inferred from that fact.

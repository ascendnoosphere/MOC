## 1. The problem and the support formulation

For \(a,b\in\mathbb C^n\), put \(D_a=\operatorname{diag}(a_i)\), \(D_b=\operatorname{diag}(b_i)\), and

\[
z_\pi=\prod_{i=1}^n(a_i+b_{\pi(i)}),\qquad
d(U)=\det(D_a+UD_bU^*),\qquad U\in U(n).
\]

The conjecture is

\[
d(U)\in\operatorname{conv}\{z_\pi:\pi\in S_n\}.
\tag{MOC}
\]

Every pair of normal matrices can be put in this form by the spectral theorem. Complex convex-hull membership is equivalent to the real support inequalities

\[
\boxed{\quad
\Re\{\eta d(U)\}\le h_\eta,\qquad
h_\eta=\max_{\pi\in S_n}\Re(\eta z_\pi),\quad \eta\in\mathbb C.
\quad}
\tag{1}
\]

The support direction \(\eta\) can be normalized to modulus one when nonzero. Allowing arbitrary \(\eta\) is convenient because common complex rescalings of all products are then harmless.

Two exact identities explain the approaches explored here. First, with \(C_{ij}=a_i+b_j\),

\[
d(U)=\frac{\det(C\circ U)}{\det U},
\qquad \operatorname{rank}C\le2.
\tag{2}
\]

Second, if \(a_I=\prod_{i\in I}a_i\) and similarly for \(b_J\),

\[
d(U)=\sum_{|I|=|J|}a_{I^c}b_J\,|\det U[I,J]|^2.
\tag{3}
\]

Thus an actual determinant support is a particular linear functional of the full squared-minor profile. Its coefficients are constrained by complex products. Replacing those coefficients by arbitrary real coefficients produces a stronger problem, and several such replacements are false.

The July 2026 publisher abstract of Mulero-Martínez still describes the general normal-matrix conjecture as open. An April 2026 Kovačec preprint also retains the unrestricted order-four problem. These are the current primary sources verified in this campaign, not a claim that every subsequent manuscript has been exhausted. See [source and attribution status](ATTRIBUTION_AND_SOURCE_STATUS.md).

## 2. A complete theorem for an entire complex two-plane action

Fix a complex isometry \(Y:\mathbb C^2\to\mathbb C^n\), so \(Y^*Y=I_2\), and a base unitary \(W\). Define

\[
G_Y(V)=I+Y(V-I_2)Y^*,\qquad V\in U(2).
\]

This permits every unitary action on the selected plane, including changes of its two phase axes. It is more general than varying two fixed phases.

### 2.1 Six real coordinates represent every minor simultaneously

For every equally sized \(I,J\), the determinant of the selected submatrix has the form

\[
\det((G_Y(V)W)[I,J])
=\alpha_{I,J}+\mathcal L_{I,J}(V)+\gamma_{I,J}\det V,
\tag{4}
\]

where \(\mathcal L\) is complex linear in the four entries of \(V\).

To prove this, write the submatrix as a fixed matrix plus \(L(V-I_2)R\). A determinant can use at most two columns of this update. Cauchy–Binet makes every quadratic update term a multiple of \(\det(V-I_2)\), and
\(\det(V-I_2)=\det V-\operatorname{tr}V+1\). No invertibility assumption on the selected submatrix is needed.

Write

\[
V=e^{it}\bigl(q_0I+i(q_1\sigma_x+q_2\sigma_y+q_3\sigma_z)\bigr),
\quad q\in S^3,\quad p=(\cos t,\sin t)\in S^1.
\]

Multiplying (4) by \(e^{-it}\) makes it linear in the six real variables \(z=(q,p)\). Hence each squared minor is a real quadratic form in \(z\). Equation (3) gives a real symmetric \(6\times6\) matrix \(L\) such that the actual support functional is

\[
F(V)=z^TLz,\qquad \|q\|^2=\|p\|^2=1.
\tag{5}
\]

The entire convex hull of profiles on this plane is an exact linear image of

\[
\mathcal K_Y=
\{X\succeq0:\operatorname{tr}X_{qq}=1,\ 
\operatorname{tr}X_{pp}=1\}.
\tag{6}
\]

Here is a direct proof of exactness. A pure point is \(X=zz^T\). Conversely, factor \(X=BB^T\). The symmetric matrix
\(B^T\operatorname{diag}(I_4,-I_2)B\) has trace zero. It has an orthonormal basis whose diagonal quadratic values are all zero: select a unit vector with value zero between positive and negative directions, restrict to its orthogonal complement, and repeat. Applying this basis to the columns of \(B\) decomposes \(X\) into at most six rank-one matrices with equal squared norms in the two blocks. Normalize each nonzero summand; the first trace equation makes the weights sum to one. Each normalized summand is an actual \(V\in U(2)\).

Consequently, with \(J_6=\operatorname{diag}(I_4,-I_2)\),

\[
\boxed{
F(V)\le h\text{ for all }V\in U(2)
\iff
\exists\lambda\in\mathbb R:
\frac h2 I_6-L+\lambda J_6\succeq0.
}
\tag{7}
\]

The multiplier is essential in general. This is an exact fixed-plane theorem in every ambient dimension, not an assertion that all such profiles have common permutation weights.

### 2.2 Stationarity reduces the criterion to five dimensions

Assume \(V=I_2\) is stationary for \(F\). For a Hermitian matrix

\[
T=\begin{pmatrix}s&x+iy\\x-iy&t\end{pmatrix},\qquad d=\det T,
\]

use the Cayley chart

\[
V(T)=(I+iT)(I-iT)^{-1},\qquad
D(T)=\det(I+T^2)=1+\operatorname{tr}(T^2)+d^2>0.
\]

Let \(F_0=F(I_2)\), let
\(H(T,T)=\left.\frac{d^2}{d\varepsilon^2}F(e^{i\varepsilon T})\right|_0\),
and let \(\Delta=F(-I_2)-F_0\). There is a unique real linear form \(\ell\) with

\[
\boxed{
F(V(T))-F_0
=\frac{2H(T,T)+2d\,\ell(T)+\Delta d^2}{D(T)}.
}
\tag{8}
\]

Indeed, the six homogeneous coordinates in (5) become linear combinations of
\((1,s,t,x,y,d)\). The constant term in \((F-F_0)D\) vanishes, and stationarity removes the ordinary linear terms. The quadratic part is \(2H\), since the Cayley parameter starts as \(e^{2iT}\). The cubic part must be \(2d\ell\). Sending an invertible \(T\) to infinity identifies the coefficient of \(d^2\) with the reflected endpoint difference \(\Delta\).

If \(H_4\) denotes the matrix of \(H\), the full criterion is

\[
\boxed{
F(V)\le F_0\ \forall V\in U(2)
\iff
\begin{pmatrix}2H_4&\ell\\\ell^T&\Delta\end{pmatrix}\preceq0.
}
\tag{9}
\]

The necessity is not a relaxation. The projective directions of \((T,\det T)\) are dense in \(\mathbb{RP}^4\). Given a Hermitian \(Q\) with \(\det Q\ne0\) and a nonzero real \(c\), take \(T=(c/\det Q)Q\). Then
\((T,\det T)=(c/\det Q)(Q,c)\). A positive direction of the five-dimensional quadratic form would therefore give an actual violating Cayley direction. Continuity covers the rest of \(U(2)\).

This theorem identifies what rank-one tests miss: all terms involving \(d\) disappear when \(\operatorname{rank}T=1\). A collection of rank-one nonascent tests cannot determine the cubic covector or the reflected endpoint.

Full proofs and endpoint derivative formulas are in [the complete plane geometry note](continuous_full_rank_two_geometry.md). The prescribed-height version, valid when the reference height is above \(F_0\), retains the one-multiplier \(6\times6\) criterion.

## 3. The actual spectral energy obligation

Now take the base \(W=I\), so \(D_a,D_b\) commute, and impose the important hypothesis

\[
h=\Re(\eta z_{\mathrm{id}})
=\max_\pi\Re(\eta z_\pi).
\tag{10}
\]

For this section, the chosen identity pairing itself must maximize the permutation support. Relabeling \(b\) to create a different maximizing pairing can destroy the rank-two relation to the given unitary. The hypothesis cannot be silently imposed on an arbitrary relative rank-two example.

Let \(y_i\) be the rows of \(Y\), and define

\[
\delta_{ij}=h-\Re(\eta z_{(ij)})\ge0,\qquad
L_{ij}(T)=y_iTy_j^*,
\]

\[
\mathcal A(T,T)=\sum_{i<j}\delta_{ij}|L_{ij}(T)|^2,\qquad
g=h-F(-I_2).
\tag{11}
\]

Direct determinant differentiation gives \(H=-2\mathcal A\). For \(W_i=y_i^*y_i\), define

\[
s_{ijk}=\Re\{\eta(z_{(ijk)}-z_{(ikj)})\},\qquad
C_{ijk}(T)=-\Im\operatorname{tr}(\operatorname{adj}W_i\,W_jTW_k).
\]

The cubic covector is

\[
\ell(T)=4\sum_{i<j<k}s_{ijk}C_{ijk}(T).
\tag{12}
\]

The rank-two spectral matrix \(C_{ij}=a_i+b_j\) has zero three-by-three minors. On three labels this gives

\[
z_{\mathrm{id}}-z_{(ij)}-z_{(ik)}-z_{(jk)}
 +z_{(ijk)}+z_{(ikj)}=0.
\tag{13}
\]

If \(p,q\) are the nonnegative deficits of the two oriented three-cycles, then

\[
p+q=\delta_{ij}+\delta_{ik}+\delta_{jk},\qquad
s_{ijk}=q-p.
\]

Thus \(|s_{ijk}|\le\delta_{ij}+\delta_{ik}+\delta_{jk}\).

Using the Plücker coordinates \(p_{ij}=\det[y_i;y_j]\), this identity produces edge flows \(a_{ij}\) such that

\[
\ell(T)=4\sum_{i<j}\delta_{ij}
\Re\{\overline{a_{ij}}L_{ij}(T)\}.
\tag{14}
\]

In particular, \(\ell\) annihilates \(\ker\mathcal A\), including zero-deficit degeneracies. Completing squares in (8) gives

\[
\begin{aligned}
(h-F(V(T)))D(T)
={}&4\sum_{i<j}\delta_{ij}
 |L_{ij}(T)-d a_{ij}|^2\\
&+\left(g-4\sum_{i<j}\delta_{ij}|a_{ij}|^2\right)d^2.
\end{aligned}
\tag{15}
\]

Among all flows satisfying (14), the least weighted energy is

\[
C_{\min}=\frac1{16}\ell^T\mathcal A^+\ell.
\]

The kernel condition is already proved. Therefore the exact remaining condition on this plane is

\[
\boxed{\qquad g\ge\frac14\ell^T\mathcal A^+\ell.\qquad}
\tag{16}
\]

This is a genuine reduction of the whole-plane question to one scalar budget. It is not a universal proof of the budget. Even a proof under (10) would leave arbitrary base pairings and a general reduction of unrestricted unitaries to controlled planes to be addressed.


### 3.3 A proved symmetric class in dimension four

Call a real cost on permutations *inversion even* if \(c_\pi=c_{\pi^{-1}}\). Here the cost must belong to the linear space spanned by permutation subset indicators; equivalently, it obeys the linear relations of the squared-minor representation. An actual spectral cost is in this space.

**Theorem.** In dimension four, if an inversion-even cost has its maximum at the identity permutation, its associated squared-minor functional is bounded by that maximum on every complex unitary matrix.

The proof uses the complete common-minor facet description. At the identity, twenty-six of the forty-eight nontrivial facets are active. For every active facet \(f\), the exact certificate gives an identity

\[
f(X)+f(X^T)=\sum_{I\ne J}k_{I,J}X_{I,J},
\qquad k_{I,J}\in\mathbb Z_{\ge0}.
\]

The identities hold on all twenty-four permutation vertices and therefore on their affine span, which contains every unitary squared-minor profile. All nonnegativity facets also hold. Consequently the symmetric part of any unitary profile lies in the tangent cone of the permutation polytope at the identity. A cost maximized there belongs to the polar cone. An inversion-even cost has the same value on a profile and its symmetric part, proving the theorem. In particular every Hermitian unitary profile lies in this tangent cone. Thus in dimension four the reflection gap \(g\) in (16) is always nonnegative; the unresolved issue is whether it is large enough to absorb the cubic energy. This theorem controls arbitrary inversion-even costs in the specified linear space; no spectral assumption is needed.

### 3.4 The exact correction at a nonmaximizing commuting base

Let \(f_0=F(I)<h\) and \(c=h-f_0>0\). Use the possibly signed base deficits
\(\delta^0_{ij}=f_0-\Re(\eta z_{(ij)})\), let
\(\mathcal A_0=\sum_{i<j}\delta^0_{ij}|y_iTy_j^*|^2\), and put
\(g_h=h-F(I-2P)\). In real Hermitian coordinates
\(T=\left(\begin{smallmatrix}s&x+iy\\x-iy&t\end{smallmatrix}\right)\),
let \(W_4,D_4\) represent the quadratic forms
\(\operatorname{tr}T^2\) and \(\det T\). The exact arbitrary-height criterion becomes
\[
\exists\lambda\in\mathbb R:\qquad
\begin{pmatrix}
c&0&\lambda/2\\
0&B_\lambda&-\ell\\
\lambda/2&-\ell^T&g_h
\end{pmatrix}\succeq0,\qquad
B_\lambda=cW_4+4\mathcal A_0-\lambda D_4.
\]
Equivalently,
\[
B_\lambda\succeq0,\qquad
\ell\in\operatorname{range}B_\lambda,\qquad
g_h-\frac{\lambda^2}{4c}\ge\ell^TB_\lambda^+\ell
\]
for some real \(\lambda\). This is an exact reformulation, including singular matrices, not a proof that such a \(\lambda\) always exists.

Replacing the signed base deficits by the nonnegative target-height deficits introduces a required extra term:
\[
B_\lambda(T,T)=4\mathcal A_h(T,T)
+c\left(2\sum_i(y_iTy_i^*)^2-\operatorname{tr}T^2\right)
-\lambda\det T.
\]
The diagonal-frame correction has no fixed sign. This is the precise obstruction to transferring the maximizing-base budget unchanged to an arbitrary commuting base.

## 4. The categorical and Clifford route becomes explicit invariant geometry

This part starts with a concrete map, not a change of terminology. Introduce spinors

\[
p_i=(a_i,1),\qquad p_{n+j}=(-b_j,1),
\]

and the alternating bracket \([u,v]=u_1v_2-u_2v_1\). Then

\[
a_i+b_j=[p_i,p_{n+j}],\qquad
z_\pi=\prod_i[p_i,p_{n+\pi(i)}].
\tag{20}
\]

All spectral products are thus matching invariants of \(2n\) points on the projective line. Plücker straightening expresses every perfect matching as a linear combination of bipartite matchings: replace a pair internal to the first \(n\) labels and a pair internal to the last \(n\) labels by cross-pairings. The invariant span has Catalan dimension

\[
\mathrm{Cat}_n=\frac1{n+1}\binom{2n}{n}.
\]

The spectral variety is the affine cone over
\(M_{2n}=(\mathbb P^1)^{2n}//SL_2\), with complex dimension \(2n-2\) for \(n\ge2\). Real parts have dimension at most \(4n-4\). This explains why arbitrary minor coefficients become a much larger class than actual spectral costs.

For \(n=4\), the ambient invariant space has dimension fourteen. Howard–Millson–Snowden–Vakil established the eight-point variety's skew cubic and its singular-locus and secant geometry. Those established results are the external input here. The campaign constructed the map explicitly in MOC permutation coordinates and then analyzed its real cost projection.

### 4.1 An explicit cubic and the physical real form

Choose fourteen independent permutation products as coordinates \(x\in\mathbb C^{14}\). Every one of the 105 perfect matchings becomes an integer linear form \(m_M(x)\). In the chosen normalization,

\[
\mathscr F(x)=\frac16\sum_M\operatorname{PfSign}(M)\,m_M(x)^3
\tag{21}
\]

has only forty-nine nonzero monomials. Its fourteen quadratic derivatives vanish identically on every actual spectral configuration; the exact coordinate certificate expands and verifies these identities.

The vanishing itself has a useful geometric interpretation. The matrix of cubed brackets has rank at most four, because the cubed bracket is the alternating form on \(\operatorname{Sym}^3(\mathbb C^2)\). Its eight-by-eight Pfaffian is therefore zero. The singular-locus theorem identifies the full eight-point cone as
\(\nabla\mathscr F=0\).

Write a complex spectral point as \(z=c+id\), with \(c,d\in\mathbb R^{14}\). Since \(\mathscr F\) is a real cubic,

\[
\nabla\mathscr F(c+id)
=\nabla\mathscr F(c)-\nabla\mathscr F(d)
 +i\,H_{\mathscr F}(c)d.
\]

Thus the real support-cost condition is

\[
\boxed{
H_{\mathscr F}(c)d=0,\qquad
\nabla\mathscr F(d)=\nabla\mathscr F(c)
}
\tag{22}
\]

for an appropriate real \(d\). This keeps the conjugate-pair structure of an actual complex point.

A sum of two real invariant-cone points has the opposite sign in the second equation. Exact rational examples show conjugate-only, real-real-only, and overlapping representations. The real secant locus itself also contains conjugate points. Therefore the real zero set of an eliminated polynomial does not by itself characterize the physical real branch.

The associated Clifford picture is also concrete: a spinor \(p\) gives the rank-one positive Hermitian matrix \(pp^*\), a future null vector for the determinant quadratic form of signature \((1,3)\). A conjugate-pair representation uses such Hermitian rank-one tensors. This observation motivates retaining the real form; it is not a positivity theorem for MOC.

### 4.2 Removing constants produces a degree-nine condition

Let \(e=(1,\ldots,1)\). It is itself an eight-point invariant vector: four coincident points in one family and four in the other give all bipartite products equal to one. The exact calculation gives

\[
D_e\mathscr F=\det B,
\tag{23}
\]

where \(B\) is the natural two-by-two singlet block. In coordinates consisting of a constant \(t\), nine other coordinates \(a\), and four entries of \(B\),

\[
\mathscr F=t\det B+\mathscr C(a,B).
\tag{24}
\]

This matters because adding a constant to every permutation cost does not change a support inequality.

Put \(Q=\det B\). The Hessian determinant is cubic in \(t\), with coefficients \(h_0,h_1,h_2,h_3\), and
\(h_3=-2Q\det K\), where \(K\) is the nine-by-nine \(a\)-block of the Hessian. Eliminating the unique cubic height when \(Q\ne0\) yields

\[
N=Q^2h_0-\mathscr CQh_1+\mathscr C^2h_2
 +2\mathscr C^3\det K.
\tag{25}
\]

This is homogeneous of degree eighteen. The established Hessian/secant multiplicity theorem, together with an exact witness showing that \(Q\) is not an extra factor, makes \(N\) a nonzero constant times the square of an irreducible degree-nine polynomial.

Consequently the centered actual complex spectral cost directions are Zariski dense in a degree-nine hypersurface in the thirteen-dimensional cost quotient. No nonzero polynomial of degree below nine vanishes on the entire cost image. This strengthens the earlier exact evaluation result that had excluded equations only through degree three.

These statements concern polynomial equations solely in the thirteen cost coordinates. They do not rule out lower-degree inequalities or a proof using additional variables. Selecting the correct real branch still requires information such as (22).

### 4.3 A troublesome facet normal is not a spectral cost

For a unitary matrix of order four, set

\[
f(U)=|U_{33}|^2+|U_{24}|^2
 +|\det U[12,13]|^2-|\det U[13,23]|^2.
\tag{26}
\]

It is nonnegative on every permutation matrix, yet it is negative at some actual unitaries. Let \(f\in\mathbb R^{14}\) denote its values on the chosen fourteen basis permutations. Exact invariant arithmetic gives

\[
\mathscr F(f)=-1,\qquad D_e\mathscr F(f)=-1.
\]

Thus the only constant shift of this cost lying on the cubic is \(f-e\). Its Hessian determinant is

\[
\det H_{\mathscr F}(f-e)=-4\ne0.
\tag{27}
\]

Every secant point of the singular locus lies on the cubic and has singular Hessian. For a conjugate spectral point this also follows directly from (22); a zero imaginary direction would require the gradient to vanish and still make the Hessian singular by Euler's identity. Equation (27) therefore excludes this facet normal, modulo constants and nonzero scaling, from actual spectral costs and from the entire projected secant.

The exclusion is quantitative. In the thirteen selected permutation-cost differences, a closed infinity-norm ball of radius \(1/100\) around the centered facet direction is disjoint from that secant. The proof is an exact Neumann-series estimate for the Hessian, not an unsuccessful numerical fit.

This is why a negative common-minor facet is not automatically a complex MOC counterexample. It also does not finish MOC: other spectral directions can combine several facet directions, and a support inequality must control those combinations.


### 4.5 Spectral rigidity proves a boundary face completely

There is a concrete place where the nonlinear spectral equations do prove the support inequality. Suppose, in dimension four, that all nine derangements attain the permutation support maximum \(h\). Put

\[
g_\pi=h-c_\pi\ge0.
\]

Thus \(g_\pi=0\) on the nine derangements. The linear spectral relations leave a five-dimensional space of possible deficits. In exact coordinates \((a,b,c,d,e)\) on that space, the invariant cubic and its constant derivative become

\[
\mathscr F(g)
=c\{(a-b)(b+e)+bd\}-ade,\qquad
Q(g)=(d-e)^2.
\tag{B1}
\]

Here \(\mathscr F\) is the invariant cubic, while \(F(U)\) denotes a support functional. A symbolic polynomial determinant calculation gives

\[
\det H_{\mathscr F}(g+t\mathbf1)
=4t^3(d-e)^2\mathscr F(g)^3.
\tag{B2}
\]

Substituting the cubic lift into the Hessian-square identity gives
\(N=-4\mathscr F(g)^6\) whenever \(Q\ne0\), hence everywhere on the five-space by polynomial continuation. Therefore the projected nonic restricts to
\[
P_9(g)=\pm\mathscr F(g)^3.
\]
Every point in the Zariski-closed projected secant on this face must consequently satisfy \(\mathscr F(g)=0\).

Nonnegativity of all twenty-four deficits has a further exact consequence:

\[
\mathscr F(g)\ge |d-e|^3.
\tag{B3}
\]

For example, in the chamber \(d-e=k\ge0\), write
\[
(a,b,c,d,e)=(A+B+k,\ B+k,\ E+k+C,\ E+k,\ E),
\]
where \(A,B,C,E,k\ge0\). Direct factorization gives
\[
\mathscr F(g)=(E+k)(B+k)(A+k)
+C\{A(B+E+k)+(B+k)(E+k)\}\ge k^3.
\]
In the opposite chamber \(e-d=k\ge0\), use
\((a,b,c,d,e)=(A+B+k,B,E+k+C,E,E+k)\), which gives
\[
\mathscr F(g)=(E+k)(A+k)(B+k)
+C\{(A+k)(B+E+k)+BE\}\ge k^3.
\]

An actual spectral cost, after its constant shift and sign change, lies in the projected secant. Thus \(\mathscr F(g)=0\), and (B3) forces \(d=e\).

On this hyperplane, all deficits have the form

\[
g_\pi=\sum_{i=1}^4w_i\mathbf1_{\{\pi(i)=i\}},
\qquad
w=(b,a-b,c-d,d)\ge0,
\]

and \(\mathscr F(g)=e_3(w_1,w_2,w_3,w_4)=0\). Nonnegativity forces at most two weights to be nonzero. Hence

\[
\boxed{h-F(U)=\sum_{i=1}^4w_i|U_{ii}|^2\ge0.}
\tag{B4}
\]

This proves scalar MOC on the entire nine-derangement maximizing face. It is an exact classification of the projected spectral costs on that face. A converse rank-two product construction realizes arbitrary two nonnegative diagonal weights; the finite-chart lemma converts it to finite complex spectra. The proof works for the Zariski closure of the larger projected complex secant, so neither a closure issue nor the distinction between its real branches causes a gap here.

This theorem also proves a zero-gap contact result at the real rank-two reflection
\[
R=\frac13\begin{pmatrix}
1&-2&0&2\\-2&-1&2&0\\0&2&1&2\\2&0&2&-1
\end{pmatrix}.
\]
If an actual spectral cost has \(h=F(I)=F(R)=\max_\pi F(P_\pi)\), then
\[
h-F(U)=\sum_iw_i|U_{i,\pi_0(i)}|^2\ge0,\qquad
\pi_0=(13)(24),
\]
with at most two nonnegative weights. The proof is exact: among facets active at identity, only two mixed facets and the four entries \(13,24,31,42\) have zero slack at \(R\). Their common-zero vertices are precisely the nine derangements relative to \(\pi_0\). A nonnegative facet decomposition of a zero-gap cost uses only these generators, so the preceding classification applies after column relabeling. In particular its cubic covector vanishes. See [ZERO_GAP_REFLECTION_RIGIDITY.md](ZERO_GAP_REFLECTION_RIGIDITY.md).

The independent review strengthens this exact face result to a quantitative stability theorem. Let \(\mathcal S\) be the union of the six cones of deficits with at most two nonnegative diagonal assignment weights. For any nonnegative deficit in the squared-minor linear space satisfying \(P_9(g)=0\), put
\[
M=\max_\pi g_\pi,\qquad
\delta=\max_{\pi\text{ a derangement}}g_\pi.
\]
There is a fixed, rigorously specified finite constant \(C_*\), independent of the deficit, such that
\[
\boxed{\operatorname{dist}_\infty(g,\mathcal S)
\le C_*M^{8/9}\delta^{1/9},\qquad
g(U)\ge-24C_*M^{8/9}\delta^{1/9}.}
\tag{B4a}
\]
The zero vector is included. The proof first projects onto the derangement-zero five-space and corrects its negative coordinates with the fixed-point-count vector. The identity \(P_9=\pm\mathscr F^3\), followed by \(\mathscr F\ge|d-e|^3\) and the nonnegative elementary-symmetric-polynomial bound, gives the exponent \(1/9\). The final estimate uses the exact signed determinant expansion of every unitary profile and its uniform coefficient bound. No regularity assumption at a singular point is needed. A numerical value or optimality of \(C_*\) or of the exponent is not asserted.

For the displayed reflection, every deficit with \(g_{\mathrm{id}}=0\) also satisfies the exact facetwise estimate
\[
\max_{\pi(i)\ne\pi_0(i)\ \forall i}g_\pi
\le\frac{81}{4}g(R).
\tag{B4b}
\]
Thus (B4a) gives uniform approximate support control in terms of a small reflection gap, after column relabeling. It does not give the rate required to prove the exact energy budget (16) for positive gaps. The full argument and constant are in [review_derangement_stability.md](review_derangement_stability.md).

### 4.6 A one-parameter family exposes the remaining interior

Let
\[
J=\begin{pmatrix}
0&-1&-1&-1\\1&0&-1&1\\1&1&0&-1\\1&-1&1&0
\end{pmatrix},
\quad J^2=-3I,\qquad
U(t)=\frac{tI+J}{\sqrt{t^2+3}}.
\]

For any real cost in the squared-minor linear space, put \(g=h-c\ge0\), let \(A=g_{\mathrm{id}}\), let \(T\) be the sum of the six transposition deficits, let \(D\) be the sum of the nine derangement deficits, and let \(K\) be the signed sum of the eight three-cycle costs from this matrix. Direct determinant expansion gives

\[
(h-F(U(t)))(t^2+3)^2=At^4+Tt^2-Kt+D.
\tag{B5}
\]

For \(A>0,D>0\), the quartic is nonnegative for every real \(t\) if and only if
\[
\boxed{K^2\le4z(T+2Az)^2,\qquad
z=\frac{\sqrt{T^2+12AD}-T}{6A}.}
\]
Indeed, minimizing \(Ar^3+Tr+D/r\) over \(r>0\) gives
\(3Az^2+Tz=D\) and the minimum \(2\sqrt z(T+2Az)\). At equality the quartic is
\[
A(t^2-z)^2+(T+2Az)(t-\operatorname{sgn}(K)\sqrt z)^2.
\]
Intermediate \(K\)'s are convex combinations of the two signs. When \(D=0\), positivity requires \(K=0\); when \(A=0\), the usual quadratic criterion applies, including its degenerate limits. Thus the remaining question is a concrete spectral coefficient inequality, not an unknown univariate minimization.

The four triangle identities and the alternating determinant identity imply

\[
T\ge2A,\qquad |K|\le2T-4A,\qquad
D=T-3A+2E,
\tag{B6}
\]

where \(E\ge0\) is the sum of the three double-transposition deficits. If the identity is maximizing, then \(A=0\), \(D\ge T\), and \(K^2\le4TD\). Thus the quadratic in (B5) is nonnegative for every real \(t\). This conclusion needs only the linear relations.

More generally, write \(T=2A+B\), \(B\ge0\). Equations (B6) give the explicit lower bound

\[
At^4+Tt^2-Kt+D
\ge A(t^4+2t^2-1)+B(|t|-1)^2.
\]

Every such cost is therefore safe for
\[
|t|\ge\sqrt{\sqrt2-1}.
\]

There is a sharper exact geometric threshold. Restricting all forty-eight mixed common-minor facets to this family leaves the following numerator types, with the common positive denominator \((t^2+3)^2\):

| Numerator type | Multiplicity |
| --- | ---: |
| \(2t^4+6t^2+4t\), \(2t^4+6t^2-4t\) | 1 each |
| \(3+3t^2+2t\), \(3+3t^2-2t\) | 4 each |
| \(3+4t^2+t^4\) | 12 |
| \(6+2t^2+4t\), \(6+2t^2-4t\) | 3 each |
| \(6+3t^2+t^4+2t\), \(6+3t^2+t^4-2t\) | 4 each |
| \(6+2t^2\) | 12 |

The last forty-six are strictly positive. The first pair is nonnegative exactly when
\[
\boxed{t=0\quad\text{or}\quad |t|\ge\rho,\qquad
\rho^3+3\rho-2=0,\quad \rho>0.}
\tag{B7}
\]
All other facets are squared-minor nonnegativity. The complete facet theorem therefore proves that (B7) is exactly the common-permutation-law region of this family. Independently, a six-class quotient by the alternating group gives the same characterization without using the full facet catalog.

The possible scalar spectral difficulty is confined to
\(0<|t|<\rho\), with \(A>0\) and \(D<T\). The preceding spectral rigidity theorem settles its boundary \(D=0\); it does not establish the inequality throughout that remaining region. This is a precise example of starting from controlled ends and identifying the missing interior estimate.

### 4.7 Higher-dimensional Pfaffian relations and a Lorentz inequality

For \(2n\) spinors and an odd integer \(p\), let \(\ell_M\) be the matching linear forms and define

\[
P_{n,p}(x)=\sum_M\epsilon(M)\ell_M(x)^p.
\]

Its polarization is the Pfaffian of the alternating Gram matrix of product tensors in \((\mathbb C^2)^{\otimes p}\). It is a nonzero spectral relation whenever

\[
p+1<2n\le2^p.
\]

Indeed, on a single spinor configuration the relevant space is
\(\operatorname{Sym}^p\mathbb C^2\), of dimension \(p+1\), so the Pfaffian vanishes. On independent polarized configurations, \(2n\) suitably paired binary basis tensors give a nonzero Pfaffian whenever \(2n\le2^p\). More generally, for \(0\le k\le p\), the \(k\)-th derivative vanishes on the spectral variety if
\((p-k+1)2^k<2n\). This explains the eight-label cubic and supplies explicit higher-dimensional algebra; it supplies no automatic positive induction.

The Lorentz model also retains useful order. For spinors \(p_i\), put
\(G_{ij}=|[p_i,p_j]|^2\), \(t_i=\|p_i\|^2\), and let \(S\) contain their three spatial Lorentz coordinates. Then
\[
G=\tfrac12(tt^T-SS^T).
\]
For every entrywise nonnegative positive semidefinite matrix \(W\),
\[
0\le\langle W,G\rangle\le\tfrac12t^TWt.
\]
The two inequalities follow respectively from entrywise positivity and
\(\operatorname{tr}(S^TWS)\ge0\). This is compatible with one block of the exact dual moment relaxation. Controlling the full signed spectral objective by this budget remains unproved.

## 5. A sharp geometric bound for the stronger common-minor problem

The common-minor permutation polytope in order four has affine dimension thirteen. The complete facet description in this record has sixteen singleton nonnegativity facets, eighteen complementary two-minor facets, and forty-eight relabelings of (26). Its completeness was checked by an exact oriented boundary-chain argument, including all nonzero and degenerate simplex determinants.

For every complex \(U\in U(4)\),

\[
\boxed{
f(U)\ge-\delta,\qquad
\delta=\frac{t(1-t^2)}4,\quad
t^3+t^2+3t-1=0,\quad 0<t<1.
}
\tag{29}
\]

Numerically, \(\delta=0.067442248868\ldots\), and the bound is attained. A September 2026 research-report abstract records an overlapping sharp orthogonal result, so no priority claim is made for the real bound; see the attribution note. The proof below and its extension to complex profiles were independently checked in this campaign.

### 5.1 Quaternion angle elimination

Write a real special orthogonal matrix as \(O=L(q)R(r)\), with unit real quaternions \(q,r\). Expansion of (26) gives

\[
\begin{aligned}
f={}&(q_0^2-q_2^2)(q_3^2-q_1^2)
 +(r_0^2-r_2^2)(r_3^2-r_1^2)\\
&+(q_0r_0-q_2r_2)^2+(q_0r_2-q_2r_0)^2\\
&+(q_1r_1+q_3r_3)^2+(q_1r_3+q_3r_1)^2.
\end{aligned}
\tag{30}
\]

Set \(X=q_0^2+q_2^2\), \(U=r_0^2+r_2^2\). The four doubled-angle pairs vary independently over circles with radii \(X,1-X,U,1-U\). Minimizing over two circles and then allocating the remaining squared radii by Cauchy's inequality gives the exact, attained angular minimum

\[
m(X,U)=XU+(1-X)(1-U)
-\sqrt{(X^2+(1-U)^2)((1-X)^2+U^2)}.
\tag{31}
\]

No generic-angle assumption is used. Zero-radius cases follow in the same formula.

Under \(p=X+U-1\), \(d=X-U\), the square becomes the diamond \(|p|+|d|\le1\). Along a ray the value in (31), as a function of the squared radius, is concave and starts with derivative zero. It therefore reaches its minimum on the boundary. The entire minimization reduces to

\[
\delta=\max_{0\le y\le1}(1-y)(\sqrt{1+y^2}-1).
\]

Its unique interior maximizer satisfies
\(2y^3-2y^2+2y-1=0\). Substitution \(t=2y-1\) gives (29). An attainer is

\[
O(t)=\frac1{\sqrt{t^2+3}}
\begin{pmatrix}
t&1&1&-1\\
-1&1&-1&-t\\
-1&-1&t&-1\\
-1&t&1&1
\end{pmatrix}.
\tag{32}
\]

### 5.2 Why the bound extends to complex unitaries

Make one row of \(U\) real by column phases. On its three-dimensional real orthogonal complement, the other rows define three real positive semidefinite effects of trace one whose sum is the identity. Every anchored singleton and wedge coordinate is linear in those effects.

Every such effect triple is a convex mixture of orthogonal rank-one frames. At an extreme triple, if all three ranks were at least two, the supported symmetric perturbations would have at least nine dimensions; the trace and sum constraints impose at most eight independent conditions. A nonzero two-sided perturbation would contradict extremality. Thus one effect is rank one, hence a projection. The remaining two commute on its two-dimensional complement and decompose into the two ordered orthogonal frames.

Averaging the resulting real orthogonal profiles recovers the complex profile. Applying the real bound to every term proves (29) for all complex \(U(4)\).

This purification theorem is specific to the three-dimensional complement; no higher-dimensional extension is asserted.




### 7.1 Exact phase completion and the remaining chamber problem

For \(O=L(q)R(r)\), one chart's rank-two phase-completion discriminant factors as

\[
\Delta=-16\prod_{i=0}^3(q_i^2-r_i^2).
\tag{35}
\]

After the twenty-four permutation charts,

\[
\exists\text{ monomial unitary }M:\operatorname{rank}(O-M)\le2
\iff
\max_\pi\Delta_\pi(O)\ge0.
\tag{36}
\]

The proof includes singular cross blocks and zero-discriminant cases by direct rank conditions and a compactness argument. The spin charts form an arrangement of 192 distinct hyperplanes. The campaign identified several inequivalent chambers, so one convenient chamber cannot be taken to represent them all.

In the first chamber, forty-four inequalities have direct nonnegative coefficient expansions. An exact rational Gram certificate and symmetry prove two more. The independent review strengthens one of these to a quantitative bound with an explicit equality locus. Two inequalities remain open in that chamber, and the full chamber classification is not complete.

See [global phase completion](categorical_global_completion_criterion.md) and [spin chambers](categorical_spin_chambers.md).


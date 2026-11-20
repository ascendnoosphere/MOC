# Spectral rigidity on the nine-derangement maximizing face

## Statement and scope

Let \(\mathcal V\subset\mathbb R^{S_4}\) be the fourteen-dimensional space spanned by the matching-product functions
\[
\pi\longmapsto\prod_{i=1}^4 C_{i,\pi(i)},\qquad \operatorname{rank}_{\mathbb C}C\le2,
\]
taking real and imaginary parts when necessary. Equivalently, this is the real Temperley--Lieb cost space of order four. Let \(e\) denote the constant function \(1\), and let \(X\subset\mathcal V_{\mathbb C}\) be the affine cone of rank-two matching products.

A real cost of the Marcus--de Oliveira problem belongs to the real part of \(X\): with finite normal spectra \(a,b\) and a complex support direction \(\lambda\),
\[
c_\pi=\operatorname{Re}\!\left(\lambda\prod_i(a_i+b_{\pi(i)})\right).
\tag{1}
\]
Absorb \(\lambda\) into one row of the rank-two matrix \(C_{ij}=a_i+b_j\). Then \(c=(z+\bar z)/2\) for \(z\in X\). In particular, \(c\) lies in the complex secant cone. A sum of two real rank-two matching-product costs also lies in that cone. These two real classes are different; neither contains the other in general.

**Theorem.** Suppose \(c\in\mathcal V\), \(h=\max_\pi c_\pi\), and all nine derangements satisfy \(c_\pi=h\). Assume that the class of \(c\) modulo constants admits a complex secant lift. Then there are nonnegative weights \(w_1,\ldots,w_4\), at most two of them nonzero, such that
\[
c_\pi=h-\sum_{i=1}^4w_i\,1_{\{\pi(i)=i\}}.
\tag{2}
\]
Conversely, every deficit on the right with at most two nonzero weights has both a real-secant representative and a finite complex normal-spectral representative modulo constants.

For the corresponding actual unitary support functional, the conclusion is
\[
c(U)=h-\sum_{i=1}^4w_i|U_{ii}|^2\le h
\qquad\text{for every }U\in U(4).
\tag{3}
\]
Thus MOC holds for every spectral support direction satisfying this simultaneous nine-derangement contact hypothesis.

The independent reviewer additionally proved that the same classification holds for the full Zariski closure of the projected complex secant cone. Section 7 gives that extension. The finite-lift proof in Sections 1--6 suffices for every actual spectral cost and does not require a sufficiency theorem for the global secant equations.

This is a sufficient-face theorem. It does not prove that arbitrary spectral support directions have nine maximizing derangements, and it does not solve unrestricted complex MOC.

## 1. Exact cubic coordinates and the secant obstruction

Choose the fourteen permutation coordinates in code/theorems/finite_and_spin_geometry/categorical_m8_coordinates.py. Every other permutation value is an exact integer linear combination of these. Write \(F\) for the normalized forty-nine-term cubic constructed there from the signed sum of the cubes of all 105 perfect-matching coordinates:
\[
F=\frac16\sum_M\operatorname{sgn}(M)\,m_M^3.
\tag{4}
\]
The script verifies by polynomial composition that every first derivative of \(F\) vanishes on \(X\). This is an exact identity in the sixteen entries of eight two-component spinors, not a sample-based check. It also verifies
\[
F(e)=0,\qquad \nabla F(e)=0.
\]
Consequently, with \(Q=D_eF\),
\[
F(g+s e)=F(g)+sQ(g).
\tag{5}
\]

Here are the two necessary equations used below:
\[
z\in\overline{X+X}\quad\Longrightarrow\quad
F(z)=0,\qquad \det H_F(z)=0.
\tag{6}
\]
They follow directly from the gradient identities. A cubic singular at \(x,y\) vanishes identically on the line joining \(x\) and \(y\), so \(F(x+y)=0\). Since a cubic Hessian is linear and its associated trilinear form is symmetric,
\[
H_F(x+y)(x-y)=0.
\]
If \(x=y\ne0\), use \(H_F(x)x=2\nabla F(x)=0\); the zero vector causes no difficulty. Polynomial continuity extends both identities to the affine closure.

For an actual cost \(c\), put \(g=he-c\). Then \(g-he=-c\) is a complex secant. Hence an actual cost automatically supplies a finite constant lift satisfying (6). This explains why the height shift must be included.

## 2. The complete derangement-zero linear space

Let \(g_\pi\ge0\) be a cost in \(\mathcal V\) vanishing on all nine derangements. The nine restrictions have rank nine in the fourteen-dimensional space, so the remaining space has dimension five. The following table parametrizes it completely. Permutations are written as the images of \(1,2,3,4\); omitted rows are precisely the nine derangements and have value zero.

| Permutation | Deficit |
|---|---:|
| \(1234\) | \(a+c\) |
| \(1243\) | \(a\) |
| \(1324\) | \(b+e\) |
| \(1342\) | \(b-d+e\) |
| \(1423\) | \(b\) |
| \(1432\) | \(b+c-d\) |
| \(2134\) | \(c\) |
| \(2314\) | \(d\) |
| \(2431\) | \(c-d\) |
| \(3124\) | \(e\) |
| \(3214\) | \(a-b+d\) |
| \(3241\) | \(a-b+d-e\) |
| \(4132\) | \(c-e\) |
| \(4213\) | \(a-b\) |
| \(4231\) | \(a-b+c-e\) |

Nonnegativity of all twenty-four values is equivalent to
\[
\begin{gathered}
b,d,e\ge0,\qquad a-b\ge0,\qquad c-d\ge0,\qquad c-e\ge0,\\
b-d+e\ge0,\qquad a-b+d-e\ge0.
\end{gathered}
\tag{7}
\]
For example, the last listed value is \((a-b)+(c-e)\), and the other omitted inequalities follow just as directly. The exact basis vectors and all twenty-four forms are checked by code/theorems/finite_and_spin_geometry/dual_derangement_secant_rigidity_exact.py.

On this space, the cubic and its constant-direction derivative simplify to
\[
Q(g)=(d-e)^2,
\tag{8}
\]
\[
\begin{aligned}
F(g)
&=c\bigl[(a-b)(b+e)+bd\bigr]-ade\\
&=(a-b)\bigl[bc+e(c-d)\bigr]+bd(c-e).
\end{aligned}
\tag{9}
\]
These are full polynomial identities in five free variables.

## 3. The exact Hessian factorization

On the same space, for every complex \(s\),
\[
\boxed{\det H_F(g+s e)=4s^3(d-e)^2F(g)^3.}
\tag{10}
\]

The proof is a finite polynomial calculation whose structural components are as follows.

First, every matrix in the five-dimensional linear pencil \(H_F(g)\) has the following three common kernel vectors, in the fourteen-coordinate basis:
\[
\begin{aligned}
&(1,0,1,0,0,0,0,0,0,0,0,0,0,0),\\
&(1,1,0,0,0,1,1,0,0,0,0,0,0,0),\\
&(1,0,0,0,0,0,0,0,0,0,0,0,1,0).
\end{aligned}
\tag{11}
\]
Therefore the determinant of \(H_F(g+s e)\) is divisible by \(s^3\).

Second, code/theorems/finite_and_spin_geometry/categorical_m8_projection.py gives an invertible coordinate change \(x=Ty\), with determinant \(-1\), in which
\[
y=(t,A_1,\ldots,A_9,B_{11},B_{12},B_{21},B_{22}),\qquad
F(Ty)=t\det B+C(A,B).
\tag{12}
\]
Changing \(g\) to \(g+s e\) changes only \(t\). In these coordinates the Hessian has block form
\[
\begin{pmatrix}
0&0&b^T\\
0&K&L\\
b&L^T&sH_Q+M
\end{pmatrix},
\qquad b=H_QB.
\tag{13}
\]
Here \(K\) is \(9\times9\), \(H_Q\) is the Hessian of the \(2\times2\) determinant, and \(\det H_Q=1\). The determinant has degree at most three in \(s\): a degree-four term would select all four entries from the bottom-right block and leave the height row unpaired. Its degree-three coefficient is
\[
-\det K\,b^T\operatorname{adj}(H_Q)b=-2Q(g)\det K.
\tag{14}
\]
The exact five-variable identity
\[
\det K=-2F(g)^3
\tag{15}
\]
then proves (10).

The verifier expands the sparse \(9\times9\) polynomial determinant using rational arithmetic and compares every coefficient with \(-2F^3\). It verifies the common kernel and the entire height-dependent part of (12). Thus (10) is established symbolically; the extra full-Hessian evaluations included in the script only check the normalization and congruence sign.

## 4. A quantitative positivity bound from the permutation gaps

The nonnegative cone (7) forces
\[
\boxed{F(g)\ge |d-e|^3.}
\tag{16}
\]
Here is a direct two-chamber proof.

If \(d-e=k\ge0\), write
\[
a=A+B+k,\quad b=B+k,\quad c=E+k+C,\quad d=E+k,\quad e=E,
\]
where \(A,B,C,E,k\ge0\). The inequalities (7) give exactly these nonnegativities. Substitution into (9) yields a polynomial whose coefficients are all nonnegative and whose \(k^3\) coefficient is one.

More explicitly, in this chamber,
\[
F=(E+k)(B+k)(A+k)
+C\bigl[A(B+E+k)+(B+k)(E+k)\bigr]\ge k^3.
\]

If \(e-d=k\ge0\), write
\[
a=A+B+k,\quad b=B,\quad c=E+k+C,\quad d=E,\quad e=E+k.
\]
Again all five new variables are nonnegative by (7), and the resulting polynomial is \(k^3\) plus terms with nonnegative coefficients. Both expansions are checked by the exact verifier.

Here the corresponding factorization is
\[
F=(E+k)(A+k)(B+k)
+C\bigl[(A+k)(B+E+k)+BE\bigr]\ge k^3.
\]

Suppose \(d\ne e\). Then \(Q>0\), \(F>0\), and the only constant lift lying on the cubic is \(s=-F/Q\). At this lift, (10) gives
\[
\det H_F(g-FQ^{-1}e)
=-\,\frac{4F(g)^6}{Q(g)^2}\ne0.
\tag{17}
\]
This contradicts the necessary secant equation (6). Therefore every nonnegative deficit on this face that admits a secant lift must satisfy
\[
d=e.
\tag{18}
\]

This is the decisive spectral restriction. Generic nonnegative Temperley--Lieb costs on the same face need not satisfy it.

## 5. Classification on the surviving hyperplane

When \(d=e\), put
\[
(w_1,w_2,w_3,w_4)=(b,a-b,c-d,d).
\tag{19}
\]
All four weights are nonnegative by (7). Substitution into the table gives, for all twenty-four permutations,
\[
g_\pi=\sum_iw_i\,1_{\{\pi(i)=i\}}.
\tag{20}
\]
Moreover,
\[
Q(g)=0,\qquad
F(g)=e_3(w_1,w_2,w_3,w_4).
\tag{21}
\]
Since \(F(g+s e)=F(g)\) on \(Q=0\), a secant lift requires \(e_3(w)=0\). With \(w_i\ge0\), this happens exactly when at most two weights are nonzero.

Conversely, one indicator \(1_{\{\pi(i)=i\}}\) is a real rank-two matching product: use a matrix whose \(i\)-th row is the \(i\)-th coordinate vector and whose other rows are all ones. Multiplying that row by a real weight preserves rank at most two. Thus every sum of at most two weighted indicators belongs to the real secant cone.

There are six closed two-dimensional cones, one for each pair of positions, with their rays and the origin included. Their union is exactly the nonnegative part of the projected secant on this derangement-zero face.

## 6. Explicit complex spectral converse, including finite spectra

A stronger converse realizes every pair of real weights by one complex rank-two product after taking its real part. Relabel positions so that they are \(1,2\), and let \(x,y\in\mathbb R\). Put
\[
p=(1-ix,\ 1+y,\ 1,\ 1),\qquad \kappa=i-1,
\]
and let \(C\) have rows
\[
p,\qquad p+\kappa\mathbf1,\qquad \mathbf1,\qquad \mathbf1.
\tag{22}
\]
Then \(\operatorname{rank}C\le2\), and expansion in the first two rows gives the full unitary identity
\[
\begin{aligned}
\frac{\det(C\circ U)}{\det U}
={}&x|U_{11}|^2+y|U_{22}|^2\\
&+i\left[
1+y|U_{12}|^2-x|U_{21}|^2
-xy|\det U[12,12]|^2
\right].
\end{aligned}
\tag{23}
\]
Here \(C\circ U\) denotes entrywise multiplication. The double row-modification term is the \(2\times2\) minor term; complementary unitary minors turn it into a squared modulus. Taking real parts yields the required penalty for every complex unitary, not only for permutation matrices.

This rank-two matrix can be converted to finite normal spectra without a limiting argument. Set \(\tau=2+i\) and
\[
a'=\left(\frac1\tau,\frac1{\tau+\kappa},0,0\right),\qquad
b'_j=\frac1{p_j-\tau},
\]
\[
\Gamma=\tau(\tau+\kappa)\prod_j(p_j-\tau).
\tag{24}
\]
All denominators are nonzero for every real \(x,y\). For \(p_1-\tau\) the real part is \(-1\), and for the other differences the imaginary part is \(-1\). With
\[
r=(\tau,\tau+\kappa,1,1),\qquad s_j=p_j-\tau,
\]
one has exactly
\[
C_{ij}=r_i s_j(a'_i+b'_j).
\tag{25}
\]
Consequently,
\[
\operatorname{Re}\!\left[
\Gamma\det\bigl(D_{a'}+UD_{b'}U^*\bigr)\right]
=x|U_{11}|^2+y|U_{22}|^2.
\tag{26}
\]
For nonnegative \(x,y\), take support direction \(-\Gamma\). The resulting cost has maximum zero, attained by every derangement, and deficit \(x|U_{11}|^2+y|U_{22}|^2\).

This realizes the cost direction modulo constants. It does not assert that adding an arbitrary prescribed constant \(h\) to this particular finite-spectral representative preserves that representative's spectral form. The theorem handles the height of an already given spectral cost by its actual \(g=he-c\).

## 7. Independent extension through the projected boundary

The categorical construction supplies a homogeneous nonic \(P_9\) on the quotient by constants and a polynomial identity
\[
Q(g)^2\det H_F\bigl(g-F(g)Q(g)^{-1}e\bigr)
=-4P_9(g)^2
\tag{27}
\]
where \(Q\ne0\), with polynomial continuation to all \(g\). The independent reviewer combined (10) with (27) to obtain on our full five-dimensional subspace
\[
P_9(g)^2=F(g)^6.
\]
Since the polynomial ring is an integral domain,
\[
P_9|_{\{g_{\mathrm{der}}=0\}}=\pm F^3.
\tag{28}
\]
Thus any point in the Zariski closure of the projected secant on this subspace has \(F(g)=0\). Equation (16) then forces \(d=e\), and (21) gives exactly the same two-weight classification. This removes the finite-lift qualification for this particular face.

The derivation of the nonic identity and its secant interpretation is in the categorical final-batch notes; (28) is the independent reviewer's extension. The basic actual-spectral theorem above can instead be proved using only the elementary necessary conditions (6).

## 8. Explicit positive correction certificate

The classified costs also admit certificates in the full quadratic completely positive framework developed in dual_quadratic_cp_cone.md. In fact, this construction works for any nonnegative diagonal assignment weights, without the restriction to two nonzero entries.

Make row \(v\) of \(U\) real using column phases; write the rows as \(r,v,s,t\), put \(P=I-vv^T\), and let \(p_j=v_j^2\). On \(H=v^\perp\), set
\[
Y=w_4Pe_4e_4^TP,\qquad
a_0=h-w_2p_2-w_4(1-p_4),
\]
\[
M=a_0I_H+Y-w_1Pe_1e_1^TP,\qquad
L=Y-w_3Pe_3e_3^TP.
\tag{29}
\]
Completeness of the four orthonormal rows gives
\[
r^*Mr+s^*Ls
=h-\sum_iw_i|U_{ii}|^2.
\tag{30}
\]
Choose scalar multipliers \(\alpha=a_0\), \(\gamma=0\). Both slacks are positive:
\[
Y+\alpha I_H-M=w_1Pe_1e_1^TP,\qquad
Y+\gamma I_H-L=w_3Pe_3e_3^TP.
\tag{31}
\]
The trace budget is
\[
\operatorname{tr}Y+\alpha+\gamma=h-w_2p_2\le h.
\tag{32}
\]

The correction is genuinely in the quadratic completely positive class because, for unit \(v\),
\[
w_4 e_4e_4^T
=\sum_{j=1}^4
(\sqrt{w_4}\,e_4e_j^T)vv^T
(\sqrt{w_4}\,e_4e_j^T)^T.
\tag{33}
\]
The two slacks have homogeneous bilinear SOS representations
\(w_1\sum_j(r_1v_j)^2\) and \(w_3\sum_j(s_3v_j)^2\). The budget remainder \(w_2p_2\) is represented homogeneously as \(w_2p_2\sum_jp_j\), a nonnegative quadratic in the anchor probabilities. Thus sign averaging and the Gram construction place this certificate in the full fifty-four-parameter cone.

To check compatibility with the original twenty cost coordinates, put
\(z_j=-w_2\,1_{j=2}+w_4\,1_{j=4}\). The first pencil can be encoded by
\[
u_i=h-w_4+w_4\,1_{i=4}-w_1\,1_{i=1}-z_i,\qquad
q_{ij}=z_i+z_j,
\]
and the second by \(u_i=w_4\,1_{i=4}-w_3\,1_{i=3}\), \(q_{ij}=0\).
Compression kills the terms containing \(v\) as a factor, leaving exactly (29).

## 9. What remains open

The theorem excludes an entire cone of potentially bad directions, rather than only one selected nonclassical facet normal. It supplies a finite actual-spectral converse and a constructive positive certificate on the surviving set.

The theorem does not control support directions away from the simultaneous nine-derangement face; the general support inequality remains unproved.

## Files and verification

- code/theorems/finite_and_spin_geometry/dual_derangement_secant_rigidity_exact.py: exact rational polynomial verifier.
- code/theorems/finite_and_spin_geometry/categorical_m8_coordinates.py: the matching coordinates and cubic gradient identities.
- code/theorems/finite_and_spin_geometry/categorical_m8_projection.py: the split Hessian coordinates and projected nonic construction.

All finite algebraic claims used in Sections 2--5 are symbolic identities, independently reproduced by the review track. The elementary converse and positive certificate are given explicitly in Sections 6 and 8.


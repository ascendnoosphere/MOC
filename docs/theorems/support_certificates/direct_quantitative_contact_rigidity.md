# Quantitative spectral rigidity at reflection contacts

Direct track, campaign 3, rounds 011–018. This note proves a stronger
distance estimate near the order-four derangement face and obtains an
actual positive-gap result for fixed real reflection planes near contacts
with two positive assignment weights. The unrestricted complex MOC energy
inequality is not proved.

## 1. Objects and precise conclusions

Let \(\mathcal V\subset\mathbb R^{S_4}\) be the fourteen-dimensional
common-minor cost space, with norm
\(\|g\|_\infty=\max_{\pi\in S_4}|g_\pi|\). Write
\(p_i(\pi)=1_{\{\pi(i)=i\}}\), and put

\[
\mathcal S=\bigcup_{1\le i<j\le4}
\{u p_i+v p_j:u,v\ge0\}.
\]

Let \(P_9\) be the projected spectral nonic. It is a fixed homogeneous
degree-nine real polynomial on \(\mathcal V\), invariant under adding a
constant cost. It vanishes on every actual complex spectral support cost,
including its constant support shift. The results below hold on the larger
real algebraic set \(P_9=0\); no sufficiency of this equation for actual
spectral realizability is assumed.

**Theorem 1 (square-root distance estimate).** There is an absolute
constant \(C\), for the fixed coordinate normalization, such that every
\(g\in\mathcal V\) with \(g_\pi\ge0\) and \(P_9(g)=0\) satisfies

\[
\boxed{\operatorname{dist}_\infty(g,\mathcal S)
\le C\sqrt{M\delta}},\qquad
M=\|g\|_\infty,
\quad\delta=\max_{\pi\text{ a derangement}}g_\pi.
\tag{1}
\]

**Theorem 2 (linear estimate at a two-weight interior point).** Fix
\(s_0=u_0p_i+v_0p_j\), with \(u_0,v_0>0\). On a neighborhood of \(s_0\)
in the same nonnegative nonic zero set,

\[
\boxed{\operatorname{dist}_\infty(g,\mathcal S)
\le C_{s_0}\delta.}
\tag{2}
\]

The approximating point in (2) can be chosen on the particular cone
\(\mathbb R_+p_i+\mathbb R_+p_j\).

Both statements hold after relabeling columns, with derangements and
assignment indicators taken relative to any fixed permutation.

**Theorem 3 (local positive-gap energy inequality).** Fix

\[
R=\begin{pmatrix}
a&0&b&c\\0&a&-c&b\\b&-c&-a&0\\c&b&0&-a
\end{pmatrix},\qquad a^2+b^2+c^2=1,\quad abc\ne0,
\tag{3}
\]

and a real orthonormal frame \(Y\) for its negative eigenspace. Let
\(\pi_0=(12)(34)\), and fix

\[
s_0(U)=w_i|U_{i,\pi_0(i)}|^2+
       w_j|U_{j,\pi_0(j)}|^2,\qquad i\ne j,\quad w_i,w_j>0.
\tag{4}
\]

For actual complex spectral support deficits \(g=h-F\) sufficiently close
to \(s_0\), satisfying \(g(I)=0\) and \(g_\pi\ge0\), the full complex
two-plane orbit with frame \(Y\) satisfies

\[
\boxed{E(g)\le C_{R,s_0}g(R)^2.}
\tag{5}
\]

Here \(E=\frac14\ell^T A^+\ell\) is the optimized cubic energy from the
rank-two Cayley formula. Shrinking the neighborhood if necessary, (5)
gives \(E\le g(R)\), with strict inequality when \(g(R)>0\), and hence
the MOC support inequality on this entire complex \(U(2)\) orbit.

The neighborhood concerns costs with the identity as a support maximum;
the reflection plane is fixed. This is not a neighborhood theorem for all
planes simultaneously or a proof of global MOC.

## 2. Algebraic inputs and their scope

The construction and normalization of the cubic \(F_3\) and nonic \(P_9\)
are in `../moc200/categorical_m8_coordinates.py`,
`../moc200/categorical_m8_projection.py`, and
`../moc200/review_final_batch_proofs.md`. We write \(F_3\) for the cubic
in this note, to distinguish it from the determinant support functional.

The external algebraic input is the invariant cubic and doubled Hessian
divisor theorem of Howard, Millson, Snowden, and Vakil,
[*The geometry of eight points in projective space: representation theory,
Lie theory, dualities*](https://arxiv.org/abs/1103.5255). The coordinate
projection and the following determinant-square identity were derived in
the prior campaign:

\[
N=Q^2h_0-F_3Qh_1+F_3^2h_2+2F_3^3\det K=-4P_9^2.
\tag{6}
\]

An overall nonzero coordinate-normalization factor in (6) has no effect
on any order-of-vanishing argument below. In the fixed split coordinates,
\(B\) is a linear \(2\times2\) block, \(Q=\det B=D_{\mathbf1}F_3\),
\(H\) is the Hessian of the cubic, \(K\) is a fixed \(9\times9\)
height-independent submatrix of that Hessian, and

\[
\det H(x+t\mathbf1)=\sum_{j=0}^3h_j(x)t^j.
\tag{7}
\]

The height variable may be based at any \(x\). Hessians in the original
and split coordinates differ by a fixed invertible congruence.

Let \(\mathcal W\) be the space of costs vanishing on the nine
derangements. The other crucial prior identity is

\[
P_9|_{\mathcal W}=\pm F_3^3.
\tag{8}
\]

The finite new inputs in Sections 3 and 4 are checked with exact rational
arithmetic in `direct_nonic_assignment_jets.py` and recorded in its JSON
certificate. They do not involve numerical evidence about vanishing.

## 3. The nonic has higher multiplicity on the assignment cones

Let \(H_i=H(p_i)\) and \(H_e=H(\mathbf1)\). The exact certificate gives

\[
B(p_i)=0,\qquad \nabla F_3(p_i)=0,\qquad
\operatorname{rank}H_i=4,\qquad \operatorname{rank}H_e=4.
\tag{9}
\]

For every pair \(i\ne j\), it also gives

\[
\dim(\operatorname{im}H_i+\operatorname{im}H_j)=7,
\qquad H_i p_j=H_jp_i\ne0.
\tag{10}
\]

These identities imply a uniform rank estimate, not just an estimate at
the finite points used to check the matrices. For
\(s=u p_i+v p_j\), cubic polarization and (9) give

\(F_3(s)=0\), since the pure and mixed cubic coefficients are all
evaluations of the vanishing gradients at the two assignment points.
The same polarization gives

\[
H(s)(u p_i-v p_j)=0.
\tag{11}
\]

Set \(W=\operatorname{im}H_i+\operatorname{im}H_j\). The symmetric
matrix \(H(s)\) maps into \(W\) and vanishes on \(W^\perp\). When
\(uv\ne0\), the kernel vector in (11) has a nonzero component in \(W\):
otherwise \(H_i(u p_i-v p_j)=0\), contrary to
\(-vH_ip_j\ne0\). Thus the restriction of \(H(s)\) to the
seven-dimensional \(W\) has a kernel. Therefore

\[
\operatorname{rank}H(u p_i+v p_j)\le6.
\tag{12}
\]

When one coefficient vanishes, (9) gives rank at most four instead.

At a two-assignment point \(s\), equations (9) and (12) imply the
following perturbation orders, where \(z\to0\) is arbitrary in the
fourteen-dimensional space:

\[
Q(s+z)=O(\|z\|^2),\qquad F_3(s+z)=O(\|z\|),
\]

\[
h_j(s+z)=O(\|z\|^4),\qquad
\det K(s+z)=O(\|z\|^3).
\tag{13}
\]

For the \(h_j\) statement, the rank of \(H(s+t\mathbf1)\) is at most
\(6+4=10\) for every fixed \(t\). A determinant of a \(14\times14\)
matrix of rank at most ten has perturbation order at least four. Taking
four distinct fixed values of \(t\) and extracting the coefficients of
the cubic polynomial (7) proves the statement for each \(h_j\).
The \(K\) statement follows from its size nine and rank at most six.

The four terms of (6) consequently have perturbation orders at least
\(8,7,6,6\), respectively. Since a square has twice the vanishing order
of its polynomial square root,

\[
\boxed{\operatorname{ord}_sP_9\ge3
\quad\text{on every two-assignment plane}.}
\tag{14}
\]

At a single-assignment point, \(\nabla F_3=0\) improves the cubic order
to two, while \(\operatorname{rank}H(s+t\mathbf1)\le8\) improves each
\(h_j\) order to six. The \(K\) order is at least five. The four terms
of (6) then have orders at least \(10,10,10,11\), giving

\[
\boxed{\operatorname{ord}_{u p_i}P_9\ge5.}
\tag{15}
\]

These are lower bounds. No assertion of equality of either multiplicity
is required in this note.

## 4. A symmetric cubic measures distance along the face

The nonnegative cone of \(\mathcal W\) has the two positive
parametrizations established in
`../moc200/review_derangement_stability.md`. With nonnegative variables
\(A,B,C,E,k\), the two cubic formulas there are

\[
\begin{aligned}
F_3&=(E+k)(B+k)(A+k)
   +C[A(B+E+k)+(B+k)(E+k)],\\
F_3&=(E+k)(A+k)(B+k)
   +C[(A+k)(B+E+k)+BE].
\end{aligned}
\]

Both simplify to exactly the same symmetric expression. With
\(w=(B,A,C,E)\),

\[
\boxed{F_3=e_3(w)+k e_2(w)+k^2e_1(w)+k^3.}
\tag{16}
\]

Deleting \(k\) changes the cost by at most \(2k\) in sup norm and leaves
the assignment cost \(\sum_iw_ip_i\). The largest cost coordinate is
the identity coordinate, so

\[
M_1=\|g_1\|_\infty=\sum_iw_i+2k.
\tag{17}
\]

Order the weights \(u\ge v\ge w\ge z\ge0\) and define
\(r=k+w+z\). Let \(s\in\mathcal S\) retain the two largest weights.
Then

\[
\|g_1-s\|_\infty\le2k+w+z\le2r,
\qquad
u+v+r\le M_1\le2(u+v+r).
\tag{18}
\]

The symmetric expression supplies the comparability estimate

\[
\boxed{\frac1{18}r(u+r)(v+r)
\le F_3(g_1)\le3r(u+r)(v+r).}
\tag{19}
\]

For the lower bound, each of
\((u+k)(v+k)(w+k)\) and \((u+k)(v+k)(z+k)\) is a sum of terms present
in (16). Taking their average gives at least
\(r(u+k)(v+k)/2\). Since \(w,z\le v\le u\),
\(u+r\le3(u+k)\) and \(v+r\le3(v+k)\), proving the factor \(1/18\).

For the upper bound, the four terms of (16) are bounded in sum by
\(2uvr+3(u+v)r^2+3r^3\), which is at most the right side of (19).
Two further consequences used below are

\[
\boxed{F_3(g_1)\ge\frac1{36}M_1r^2,
\qquad F_3(g_1)\ge uv r.}
\tag{20}
\]

The first follows from \(M_1\le2(u+r)\) and \(v+r\ge r\); the second
uses the terms \(uv(w+z)+kuv\) in (16).

## 5. A derivative estimate incorporating both multiplicities

Choose the fourteen independent permutation coordinates and use their
sup norm; it is at most the full 24-coordinate sup norm. Norms of
derivatives below are the corresponding multilinear operator norms.
All constants in this section depend only on the fixed polynomial
\(P_9\).

For \(s=u p_i+v p_j\), \(u,v\ge0\), (14) says that \(D P_9(s)\) and
\(D^2P_9(s)\) vanish. The tensor \(D^3P_9(s)\), a homogeneous polynomial
of degree six in \(u,v\), is divisible by \(u^2v^2\): at either axis,
(15) makes its constant and first transverse coefficients vanish.
Similarly \(D^4P_9(s)\), of degree five, is divisible by \(uv\).
Therefore, with one fixed constant \(C_0\) large enough for all six
pairs,

\[
\begin{aligned}
\|D^3P_9(s)\|&\le C_0u^2v^2(u+v)^2,\\
\|D^4P_9(s)\|&\le C_0uv(u+v)^3,\\
\|D^jP_9(s)\|&\le C_0(u+v)^{9-j},\qquad5\le j\le9.
\end{aligned}
\tag{21}
\]

Taylor's formula for the gradient is finite. For \(\|e\|\le R\), (21)
implies

\[
\boxed{
\|D P_9(s+e)\|
\le C_1 R^2(u+R)^2(v+R)^2(u+v+R)^2.}
\tag{22}
\]

Here is a direct check of all Taylor orders. The cubic-derivative term is
bounded immediately by the right side. For the fourth-derivative term,

\[
[(u+R)(v+R)]^2\ge2uvR(u+v)
\]

absorbs \(R^3uv(u+v)^3\). For every \(j\ge5\), use

\[
(u+R)(v+R)\ge R(u+v+R)
\]

and
\(R^{j-1}(u+v)^{9-j}\le R^4(u+v+R)^4\).
The finitely many Taylor factors are absorbed into \(C_1\).

Thus (22) is a polynomial estimate valid at all scales. It is not a
bounded-region estimate that loses homogeneity near a one-weight corner.

## 6. Proof of the square-root and linear distance estimates

Let \(D:\mathcal V\to\mathbb R^9\) be restriction to the derangements.
Its rank is nine. Fix a linear right inverse \(L\), and choose
\(\beta\ge1\) such that
\(\|Lx\|_\infty\le\beta\|x\|_\infty\). Let
\(\kappa=\sum_i p_i\), the fixed-point count. Define the same positive
face correction used in the previous stability theorem:

\[
g_1=g-LDg+\beta\delta\kappa.
\tag{23}
\]

It lies in the nonnegative cone of \(\mathcal W\), and

\[
\|g_1-g\|_\infty\le5\beta\delta,
\qquad M_1\le(1+5\beta)M.
\tag{24}
\]

Use the parameters of Section 4 for \(g_1\). If \(r\le\delta\), then
\(\|g-s\|_\infty\le(5\beta+2)\delta\); this already proves (1)
because \(\delta\le M\).

Suppose instead that \(r>\delta\). The segment from \(g\) to \(g_1\)
lies within distance \((2+5\beta)r\) of \(s\). Apply (22), (24),
\(P_9(g)=0\), and (8):

\[
\begin{aligned}
F_3(g_1)^3
&=|P_9(g_1)-P_9(g)|\\
&\le C_2\delta r^2(u+r)^2(v+r)^2(u+v+r)^2\\
&\le C_3\delta F_3(g_1)^2M_1^2.
\end{aligned}
\tag{25}
\]

The second inequality uses the lower estimate in (19). If the cubic is
zero, then \(r=0\) by (19). Otherwise cancellation yields

\[
\boxed{F_3(g_1)\le C_3\delta M_1^2.}
\tag{26}
\]

This bound also holds when \(r\le\delta\), after enlarging \(C_3\),
by the upper estimate in (19). Combining (26) with the first inequality
in (20) gives

\[
r^2\le36C_3M_1\delta\le C_4M\delta.
\]

Together with (18) and (24), this proves Theorem 1.

There is also the more informative two-weight bound

\[
r\le\frac{C_3M_1^2}{uv}\,\delta\qquad(uv>0),
\tag{27}
\]

using the second inequality in (20). At a fixed two-weight interior point
\(s_0\), the chamber parameters of \(g_1\) are continuous piecewise
linear functions of its cost coordinates. The two specified weights
remain bounded below and remain the largest weights in a sufficiently
small neighborhood. The numerator in (27) remains bounded. Equations
(18), (24), and (27) therefore prove Theorem 2, with the approximating
point on the same two-weight cone.

## 7. An exact positive permutation law for the reflection family

For (3), the signed products
\(\operatorname{sgn}(\pi)\prod_iR_{i,\pi(i)}\) are nonnegative. The
only nonzero ones are the following nine, all derangements relative to
\(\pi_0=(12)(34)\):

| Permutation | Weight |
|---|---:|
| identity | \(a^4\) |
| \((13),(24)\) | \(a^2b^2\) each |
| \((14),(23)\) | \(a^2c^2\) each |
| \((13)(24)\) | \(b^4\) |
| \((14)(23)\) | \(c^4\) |
| \((1324),(1423)\) | \(b^2c^2\) each |

They sum to \((a^2+b^2+c^2)^2=1\). For actual spectral matching products,

\[
\det(D_\alpha+R D_\beta R^*)
=\frac{\det([(\alpha_i+\beta_j)R_{ij}])}{\det R}
\]

shows directly that these weights give the corresponding support value.
The identity also holds on all of \(\mathcal V\) by linearity of the
common-minor extension. Consequently

\[
g(R)=\sum_{\pi}q_\pi(R)g_\pi.
\tag{28}
\]

Since \(abc\ne0\), all nine displayed weights are positive. Thus, for
every nonnegative cost,

\[
\boxed{\delta_{\pi_0}:=
\max_{\pi(i)\ne\pi_0(i)\ \forall i}g_\pi
\le\frac{g(R)}{\min_{q_\pi>0}q_\pi(R)}.}
\tag{29}
\]

This gives the quantitative bridge from the derangement face to the
reflection gap without a condition-number estimate for the facet cone.

## 8. The quadratic kernel separates from the cubic direction

This separation is essential to Theorem 3. A distance estimate alone
would not control the pseudoinverse energy for a general complex plane
with a degenerating quadratic eigenvalue.

Choose \(Y\) real and write its rows as \(y_i\in\mathbb R^2\). For

\[
T=\begin{pmatrix}s&x+iy\\x-iy&t\end{pmatrix},
\]

the real part of \(L_{ij}(T)=y_iTy_j^T\) depends only on \((s,t,x)\),
and its imaginary part is \(y p_{ij}\), with
\(p_{ij}=\det\binom{y_i}{y_j}\). Because

\[
A_g(T)=\sum_{i<j}g_{(ij)}|L_{ij}(T)|^2,
\]

the quadratic form splits **exactly**, for every real cost with
\(g(I)=0\), as

\[
A_g=A_{g,\mathrm{real}}\oplus A_{g,yy},\qquad
A_{g,yy}=\sum_{i<j}g_{(ij)}p_{ij}^2.
\tag{30}
\]

The cubic covector also separates exactly: every real-symmetric \(T\)
makes its defining imaginary traces zero, so

\[
\ell_g(T)=\ell_{g,y}y.
\tag{31}
\]

For an assignment contact
\(s=\sum_iw_i|U_{i,\pi_0(i)}|^2\), \(P=(I-R)/2\) has
\(P_{i,\pi_0(i)}=0\). Each squared entry is zero at \(R\), so its
differential, and hence its cubic covector, vanishes:
\(\ell_s=0\). Moreover,

\[
A_{s,yy}=(w_1+w_2)\frac{(1-a)^2}{4}
          +(w_3+w_4)\frac{(1+a)^2}{4}.
\tag{32}
\]

This is strictly positive whenever any weight is positive and
\(|a|<1\). The real block of \(A_s\) may have a kernel, including the
scalar matrix direction. It has no coupling to \(y\) in (30), for
either the contact cost or any perturbed cost. Thus, whenever
\(A_{g,yy}>0\),

\[
\boxed{E(g)=\frac{\ell_{g,y}^2}{4A_{g,yy}}.}
\tag{33}
\]

There is no omitted Schur-complement contribution from a small eigenvalue
of the real block.

## 9. Proof of the local positive-gap theorem

Fix \(R,s_0\) as in Theorem 3. Relabel the distance theorem to \(\pi_0\).
For \(g\) near \(s_0\), Theorem 2 gives an assignment contact \(s\)
on the same two-weight cone with

\[
\|g-s\|_\infty\le C\delta_{\pi_0}\le C' g(R).
\tag{34}
\]

The map from the cost to \(\ell_{g,y}\) is linear and bounded, and
\(\ell_s=0\). Hence \(|\ell_{g,y}|\le C''g(R)\). Equations (30) and
(32) also give \(A_{g,yy}\ge A_{s_0,yy}/2>0\) after shrinking the
neighborhood. Equation (33) proves (5).

In the same neighborhood \(g(R)\to0\) as \(g\to s_0\), so the
neighborhood can be made small enough that
\(C_{R,s_0}g(R)<1\) whenever \(g(R)>0\). Then \(E(g)<g(R)\).
At \(g(R)=0\), the zero-contact theorem gives \(\ell=0\), or the
distance estimate gives \(g\in\mathcal S\) directly.

Since \(g_{(ij)}\ge0\), \(A_g\) is positive semidefinite. Its
covector lies in its range by (30)–(32). The optimized Cayley criterion
therefore proves the support inequality on the entire complex \(U(2)\)
orbit, completing the proof of Theorem 3.

## 10. What the one-weight corner still requires

Near a one-weight contact, Theorem 1 and the same exact separation give
only

\[
E(g)\le C_R g(R),
\tag{35}
\]

with an unspecified constant. To see the scaling, normalize the cost so
the contact weight stays bounded above and below. The distance estimate
gives \(\ell_y=O(\sqrt{g(R)})\), while \(A_{yy}\) stays bounded below.
This rules out an unbounded energy ratio along actual nonic-zero costs
approaching that fixed contact plane, but it does not prove the required
constant one.

A leading blowup \(g_\epsilon=s_0+\epsilon q+\epsilon^2r+\cdots\)
with reflection gap of order \(\epsilon^2\) can have
\(\ell_y\) of order \(\epsilon\). Its limiting energy ratio is a
nontrivial quotient of the second-order reflection deficit and the square
of the first-order cubic covector. The fifth-order nonic at a one-weight
axis constrains \(q\), but its full real spectral branch and the
second-order terms are needed to settle that quotient. No coefficient-one
bound or claim of a sharp Hölder exponent is made here.

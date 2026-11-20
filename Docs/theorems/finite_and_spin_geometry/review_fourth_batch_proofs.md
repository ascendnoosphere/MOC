## 1. The real fixed-chart completion criterion includes singular cases

For \(V\in SO(4)\), define

\[
a=\det V[123,124],\quad b=-\det V[23,24],\quad
c=-\det V[13,14],\quad d=V_{34},
\]

\[
\Delta(V)=4(ab-cd)^2-(a^2+b^2-c^2-d^2)^2.
\]

The assertion in `categorical_global_completion_criterion.md` is accepted with no remaining nonsingularity restriction:

\[
\exists\text{ diagonal unitary }Z:\operatorname{rank}(V-Z)\le2
\quad\Longleftrightarrow\quad\Delta(V)\ge0.
\tag{1}
\]

Necessity comes from a three-by-three minor of \(V-Z\), whose relevant two-phase polynomial is

\[
p(z_1,z_2)=a+bz_1+cz_2+dz_1z_2.
\]

There is a torus zero precisely when some \(|z_1|=1\) satisfies
\(|a+bz_1|=|c+dz_1|\). The difference of the squared moduli is

\[
a^2+b^2-c^2-d^2+2(ab-cd)\operatorname{Re}z_1.
\]

Its range contains zero exactly when \(\Delta\ge0\). If both coefficients of \(z_2\) vanish at the same \(z_1\), that point already gives a torus zero; no division by a possibly zero coefficient is needed.

For regular sufficiency, partition \(V=\left(\begin{smallmatrix}A&B\\C&E\end{smallmatrix}\right)\) into two-by-two blocks and assume \(C\) invertible. Orthogonality gives \(I-A^*A=C^*C\succ0\), so \(A-Z_0\) is invertible for every diagonal unitary \(Z_0\). The feedback matrix

\[
F=E-C(A-Z_0)^{-1}B
\]

is unitary. One direct proof uses norm preservation for the orthogonal block matrix with the internal relation \(Ax+By=Z_0x\). A torus zero above makes one off-diagonal entry of \(F\) vanish. A two-by-two unitary with that entry zero is diagonal. Choosing the remaining phases equal to its diagonal then gives a rank-two completion.

The singular case requires a closure argument, rather than the same inverse formula. Write \(V=L(q)R(r)\), with unit real quaternions. The previously audited exact identity is

\[
\Delta(V)=-16\prod_{i=0}^3(q_i^2-r_i^2).
\tag{2}
\]

Every point with \(\Delta=0\) can be approximated by points with \(\Delta>0\). To see this, put \(p_i=q_i^2\), \(s_i=r_i^2\). First mix both probability vectors with a small amount of the uniform vector. Their difference still has a zero coordinate, while both vectors now lie in the simplex interior. If \(p-s\ne0\), its at most three nonzero entries have one sign occurring exactly once; assign the formerly zero coordinates the other sign, compensating by a tiny change in a nonzero coordinate to preserve the zero sum. The product of all four differences is then negative. If all differences vanish, use a small multiple of \((-3,1,1,1)\). Signed square roots lift these perturbations continuously to the original quaternions.

The analytic function \(\det C\) is not identically zero on connected \(SO(4)\). Its nonzero set is therefore dense in every nonempty open set, including each local \(\Delta>0\) region. Regular completed matrices approach every boundary point. Compactness of the phase torus and closedness of the rank-at-most-two condition complete the proof of (1).

Applying (1) to all 24 signed column-permutation charts proves the exact monomial-distance criterion. This is a real four-dimensional structural theorem. It does not establish scalar MOC for every rank-two relative unitary.

## 2. The finite spin arrangement and the exact extent of its present certificates

The 24 quaternion chart lifts produce 192 distinct primitive hyperplanes in \(\mathbb R^{4,4}\). The independent reconstruction found 32 normals with support two, 96 with support four, and 64 with support eight. Every normal is null for \(J=\operatorname{diag}(I_4,-I_4)\). These facts are exact enumeration statements, not counts inferred from a plotted arrangement.

For each of the three supplied eight-ray cones, the verifier checks the inverse wall/ray matrices, a rational physical witness with \(\|q\|=\|r\|=1\), signs of all 192 walls, and negativity of all 24 completion discriminants throughout the open cone. The numbers of orthogonal unordered wall pairs are 15, 16, and 17. Consequently the three cones cannot be equivalent under the orthogonal spin symmetries used in the construction.

All 48 common-facet quartics were independently reconstructed on each cone. Exactly 44 in each cone have coefficientwise nonnegative expansions in the nonnegative ray parameters. The remaining four on the first cone are indexed \((0,6),(0,12),(1,6),(1,12)\) in the supplied chart convention. The exact Gram certificate below covers \((0,12)\), and symmetry transfers it to \((1,12)\). Thus the present first-cone result covers **46 of 48** facets. It does not cover the other two, and three inequivalent cones are not a classification of every no-completion chamber.

This audit does not recount the previous batch's separate proof that the common-minor polytope has 82 facets. It uses that result as the starting finite list of inequalities to test.

## 3. A new exact coercivity bound and complete equality locus

Let \(t_0,\ldots,t_7\ge0\) be the ray coordinates of the first cone, and let \(g(t)=\|q(t)\|^2-\|r(t)\|^2\). The exact rational certificate has the form

\[
\frac{f_{0,12}(t)}{1031}=b(t)^TQb(t)+g(t)h(t)+r(t),
\tag{3}
\]

where the 26 entries of \(b\) are quadratic, and every coefficient of \(r\) is nonnegative. The verifier reconstructs the target quartic from the quaternion facet formula before checking (3) coefficient by coefficient.

The new quantitative check is

\[
Q-\frac1{10^6}I_{26}\succ0.
\tag{4}
\]

All 26 exact Fraction LDL pivots are positive. No floating eigenvalue is used as a proof. Four entries of \(b\) are \(t_0^2,t_1^2,t_2^2,t_3^2\). Therefore, on the physical cone \(g=0\),

\[
\boxed{f_{0,12}(t)\ge
\frac{1031}{4,000,000}
\left(t_0^2+t_1^2+t_2^2+t_3^2\right)^2.}
\tag{5}
\]

This is coercivity transverse to the four-dimensional boundary face. It gives an exact gap at any specified positive distance from that face in the cone coordinates.

There is also a complete equality classification. On \(t_0=\cdots=t_3=0\), all entries of \(b\) vanish except

\[
s=t_4t_7-\frac12(t_5t_6+t_6^2)+t_7^2,
\]

and direct restriction of the target polynomial is \(f_{0,12}=s^2\). Since \(Q\) is positive definite, equality in the nonnegative decomposition forces \(b=0\). Hence

\[
\boxed{f_{0,12}=0\iff t_0=t_1=t_2=t_3=0\ \text{and}\ s=0}
\tag{6}
\]

on the physical nonnegative cone.

The cone map

\[
Tt=(t_1,2t_0,2t_3,t_2,t_5,2t_4,2t_7,t_6)
\]

satisfies \(g(Tt)=2g(t)\), \(f_{1,j}(t)=f_{0,j}(Tt)/4\) for \(j=6,12\), and \(s(Tt)=-2s(t)\). The verifier checks these polynomial identities exactly. Thus the second certified hard facet has the same equality locus and an explicit transferred positive lower bound. The result still gives no sign proof for the pair with \(j=6\).

## 4. Defect-one positivity and reciprocity: accepted, with the scalar limitation

For a defect-one unitary completion \(D(z)=D_0+zxy^*\), exterior powers split as

\[
\bigwedge^kD(z)=C_k+zE_k,
\quad C_k^*E_k=C_kE_k^*=0,
\]

\[
C_k^*C_k+E_k^*E_k=I,
\quad C_kC_k^*+E_kE_k^*=I.
\]

The source and target split into exterior vectors respectively avoiding or containing the one-dimensional defect direction. This proves the identities, including degenerate parameter values. In particular,

\[
I-(\bigwedge^kD(w))^*\bigwedge^kD(z)
=(1-\bar wz)E_k^*E_k,
\]

and the coefficient on the right is a positive projection of rank \(\binom{m-1}{k-1}\).

For each minor \(c+ze\), the two-by-two coefficient matrix of its squared modulus is positive semidefinite and rank at most one. Summing these as matrix-unit Kraus terms gives the stated completely positive two-variable kernel. These operator facts do not imply subharmonicity after arbitrary real spectral support weights, which can have either sign.

The reciprocal completion is \(\widetilde D(w)=D_0^*+wyx^*\). For nonzero \(z\),

\[
D(z)^{-1}=\widetilde D(1/z),\qquad |\det D(z)|^2=|z|^2.
\]

Consequently the real quadratic scalar coefficients \((c,b,q)\) transform to \((q,\bar b,c)\). Reciprocal transport exchanges the interior and exterior of the disk, so a contraction estimate cannot simply be applied on both sides. The positive kernel and reciprocity are valid structural information; neither resolves the signed center term in defect-one scalar induction.

## 5. The entire fixed \(U(2)\) plane has an exact six-coordinate lift

Fix an isometry \(Y:\mathbb C^2\to\mathbb C^n\), a base unitary \(W\), and

\[
U_Y(V)=I+Y(V-I)Y^*,\qquad V\in U(2).
\]

Every selected minor of \(U_Y(V)W\) is a linear combination of \(1\), the four entries of \(V\), and \(\det V\). This follows by the rank-two update expansion; its quadratic part is a multiple of \(\det(V-I)=\det V-\operatorname{tr}V+1\). It does not require a nonzero base minor.

Write \(V=e^{i\theta}(q_0I+i\sum_{j=1}^3q_j\sigma_j)\), with \(q\in S^3\), and let \(p=(\cos\theta,\sin\theta)\in S^1\). Multiplication by the harmless phase \(e^{-i\theta}\) turns every minor into a complex linear form in the six real coordinates \((q,p)\). Its squared modulus is thus a real quadratic form. Every scalar support objective has the form \(z^TLz\).

The convex hull of this entire plane's squared-minor profiles is exactly the linear image of

\[
X\succeq0,\qquad \operatorname{tr}X_{qq}=1,\qquad
\operatorname{tr}X_{pp}=1.
\tag{7}
\]

For completeness, let \(J=\operatorname{diag}(I_4,-I_2)\) and factor \(X=BB^T\). The symmetric matrix \(B^TJB\) has trace zero. A trace-zero symmetric matrix has an orthonormal basis in which every diagonal entry is zero: find a unit vector with zero quadratic value between opposite-sign eigenvectors, restrict to its orthogonal complement, and repeat. The corresponding columns \(z_\nu\) of a rotated factor \(B\) satisfy \(z_\nu^TJz_\nu=0\). Normalize their two equal block norms to obtain points of \(S^3\times S^1\). The squared norms give convex weights summing to one. At most \(\operatorname{rank}X\le6\) actual plane points are required.

It follows that a scalar height \(h\) bounds the whole plane if and only if

\[
\exists\lambda\in\mathbb R:\quad
\frac h2I_6-L+\lambda J\succeq0.
\tag{8}
\]

The moment description has a strictly positive feasible matrix, so the finite-dimensional semidefinite duality here includes attainment. This is an exact description of one fixed plane. It does not identify its image with the permutation hull.

## 6. Stationarity removes one dimension, but prescribed heights retain it

For a Hermitian two-by-two matrix

\[
T=\begin{pmatrix}s&x+iy\\x-iy&t\end{pmatrix},\qquad
d=st-x^2-y^2,
\]

the Cayley map is \(V=(I+iT)(I-iT)^{-1}\), with positive denominator

\[
D(T)=\det(I+T^2)=1+s^2+t^2+2x^2+2y^2+d^2.
\]

At a stationary identity, direct use of the preceding six-coordinate formula gives

\[
F(V)-F(I)=\frac{2H(T,T)+2d\ell(T)+\Delta d^2}{D(T)}.
\tag{9}
\]

Here \(H\) is the Hessian for the exponential path convention used in the continuous notes, and \(\Delta=F(-I)-F(I)\). Thus the entire-plane nonascent condition is

\[
M_5=\begin{pmatrix}2H_4&\ell\\\ell^T&\Delta\end{pmatrix}\preceq0.
\tag{10}
\]

Necessity is stronger than an ordinary Hessian test. The projective image \([T:\det T]\) is dense in \(\mathbb RP^4\): for a target \([Q:c]\) with \(c\det Q\ne0\), take \(T=(c/\det Q)Q\). The quadratic numerator in (9) therefore has the required sign on every projective direction if it has that sign on the Cayley plane. Sufficiency follows immediately; the omitted Cayley locus follows by continuity.

For a higher prescribed level \(h\), put \(c=h-F(I)\),

\[
W_6=\operatorname{diag}(1,1,1,2,2,1),\quad
N_h=cW_6-\operatorname{diag}(0,M_5).
\]

The homogenized coordinates \((z_0,s,t,x,y,d)\) satisfy
\(z_0d-st+x^2+y^2=0\). The whole plane lies below \(h\) exactly when
\(N_h+\lambda J_6\succeq0\) for some real multiplier, where \(J_6\) represents that quadratic equation. The same trace-zero decomposition proves the nonstrict equality form; there is no missing degeneracy assumption.

In the separate two-phase note, the displayed Schur complement using the stationary matrix \(M_3\) requires the stationarity assumption of its preceding paragraph. Without stationarity, use the stated full four-by-four two-phase pencil. No incorrect extension of that specialized formula is needed in the full \(U(2)\) reduction.

The derivative factors were also checked from (9):

\[
D^3F(e^{i\varepsilon T})\big|_{\varepsilon=0}
=\frac32\det T\,\ell(T).
\]

At the reflection endpoint, the first derivative is \(-\ell(\operatorname{adj}S)\), and its exponential second derivative is
\(H(\operatorname{adj}S,\operatorname{adj}S)-\Delta\operatorname{tr}(S^2)/2\).
The endpoint need not itself be stationary. These factors follow by the inverse Cayley identity and are not obtained by assuming endpoint stationarity.

## 7. Triangle flow proves kernel compatibility, not the reflection budget

Now take diagonal spectra, and assume the chosen identity permutation already attains the global support height \(h\). Set

\[
\delta_{ij}=h-\operatorname{Re}(\eta z_{(ij)})\ge0,
\qquad L_{ij}(T)=y_iTy_j^*,
\]

\[
\mathcal A(T)=\sum_{i<j}\delta_{ij}|L_{ij}(T)|^2.
\]

The rank-two matrix \((a_i+b_j)\) has zero three-by-three determinants. Expanding a three-label determinant gives

\[
z_{\rm id}-z_{(ij)}-z_{(ik)}-z_{(jk)}
+z_{(ijk)}+z_{(ikj)}=0.
\tag{11}
\]

If \(s_{ijk}=\operatorname{Re}\eta(z_{(ijk)}-z_{(ikj)})\), the nonnegative deficits of both cycles therefore imply

\[
|s_{ijk}|\le\delta_{ij}+\delta_{ik}+\delta_{jk}.
\tag{12}
\]

The third derivative calculation in `continuous_spectral_rank_two_budget.md` was independently audited, including its orientation and factors. With \(W_i=y_i^*y_i\),

\[
\ell(T)=4\sum_{i<j<k}s_{ijk}C_{ijk}(T),\qquad
C_{ijk}(T)=-\operatorname{Im}\operatorname{tr}(\operatorname{adj}W_i\,W_jTW_k).
\]

The identity \(TWT=\operatorname{tr}(TW)T-\det T\operatorname{adj}W\) reduces the apparent cubic term to \(\det T\) times this linear form. The remaining part is real because it is a trace of two Hermitian matrices. This checks the sign convention without relying only on a sampled determinant.

The supplied Plücker flow distributes each \(s_{ijk}\) among its three edges with coefficient magnitude at most one. It yields explicit complex \(a_{ij}\) such that

\[
\ell(T)=4\sum_{i<j}\delta_{ij}\operatorname{Re}(\bar a_{ij}L_{ij}(T)).
\tag{13}
\]

Consequently \(\ell\) automatically annihilates \(\ker\mathcal A\), including every zero-edge degeneracy. This closes one genuine obligation in the stationary plane reduction.

Let \(g=h-F(I-2YY^*)\) be the reflection loss. The whole plane is bounded by \(h\) exactly when

\[
\begin{pmatrix}4\mathcal A&-\ell\\-\ell^T&g\end{pmatrix}\succeq0,
\quad\text{equivalently}\quad
\boxed{g\ge\frac14\ell^T\mathcal A^+\ell.}
\tag{14}
\]

The range condition in this Schur complement has just been proved. The boxed scalar inequality remains unproved in general.

For a chosen flow, \(C_{\rm flow}=\sum\delta_{ij}|a_{ij}|^2\) gives the exact identity

\[
(h-F(V))D(T)=4\sum_{i<j}\delta_{ij}|L_{ij}(T)-d a_{ij}|^2
+(g-4C_{\rm flow})d^2.
\tag{15}
\]

Thus \(g\ge4C_{\rm flow}\) is sufficient. Minimizing over all edge representations of (13) gives
\(C_{\min}=\ell^T\mathcal A^+\ell/16\), recovering (14). A particular explicit flow need not be energy-minimizing. Neither a universal explicit-flow budget nor the universal optimum budget is claimed in this audit.

The maximizing-base hypothesis is essential to this argument. Permuting the second spectrum to put its maximizing vertex at the identity also changes the relative unitary; its distance from that identity need not remain two. For an arbitrary given rank-two relative unitary, the prescribed-height six-by-six pencil is the valid formulation.



### A coordinate-containing active plane

Work in a diagonal spectral basis, with \(A=\operatorname{diag}(a_j)\), \(B=\operatorname{diag}(b_j)\), and relative unitary
\[
U_Y(V)=I+Y(V-I_2)Y^*,\qquad Y^*Y=I_2,\qquad V\in U(2).
\]
Suppose the active plane contains a coordinate vector \(e_i\), and choose its orthonormal frame as \(Y=(e_i,v)\). This subclass does not require the maximizing-base hypothesis. For every \(V\in U(2)\), there is a phase \(z\), \(|z|=1\), such that
\[
\operatorname{rank}(\operatorname{diag}(z,1)V-I_2)\le1.
\]
If \(V_{22}\ne1\), take
\(z=(V_{22}-1)/(\det V-V_{11})\). The unitary identity \(V_{11}=\det V\,\overline{V_{22}}\) proves \(|z|=1\). If \(V_{22}=1\), the matrix is already diagonal with a rank-at-most-one difference. Lifting this correction is multiplication by a phase on just coordinate \(i\), which commutes with diagonal \(A\) and preserves the determinant support objective. The previously established rank-one relative-unitary MOC theorem therefore proves the coordinate-containing rank-two subclass. This reduction does not require that its base pairing be maximizing.

## 9. The sharp actual common-facet minimum

The new proof in `dual_common_facet_sharp_bound.md` is accepted. In anchored profile coordinates,

\[
f=R_1+S_3-P_{12}+Q_{14}.
\]

For all actual complex \(U(4)\),

\[
\boxed{\min f=-\delta,\qquad
\delta=\frac{t(1-t^2)}4,\quad t^3+t^2+3t-1=0.}
\tag{16}
\]

The cubic has one real root, between \(29/100\) and \(3/10\), and \(\delta<3/40\).

Here are the central reductions independently checked. In quaternion coordinates put
\(X=q_0^2+q_2^2\), \(U=r_0^2+r_2^2\). Exact minimization over four independent circle angles gives

\[
m(X,U)=XU+(1-X)(1-U)
-\sqrt{(X^2+(1-U)^2)((1-X)^2+U^2)}.
\]

The Cauchy bound used in this step is attainable: the two relevant squared circle coordinates range over their full intervals, and their difference covers the required interval. With \(p=X+U-1\), \(d=X-U\), the domain becomes \(|p|+|d|\le1\), and

\[
m=\frac12\left[1+p^2-d^2-
\sqrt{(1+p^2+d^2)^2-4d^2}\right].
\]

Along a ray \((|p|,|d|)=\rho(a,b)\), \(a+b=1\), the expression is concave in \(s=\rho^2\), has zero derivative at zero, and has second derivative
\(-2a^2b^2/(1+2(a^2-b^2)s+(a^2+b^2)^2s^2)^{3/2}\).
It therefore attains its minimum on the diamond boundary; on a coordinate ray it is identically zero, so this includes that degeneracy. All four boundary sides reduce to maximizing
\((1-y)(\sqrt{1+y^2}-1)\). The unique interior critical point obeys
\(2y^3-2y^2+2y-1=0\), giving \(t=2y-1\) and (16).

The displayed rational-in-\(t\) orthogonal attainer is

\[
O(t)=\frac1{\sqrt{t^2+3}}
\begin{pmatrix}
t&1&1&-1\\-1&1&-1&-t\\-1&-1&t&-1\\-1&t&1&1
\end{pmatrix}.
\]

The independent verifier checks its exact cubic equality factor, rather than merely comparing decimal objective values.

The complex extension is valid because this is an anchored linear profile problem in a real three-dimensional complement. Gauge the anchor real and replace each remaining complex row outer product by its real part. The resulting three positive effects have trace one and sum to the identity on that complement. Any extreme such triple has a rank-one effect: if all ranks were at least two, the spaces of symmetric perturbations supported on their ranges would have total dimension at least nine, while the sum and trace equations impose at most eight independent constraints. A nonzero two-sided positive perturbation contradicts extremality. The rank-one trace-one effect is a projection; the remaining two effects are complementary on its two-dimensional orthogonal complement and diagonalize together. Their two-eigenvalue decomposition supplies an orthogonal-frame mixture. Thus every complex anchored profile lies in the real profile convex hull, while the real attainer preserves sharpness.

## 10. The exact 37-dimensional dual moment lift

The complete converse in `dual_outer_profile_geometry.md` was audited, rather than just the membership of one example. Its variables are a symmetric entrywise nonnegative \(W\succeq0\) with \(\mathbf1^TW\mathbf1=1\), \(m=W\mathbf1\), and three pairs \((A_\alpha,Z_\alpha)\) satisfying

\[
A_\alpha\succeq0,\ A_\alpha\mathbf1=0,\
\operatorname{diag}Z_\alpha=\operatorname{diag}A_\alpha,\
Z_\alpha^T\mathbf1=m,
\]

\[
\sum_\alpha A_\alpha=\operatorname{diag}m-W,\qquad
\sum_\alpha Z_\alpha=\mathbf1m^T-W,
\]

\[
\begin{pmatrix}Z_{\alpha,ij}&A_{\alpha,ij}\\
A_{\alpha,ij}&Z_{\alpha,ji}\end{pmatrix}\succeq0.
\tag{17}
\]

The profile projection is \(R_i=\sum_j Z_{R,ij}\),
\(P_{ij}=Z_{R,ij}+Z_{R,ji}-2A_{R,ij}\), and similarly for \(S,Q\).

The affine parametrization has dimension \(9+6+6+8+8=37\). Its explicit strict relative interior point has \(W=(J+2I)/24\), all \(A=(4I-J)/72\), diagonal \(Z=1/24\), and off-diagonal \(Z=5/72\). Every variable is bounded directly: \(W\) has nonnegative entries summing to one, each \(Z\) column is nonnegative with sum at most one, and the positive block inequalities bound every entry of \(A\). Thus this is a compact lift, with no unremoved gauge direction.

Solving the annihilation equations for all 54 primal directions gives exactly (17). Nonzero positive dual tuples always have positive height coefficient: a zero coefficient would force \(W=0\), hence \(m=0\), hence the nonnegative column sums force all \(Z\) and then all \(A\) and remaining blocks to vanish. Thus normalizing the height coefficient to one loses no nonzero dual ray.

For **every** real twenty-coordinate cost \(c\), the optimal height in the full 54-variable certificate is therefore

\[
\boxed{h_{54}(c)=\max_{L\in\mathcal L}c\cdot\Pi(L).}
\tag{18}
\]

The strict relative dual point, compactness, and primal feasibility at sufficiently large height give equality and attainment. The verifier independently rebuilt all 32 dual blocks, checked positivity by exact principal minors, annihilated each of the 54 primal basis directions, and checked all twenty cost basis pairings and the unit height pairing.
## 11. A new exact rank-one-anchor fiber criterion

Suppose a lift point has \(W=pp^T\), where \(p\) is a probability vector, and put \(R^\alpha=Z_\alpha\mathbf1\). Then the entire moment tuple is a convex mixture of actual orthogonal-frame moment tuples if and only if

\[
\boxed{Z_\alpha=R^\alpha p^T\quad\text{for each }\alpha.}
\tag{20}
\]

For necessity, an actual mixture has \(W=\mathbb E(p_\omega p_\omega^T)\) and mean \(m=p\). The covariance is zero, so \(p_\omega=p\) almost surely. The mixed moments then factor as in (20).

For sufficiency, set \(v_i=\sqrt{p_i}\). On positive coordinates define
\(E^\alpha_{ij}=A_{\alpha,ij}/\sqrt{p_ip_j}\). On a coordinate with \(p_i=0\), put \(E^\alpha_{ii}=R^\alpha_i\) and set its newly introduced off-diagonal entries to zero. Each \(E^\alpha\) is positive: the positive-coordinate part is a congruence of a principal submatrix, and the extra part is a nonnegative diagonal matrix. Moreover, positivity of \(A\) and its zero diagonal at a zero \(p_i\) force the original corresponding rows to vanish.

The row-zero equations yield \(E^\alpha v=0\), (20) gives \(\operatorname{tr}E^\alpha=1\), and the two coupling identities give
\(\sum E^\alpha=I-vv^T\), including at zero coordinates. The real three-dimensional purification argument in Section 9 now supplies an orthogonal-frame mixture. With the anchor held fixed, it reproduces exactly the prescribed \(A,Z,W\). This proves (20) without a strictly positive anchor assumption.

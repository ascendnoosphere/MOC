## Round 087 — Prove a universal oriented law for two orthonormal rows

Letu,v be complex orthonormal rows of arbitrary lengthn, and set

\[
q_{ij}=|u_iv_j-u_jv_i|^2,\quad i<j.
\]

**Lemma, proved.** There are nonnegativeλ_ij fori≠j satisfying

\[
\lambda_{ij}+\lambda_{ji}=q_{ij},\quad
\sum_{j\ne i}\lambda_{ij}=|u_i|^2,\quad
\sum_{i\ne j}\lambda_{ij}=|v_j|^2.
\]

This is a fractional orientation of the weighted complete graph. The necessary and sufficient subset-cut condition is that the total required outgoing mass fromS is at least the weight of its internal edges; the complementary cuts give the upper constraints.

Cauchy–Binet verifies every cut:

\[
\sum_{i<j\in S}q_{ij}
=\|u_S\|^2\|v_S\|^2-|\langle u_S,v_S\rangle|^2
\le\|u_S\|^2.
\]

Total edge weight is1. The degree identityΣ_{i≠j}q_ij=|u_j|²+|v_j|² converts the outgoing constraints into the stated incoming ones.

Hence

\[
C_{11}+\det C[12]
=\sum_{i\ne j}\lambda_{ij}\beta_i(1+\beta_j).
\]

The second-row marginal is exactly prescribed. This proves the conditional affine vertex bound for either single CH pencil, for all complex spectra.

## Round 088 — Strengthen the single-pencil bound to full spectral majorization in dimension three

FixM=Re(λT_β)|H andp_j=v_j². Let

\[
a^{(j)}=(\Re[\lambda\beta_i(1+\beta_j)])_{i\ne j}\in\mathbb R^3.
\]

Round087 gives

\[
\lambda_{\max}(M)\le\sum_jp_j\max a^{(j)},\qquad
\lambda_{\min}(M)\ge\sum_jp_j\min a^{(j)}.
\]

Direct tracing yields

\[
\operatorname{tr}M=\sum_jp_j\sum_{i\ne j}
\Re[\lambda\beta_i(1+\beta_j)].
\]

In dimension3 these are precisely all eigenvalue-majorization inequalities:

\[
\boxed{\operatorname{eig}^{\downarrow}(M)
\prec\sum_jp_j(a^{(j)})^\downarrow.}
\]

For example the second partial-sum inequality follows by subtracting the smallest-eigenvalue bound from the exact trace.

**Outcome.** Every weighted real frame objective formed from one pencil is bounded by the corresponding conditional assignment support. This is stronger than bounding one eigenvalue and will close a genuinely joint support stratum in the next round.

## Round 089 — Prove a coupled aligned-support theorem on the unit circle

Assume|β_j|=1 and

\[
\lambda_0p_\beta=\kappa\overline{\lambda_1},
\qquad\kappa\in\mathbb R.
\]

Because T_{1/β}=\overline{T_β}, the two real support matrices satisfyN=κM for everyv. The exact frame objective is the maximum pairing of eig(M) with the weights(1,κ,0), in their appropriate sorted order.

By Round088,

\[
f(M,\kappa M)
\le\sum_jp_j
\max_{\substack{i,k\ne j\\i\ne k}}
\bigl(a_i^{(j)}+\kappa a_k^{(j)}\bigr).
\]

At the actual CH vertices the reciprocal coefficient equalsκa_k^(j), so the right side is exactlyΣ_jp_jh_j, whereh_j is the best permutation support withπ(2)=j. This is at most the global permutation supporth.

**Proved scope.** Every unitaryU∈U(4), every unit-circleβ, and every support direction satisfying the displayed real-alignment condition obey the full CH support inequality. The complex-U case follows from realification. This does not prove every support direction for unit-circleβ, and no extension beyond the stated condition is inferred.


## Round 092 — Prove an all-dimensional binary reduction for a sparse row

SupposeU∈U(n) has a row with at most two nonzero entries. Relabel and gauge so it is row1 supported on columns1,2. Write

\[
U=\operatorname{diag}(1,V)G_{12},
\]

withV∈U(n−1) andG₁₂ a unitary2×2 column rotation. For every minor, Cauchy–Binet has at most one nonzero mixing term: the first row ofdiag(1,V) is a coordinate vector, and all other rows vanish in its column.

Consequently the complete minor profile obeys

\[
\boxed{\mathcal M(U)=
|G_{11}|^2\mathcal M(\operatorname{diag}(1,V))
+|G_{12}|^2\mathcal M(\operatorname{diag}(1,V)S_{12}).}
\]

For minors using both or neither mixed columns, the two endpoint squared minors agree. For a minor using exactly one mixed column, the row1 inclusion determines its sole surviving term and the indicated coefficient.

Thus MOC(n−1) proves MOC(n) for this sparse-row class. In n4, the common law forU3 yields a full common permutation-minor law.

In fixed-row coordinates, support(v)≤2 makesC andG simultaneously diagonal in the basis(v₂e₁−v₁e₂,e₃,e₄). Hence all edges of the outer simplex satisfy the exact joint conditional assignment bound, not merely its vertices. Transposition gives the corresponding sparse-column statement.

## Round 093 — Eliminate the remaining plane rotation exactly

For any real symmetric3×3 M,N, fix the unused frame vectort. The maximum over the orthogonal pair in t⊥ is

\[
\operatorname{tr}(N|_{t^\perp})+
\lambda_{\max}((M-N)|_{t^\perp}).
\]

PutD=M−N,S=M+N. Forunit t this equals

\[
\frac12\left[\operatorname{tr}S-t^TSt+
\sqrt{(\operatorname{tr}D-t^TDt)^2
-4t^T\operatorname{adj}(D)t}\right].
\]

The adjugate term is the determinant of the2D compression. Therefore f(M,N)≤h is equivalent to nonnegativity, for everyt, of both

\[
L_h(t)=(2h-\operatorname{tr}S)\|t\|^2+t^TSt
\]

and the ternary quartic

\[
P_h(t)=
((h-\operatorname{tr}M)\|t\|^2+t^TMt)
((h-\operatorname{tr}N)\|t\|^2+t^TNt)
+\|t\|^2t^T\operatorname{adj}(D)t.
\]

The sign conditionL_h≥0 must accompany the squared inequalityP_h≥0. This gives a precise coupled quartic target without replacing a real plane by an unconstrained complex one.

## Round 094 — Derive an explicit SOS identity for that ternary quartic

Take a rank-one dual certificateY=yyᵀ with PSD slacks

\[
S_0=Y+\alpha I-M,\quad T_0=Y+\beta I-N,
\]

andh=α+β+||y||². Then

\[
L_h(t)=t^T[(\operatorname{tr}S_0+\operatorname{tr}T_0)I
-S_0-T_0+2yy^T]t\ge0.
\]

An exact identity supplies the quartic certificate:

\[
\begin{aligned}
P_h(t)={}&\|t\|^2t^T(\operatorname{adj}S_0+\operatorname{adj}T_0)t\\
&+\|S_0^{1/2}(\|t\|^2I-tt^T)T_0^{1/2}\|_F^2\\
&+(y^Tt)^2t^T[(\operatorname{tr}S_0+\operatorname{tr}T_0)I
-S_0-T_0]t+(y^Tt)^4.
\end{aligned}
\]

Derivation: onunit t, cancel the scalar shiftsα,β inP_h and use the2×2 identity det(T−S)=detT+detS−trTtrS+tr(TS) on t⊥. Homogenize.

All displayed coefficient matrices arePSD whenS₀,T₀ arePSD. An exact integer substitution using noncommuting positive slacks verified the identity with difference0 and value19404. The algebraic derivation, not the substitution, proves it generally.

## Round 095 — Quantify the loss from competing top eigenvectors

LetM have eigenvaluesμ₁≥μ₂≥μ₃ withtop unit vectoru, andN haveν₁≥ν₂≥ν₃ withtop unit vectorv. Seta=μ₁−μ₂,b=ν₁−ν₂. Then

\[
M\preceq\mu_2I+a uu^T,\qquad
N\preceq\nu_2I+b vv^T.
\]

For rank-one objectives the orthogonality loss has an exact formula:

\[
\max_{r\perp s}a(u^Tr)^2+b(v^Ts)^2
=\frac{a+b+\sqrt{(a+b)^2-4ab(u^Tv)^2}}2.
\]

To derive it, fixr and choose s along the projection ofv into r⊥. The objective becomes b+rᵀ(auuᵀ−bvvᵀ)r. The two nonzero eigenvalues of that rank-two matrix give the formula.

Hence f(M,N) is bounded byμ₂+ν₂ plus the displayed expression.

**Use and limitation.** The bound records the actual angle between competing top eigendirections. It becomes the exact assignment collision penalty when the directions coincide. A proof for the reciprocal spectral pair would need to relate this angle to the24 facet gaps; no universal such inequality has been derived.

## Round 096 — Complete the capacity certificate by allowing all14 balanced circuits

Write the capacity objective asΣ_s c_s x^{a_s}, with exponents2e_i for loopsd_i ande_i+e_j for edgese_ij. The balanced-weight polytope is

\[
\lambda_s\ge0,\quad\sum_s\lambda_s=1,\quad
\sum_s\lambda_s a_s=(1/2,1/2,1/2,1/2).
\]

Its extreme supports are exactly:
one four-loop support; six edge-plus-two-loop supports; three opposite-edge pairs; four triangle-plus-loop supports. This follows from the fractional matching classification: a nonintegral connected extreme component is an odd cycle, which on four vertices can only be a triangle.

**Exact allocation theorem.**

\[
\operatorname{cap}(c)=
\max_{\substack{c^{(r)}\ge0\\\sum_r c^{(r)}\le c}}
\sum_{r=1}^{14}K_r(c^{(r)}),
\]

where each c^(r) is supported on circuit r and K_r is the weighted AM–GM value on that minimal balanced support. The four types are

4(∏d)^{1/4}; 2√2√e_ij(d_kd_l)^{1/4};
2√(e_ij e_kl); 4(d_l e_ij e_ik e_jk)^{1/4}.

At a positive-coefficient capacity minimizer, the Gibbs weightsc_sx^{a_s}/cap are balanced. Decompose them into extreme balanced weights and allocate each coefficient proportionally. Every circuit has the same minimizingx, so the sum of its AM–GM values is exactlycap. The converse is AM–GM; zero coefficients follow by continuity and compactness of allocations.

**Outcome.** This is a complete finite circuit allocation formula for capacity. An allocation dominating the actual chirality would prove the isoclinic capacity inequality; such a universal allocation is not established here.

## Round 097 — Derive the exact SOS threshold within the one-chirality quartic family

For

\[
F(q)=\sum_i d_iq_i^4+\sum_{i<j}e_{ij}q_i^2q_j^2
-\chi q_0q_1q_2q_3,
\]

average any quadratic SOS Gram matrix under sign changes with product+1. The quadratic monomials split into four invariant blocks:

(q₀²,q₁²,q₂²,q₃²),
(q₀q₁,q₂q₃),
(q₀q₂,q₁q₃),
(q₀q₃,q₁q₂).

LetQ₀ be the first PSD4×4 block, withdiagQ₀=d. Put

\[
A_{ij}=e_{ij}-2(Q_0)_{ij}.
\]

The other blocks arePSD2×2 matrices with diagonals(A_ij,A_kl). Their three off-diagonal entries must sum to−χ/2. Therefore

\[
\boxed{F\text{ is quadratic SOS}\iff
\exists Q_0\succeq0,\ \operatorname{diag}Q_0=d,\ A_{ij}\ge0,\
|\chi|\le2\!\sum_{\rm opposite}\sqrt{A_{ij}A_{kl}}.}
\]

The interval of achievable summed off-diagonals proves both directions. This is an exact continuous certificate family that includes the loop-edge repairs missed byB.

**Scope.** General one-chirality nonnegative quartics need not be SOS. Equality of this SOS threshold and full capacity on the actual paired spectral slice is unproved; the two criteria must remain distinct.


## Round 099 — Reduce global certification of a stationary frame to one scalar and two2×2 PSD tests

Let(r,s,t) be an orthonormal candidate frame. Stationarity of its objective implies

\[
M_{tr}=0,\quad N_{ts}=0,\quad M_{rs}=N_{rs}=c
\]

in this frame basis. An optimal rank-one dual annihilatest, so writey=xr+zs withxz=c. Its scalar multipliers must be

\[
\alpha=M_{rr}-x^2,\quad\beta=N_{ss}-z^2.
\]

The two remaining PSD slacks reduce exactly to

\[
\begin{pmatrix}
z^2+\alpha-M_{ss}&-M_{st}\\
-M_{st}&\alpha-M_{tt}
\end{pmatrix}\succeq0,
\]

\[
\begin{pmatrix}
x^2+\beta-N_{rr}&-N_{rt}\\
-N_{rt}&\beta-N_{tt}
\end{pmatrix}\succeq0.
\]

Forc≠0, setx²=a>0 andz²=c²/a. Thus global optimality of this stationary frame is equivalent to feasibility of two rational2×2 PSD conditions in one positive scalar. Its dual objective automatically equalsM_rr+N_ss. Forc=0 use the branchesx=0 orz=0, includingy=0.

**Outcome.** This is a complete global certificate for a proposed frame, stronger than a second-order local test. It does not show that a permutation or special frame is always globally maximizing for actual spectral costs.

## Round 100 — The left-isoclinic pair profile is not a permutation marginal

Let \(p=(p_0,p_1,p_2,p_3)\) be real, \(s=p_0^2+p_1^2+p_2^2+p_3^2\), and let \(L(p)\) be the left-isoclinic matrix

\[
\begin{pmatrix}
p_0&-p_1&-p_2&-p_3\\
p_1&p_0&-p_3&p_2\\
p_2&p_3&p_0&-p_1\\
p_3&-p_2&p_1&p_0
\end{pmatrix}.
\]

For \(s>0\), \(O=L(p)/\sqrt s\) lies in \(SO(4)\). The four Klein weights

\[
w(\mathrm{id})=p_0^2/s,\quad
w((1\,2)(3\,4))=p_1^2/s,\quad
w((1\,3)(2\,4))=p_2^2/s,\quad
w((1\,4)(2\,3))=p_3^2/s
\]

reproduce every singleton \(|O_{ij}|^2\). They do not reproduce the pair minors. On the slot \(((0,1),(0,2))\),

\[
\det L(p)[(0,1),(0,2)]=-p_0p_3+p_1p_2,
\]

so the squared minor of \(O\) is \((p_0p_3-p_1p_2)^2/s^2\), while every Klein permutation sends \(\{0,1\}\) to \(\{0,1\}\) or \(\{2,3\}\). The same holds, up to signs and Klein relabeling, for the other off-orbit slots. Complementary pair minors agree up to sign because \(O\) is real orthogonal.

The obstruction is not confined to this four-point set. Let \(y\) be the linear functional on pair-minor coordinates with value \(+1\) on

\[
((0,1),(0,1)),\ ((0,1),(0,3)),\ ((0,1),(1,2)),\ ((0,3),(0,3))
\]

and value \(-1\) on \(((0,2),(0,2))\), and value \(0\) elsewhere. Every permutation scores at most \(1\) under \(y\). The pairing of \(y\) against the squared pair minors of \(O\) is \(Q(p)/s^2\), where

\[
\begin{aligned}
Q(p)={}&p_0^4+2p_0^2p_1^2+2p_0^2p_3^2+4p_0p_1p_2p_3\\
&+p_1^4+2p_1^2p_3^2-p_2^4+p_3^4.
\end{aligned}
\]

Hence

\[
Q(p)-s^2=-2\big((p_0p_2-p_1p_3)^2+p_2^4+p_1^2p_2^2+p_3^2(p_2^2-p_1^2)\big).
\]

The right-hand side is positive for some unit \(p\). Its maximum on \(s=1\) is the unique real root of

\[
4g^3+12g^2+14g-1=0,
\]

approximately \(0.06744224886812295\). The maximizing ratio \(p_2/p_0\) is the unique real root of \(r^3+r^2+3r-1=0\), with \(p_0=p_1=p_3\) and \(p_2=rp_0\). At that point the four Lagrange equations for \(Q-s^2\) on the sphere hold, so the critical point is genuine.

**Outcome.** No probability on \(S_4\), independent of the spectra, reproduces all squared pair minors of a general left-isoclinic matrix. The Birkhoff certificate that proves Marcus–de Oliveira for \(n\le 3\) therefore stops at \(n=4\) already on \(SO(4)\). A proof for left-isoclinic matrices must use weights that depend on the two spectra, or must avoid pair profiles entirely. This does not by itself put \(\det(\mathrm{diag}(a)+O\mathrm{diag}(b)O^T)\) outside the permutation hull.

## Round 101 — Exact Klein defect of a left-isoclinic determinant

Keep \(O=L(p)/\sqrt s\) and the Klein weights of Round 100. Let \(B=O\operatorname{diag}(b)O^T\). The diagonal of \(B\) equals the Klein mixture of the permuted diagonals. Consequently every principal \(1\times1\) minor matches that mixture. Since \(B\) is orthogonally similar to \(\operatorname{diag}(b)\), its determinant and the sums of its principal minors of each order agree with those of \(\operatorname{diag}(b)\). The principal \(3\times3\) minors are the complementary diagonal entries of \(\det(B)B^{-1}\), and \(B^{-1}=O\operatorname{diag}(b^{-1})O^T\) has the same diagonal theorem. Thus only principal \(2\times2\) minors can differ from the Klein prediction.

Write \(\widetilde B=L(p)\operatorname{diag}(b)L(p)^T\), so \(B=\widetilde B/s\). For each pair \(I\), let \(m_I\) be the corresponding principal minor of \(\widetilde B\) and let \(k_I\) be the Klein prediction before dividing by \(s\). Then

\[
\begin{aligned}
m_{01}-sk_{01}
&=(p_0p_3-p_1p_2)^2(b_0-b_3)(b_2-b_1)
+(p_0p_2+p_1p_3)^2(b_0-b_2)(b_3-b_1),\\
m_{02}-sk_{02}
&=(p_0p_3+p_1p_2)^2(b_0-b_3)(b_1-b_2)
+(p_0p_1-p_2p_3)^2(b_0-b_1)(b_3-b_2),\\
m_{03}-sk_{03}
&=(p_0p_2-p_1p_3)^2(b_0-b_2)(b_1-b_3)
+(p_0p_1+p_2p_3)^2(b_0-b_1)(b_2-b_3).
\end{aligned}
\]

The complementary pairs repeat these three defects: \(m_{23}-sk_{23}=m_{01}-sk_{01}\), and likewise for the other two partitions. Dividing by \(s^2\) gives the defect of \(B\). Therefore

\[
\det(\operatorname{diag}(a)+B)-\sum_{k=0}^3\frac{p_k^2}{s}\prod_{i=0}^3(a_i+b_{\pi_k(i)})
=s^{-2}\sum_{|I|=2}\Big(\prod_{i\notin I}a_i\Big)(m_I-sk_I),
\]

where \(\pi_0=\mathrm{id}\), \(\pi_1=(1\,2)(3\,4)\), \(\pi_2=(1\,3)(2\,4)\), and \(\pi_3=(1\,4)(2\,3)\), written in zero-based index form as \((0)(1)(2)(3)\), \((1\,0\,3\,2)\), \((2\,3\,0\,1)\), and \((3\,2\,1\,0)\).

**Outcome.** The left-isoclinic determinant differs from its Klein combination by an explicit quadratic form in the eigenvalue gaps \((b_i-b_j)\), with coefficients bilinear in the complementary \(a\)-products and quadratic in the six quaternion cross terms. The difference vanishes when \(b\) is constant on the support of a cross term, and in particular when all \(b_i\) are equal. It is not a sum of permutation products with nonnegative spectrum-independent weights. Whether spectrum-dependent weights can absorb this quadratic form remains open.

## Round 102 — Closed form for a left-isoclinic determinant

Let \(s=p_0^2+p_1^2+p_2^2+p_3^2>0\), \(O=L(p)/\sqrt s\), and \(B=O\operatorname{diag}(b)O^T\). Let \(Z\) be the Klein combination with weights \(p_k^2/s\). Write

\[
\begin{aligned}
U_1&=(a_0-a_2)(a_1-a_3),&
U_2&=(a_0-a_1)(a_2-a_3),\\
V_1&=(b_0-b_2)(b_1-b_3),&
V_2&=(b_0-b_1)(b_2-b_3),
\end{aligned}
\]

and

\[
\begin{aligned}
H_{11}&=-(p_0^2+p_1^2)(p_2^2+p_3^2),&
H_{12}&=(p_0p_3-p_1p_2)^2,\\
H_{21}&=(p_0p_3+p_1p_2)^2,&
H_{22}&=-(p_0^2+p_2^2)(p_1^2+p_3^2).
\end{aligned}
\]

Then, for every complex \(a,b\),

\[
\det(\operatorname{diag}(a)+B)-Z=s^{-2}(H_{11}U_1V_1+H_{12}U_1V_2+H_{21}U_2V_1+H_{22}U_2V_2).
\]

The same correction equals \(s^{-2}S(a)^\top\Gamma(p)T(b)\), where \(S_1=a_0a_1+a_2a_3\), \(S_2=a_0a_2+a_1a_3\), \(S_3=a_0a_3+a_1a_2\), the vector \(T\) is the same form in \(b\), and

\[
\Gamma=\begin{pmatrix}
H_{11}&H_{12}&(p_0p_2+p_1p_3)^2\\
H_{21}&H_{22}&(p_0p_1-p_2p_3)^2\\
(p_0p_2-p_1p_3)^2&(p_0p_1+p_2p_3)^2&-(p_0^2+p_3^2)(p_1^2+p_2^2)
\end{pmatrix}.
\]

Every row and every column of \(\Gamma\) sums to \(0\).

The identity is a polynomial identity, not a sphere-only numerical fit. The principal-minor expansion reduces it to three checks. Diagonals of \(L\operatorname{diag}(b)L^T\) match the Klein prediction exactly. Each principal \(3\times3\) minor equals \(s^2\) times its Klein prediction. Each principal \(2\times2\) defect equals the bilinear form of Round 101, complementary pairs have equal defects, and the resulting degree-\((2,2)\) form factors as the displayed combination of \(U_iV_j\).

The four alternants

\[
\begin{aligned}
U_2V_2&=z_{\mathrm{id}}-z_{(0\,1)}-z_{(2\,3)}+z_{(0\,1)(2\,3)},\\
U_1V_1&=z_{\mathrm{id}}-z_{(0\,2)}-z_{(1\,3)}+z_{(0\,2)(1\,3)},\\
U_1V_2&=z_{(1,3,0,2)}-z_{(1,2,0,3)}-z_{(0,3,1,2)}+z_{(0,2,1,3)},\\
U_2V_1&=z_{(2,0,3,1)}-z_{(2,0,1,3)}-z_{(0,2,3,1)}+z_{(0,2,1,3)}
\end{aligned}
\]

factor as differences of pair products. Substituting them writes the determinant as an affine combination of permutation products. The coefficients sum to \(1\) on \(s=1\), but \(-(p_0p_3\pm p_1p_2)^2\) occurs on four \(3\)-cycles, so the combination is not convex. A constant-coefficient syzygy cannot repair the signs: the relations among the twenty-four products form a fixed \(10\)-dimensional space, and a nonnegative correction in that space would be a spectrum-independent probability, contradicting Round 100.

In Hopf coordinates \(p=(r\cos\alpha,r\sin\alpha,t\cos\beta,t\sin\beta)\), the pure sectors factor:

\[
\begin{aligned}
r^4C_r&=\big(\cos^2\alpha\,(a_0+b_0)(a_1+b_1)+\sin^2\alpha\,(a_0+b_1)(a_1+b_0)\big)\\
&\qquad\times\big(\cos^2\alpha\,(a_2+b_2)(a_3+b_3)+\sin^2\alpha\,(a_2+b_3)(a_3+b_2)\big),\\
t^4C_t&=\big(\cos^2\beta\,(a_0+b_2)(a_1+b_3)+\sin^2\beta\,(a_0+b_3)(a_1+b_2)\big)\\
&\qquad\times\big(\cos^2\beta\,(a_2+b_0)(a_3+b_1)+\sin^2\beta\,(a_2+b_1)(a_3+b_0)\big).
\end{aligned}
\]

Each factor is a convex combination of two pair products, so each sector lies in the permutation hull. At \(t=0\) this is the whole determinant, and the block-diagonal case is settled. The cross mass \(2r^2t^2\) is not absorbed by these two products.

**Outcome.** A left-isoclinic determinant is the Klein combination plus an explicit rank-at-most-two correction in the three pair-partition coordinates. The block-diagonal subcase lies in the permutation hull. The general left-isoclinic hull, and hence unrestricted \(4\times4\) Marcus–de Oliveira, remains open. Any remaining weights must depend on both spectra.

## Round 103 — Convex combination when one quaternion coordinate vanishes

Let \(p=(p_0,p_1,p_2,0)\) be a unit quaternion, so \(p_0^2+p_1^2+p_2^2=1\), and let \(L(p)\) be the corresponding left-isoclinic matrix. Write \(z_\pi=\prod_{i=0}^3(a_i+b_{\pi(i)})\). Then, for all complex \(a,b\),

\[
\begin{aligned}
\det(\operatorname{diag}(a)+L(p)\operatorname{diag}(b)L(p)^T)
&=p_0^4 z_{(0,1,2,3)}+p_0^2p_1^2 z_{(0,1,3,2)}+p_0^2p_1^2 z_{(1,0,2,3)}+p_1^4 z_{(1,0,3,2)}\\
&\quad+p_0^2p_2^2 z_{(0,3,2,1)}+p_0^2p_2^2 z_{(2,1,0,3)}\\
&\quad+p_1^2p_2^2 z_{(1,3,0,2)}+p_1^2p_2^2 z_{(2,0,3,1)}+p_2^4 z_{(2,3,0,1)}.
\end{aligned}
\]

Every coefficient is nonnegative and the nine coefficients sum to \(1\). Thus the determinant lies in the permutation-product convex hull. The same identity holds for a non-unit \(p\) with fourth coordinate \(0\) after dividing every coefficient by \((p_0^2+p_1^2+p_2^2)^2\), because both sides are homogeneous of degree \(0\) in \(p\) once \(L(p)\) is normalized.

The proof is the Round 102 expansion plus two polynomial syzygies. Substituting the four alternants into the closed form gives an affine combination whose coefficients, at \(p_3=0\), are nonnegative except

\[
\begin{aligned}
z_{(0,2,3,1)},\ z_{(0,3,1,2)},\ z_{(1,2,0,3)},\ z_{(2,0,1,3)}
&\quad\text{each }-p_1^2p_2^2,\\
z_{(0,1,2,3)}&\quad p_0^4-2p_1^2p_2^2.
\end{aligned}
\]

The following two identities hold for all complex \(a,b\):

\[
\begin{aligned}
0&=-z_{(0,1,2,3)}+z_{(0,1,3,2)}+z_{(0,2,1,3)}-z_{(0,2,3,1)}-z_{(0,3,1,2)}+z_{(0,3,2,1)},\\
0&=-z_{(0,1,2,3)}+z_{(0,2,1,3)}+z_{(1,0,2,3)}-z_{(1,2,0,3)}-z_{(2,0,1,3)}+z_{(2,1,0,3)}.
\end{aligned}
\]

Adding \(p_1^2p_2^2\) times each identity clears the four negative coefficients and replaces \(p_0^4-2p_1^2p_2^2\) by \(p_0^4\). The other affected coefficients remain nonnegative: \(p_0^2p_1^2\), \(p_0^2p_2^2\), and \(p_1^4\). Their sum is \((p_0^2+p_1^2+p_2^2)^2\).

Setting \(p_2=0\) recovers the block-diagonal product of Round 102. The case \(p_3=0\) is strictly larger: \(p=(1,1,1,0)/\sqrt3\) is not block diagonal.

**Outcome.** Left-isoclinic matrices with a vanishing quaternion coordinate satisfy Marcus–de Oliveira for every complex spectrum. The same syzygy correction does not stay nonnegative when all four coordinates are nonzero, in agreement with Round 100. The unrestricted left-isoclinic case remains open.


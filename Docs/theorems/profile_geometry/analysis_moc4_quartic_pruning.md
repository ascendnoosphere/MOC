# Unrestricted MOC4: a quartic proof architecture with certified pruning

**Status.** The reductions and pruning lemmas below are proved. They do **not** prove the remaining universal quartic inequality. The four contact branches are exhaustive branches of the unrestricted problem, not four proposed special cases. Classical quartic invariants and interval SOS are used without a novelty claim. Existing canonical and reflection-average results are explicitly identified rather than claimed anew.

Notation and the full-unitary coefficient identities come from [analysis_full_cayley_quartic.md](analysis_full_cayley_quartic.md). Put
\[
 z_\pi=\prod_i(a_i+b_{\pi(i)}),\quad
 F(U)=\Re\{\eta\det(D_a+UD_bU^*)\},\quad
 h=\max_\pi\Re(\eta z_\pi).
\]
After relabeling a maximizing permutation to identity,
\(\delta_\pi=h-\Re(\eta z_\pi)\ge0\) and \(\delta_{\rm id}=0\).
For Hermitian \(H\), let
\[
 U_t=(I+itH)(I-itH)^{-1},\quad d_H(t)=\det(I+t^2H^2),
\]
\[
 d_H(t)[h-F(U_t)]=t^2Q_H(t),\qquad
 Q_H(t)=A+Bt+Ct^2+Dt^3+Et^4.
\tag{1}
\]
In particular,
\[
 A=4\sum_{i<j}\delta_{(ij)}|H_{ij}|^2,\qquad
 E=4\sum_{i<j}\delta_{(ij)}|\operatorname{adj}(H)_{ij}|^2.
\tag{2}
\]

## 1. Two valid support reductions — do not conflate them

**Dense strict-support route.** It suffices to prove the inequality for spectra and directions with identity uniquely maximizing and all nonidentity gaps positive; continuity gives the rest. This was proved in [GENERIC_STRICT_SUPPORT_REDUCTION.md](../../research/GENERIC_STRICT_SUPPORT_REDUCTION.md).

**Edge route.** For a fixed nondegenerate polygon \(\operatorname{conv}\{z_\pi\}\), it suffices to prove its finitely many edge support inequalities. This is elementary intersection-of-half-planes geometry. A point outside the polygon violates at least one of those inequalities.

Generically, the products are distinct and no three are collinear. These conditions are dense: differences of distinct products are nonzero polynomials. Three distinct product polynomials cannot be identically collinear over the reals, because a holomorphic ratio taking only real values on an open set is constant, and three distinct vertices of their 0–1 monomial coefficient vectors cannot be collinear. Thus the collinearity loci are proper real-algebraic sets. Limits cover all excluded spectra and degenerate polygons.

At a generic edge there are exactly two active permutations. Relabel one to identity and conjugate the remaining relative permutation by a simultaneous row/column relabeling. The only possible cycle types are
\[
\boxed{(12),\quad(12)(34),\quad(123),\quad(1234).}
\tag{3}
\]
The edge route therefore has precisely four exhaustive branch types, with
\[
 \delta_{\rm id}=\delta_\sigma=0,\qquad
 \delta_\tau>0\quad(\tau\notin\{{\rm id},\sigma\}).
\tag{4}
\]
The strict-support lower bounds below cannot simply be carried into (4), where a nonidentity gap is zero. Section 4 supplies the appropriate edge-specific replacement.

## 2. A compact, fully complex canonical Cayley domain

The following existing canonical reduction is recorded in
`docs/full_text/MOC_Complete_Standalone_Volume(1).txt:17845–17925`.
Here is the proof in the sign convention of (1).

Maximize \(|\det(I+LU)|\) over diagonal unitaries \(L\), and write \(V=LU\) at a maximum. The maximum is positive: the determinant's Fourier polynomial has constant coefficient 1 and cannot vanish identically. Hence \(I+V\) is invertible and
\[
 H=-i(V-I)(V+I)^{-1}=H^*.
\]
For \(E_\theta=\operatorname{diag}(e^{2i\theta_j})\),
\[
 \frac{\det(I+E_\theta V)}{\det(I+V)}
 =e^{i\sum\theta_j}
 \det\{\operatorname{diag}(\cos\theta_j)
       -\operatorname{diag}(\sin\theta_j)H\}.
\]
Maximality bounds the absolute value by 1. Differentiation at zero gives \(H_{ii}=0\). Setting \(t_j=\tan\theta_j\), and allowing both signs, gives
\[
\boxed{
 H_{ii}=0,\qquad
 \det(I+TH)^2\le\prod_j(1+t_j^2)
 \quad\text{for every real diagonal }T.
}
\tag{5}
\]
The determinant on the left is real, by its principal-minor expansion. Two-coordinate specializations give \(|H_{ij}|\le1\), so \(\|H\|_{\rm op}\le3\).

Left diagonal phases preserve \(F\), because they commute with \(D_a\); right diagonal phases also preserve \(F\), because they commute with \(D_b\). Thus (5) loses **no** relevant unitary.

Diagonal conjugation of \(H\) preserves (5) and \(F\). It can make \(H_{12},H_{13},H_{14}\) nonnegative real, including when some are zero. We are left with three real entries and three complex entries: **nine real coordinates, not a real-orthogonal restriction**.

The canonical condition must not be replaced by entry bounds alone. An exact version using only two free real variables is as follows. Put
\(p_{ij}=|H_{ij}|^2\), \(c_{ijk}=\det H[ijk]\), \(d=\det H\), and
\[
\begin{aligned}
 a_0&=1-p_{12}xy,\\
 b_0&=-p_{13}x-p_{23}y+c_{123}xy,\\
 c_0&=-p_{14}x-p_{24}y+c_{124}xy,\\
 e_0&=-p_{34}+c_{134}x+c_{234}y+dxy.
\end{aligned}
\]
Then (5) is equivalent to
\[
 \begin{pmatrix}a_0&c_0\\b_0&e_0\end{pmatrix}
 \begin{pmatrix}a_0&b_0\\c_0&e_0\end{pmatrix}
 \preceq(1+x^2)(1+y^2)I_2\quad\forall x,y\in\mathbb R.
\tag{6}
\]
Indeed the four-variable determinant is
\((1,z)\left(\begin{smallmatrix}a_0&c_0\\b_0&e_0\end{smallmatrix}\right)(1,w)^T\); maximizing over the normalized real vectors \((1,z),(1,w)\) gives its operator norm.

A useful sufficient condition, not an equivalence, is
\[
 H_{ii}=0,\qquad\sum_{j\ne i}|H_{ij}|^2\le1\quad\forall i.
\tag{7}
\]
Hadamard's determinant inequality proves (5), since the squared norm of row i of \(I+TH\) is at most \(1+t_i^2\).

Two other phase gauges are valid but must not be merged without proof: a largest-eigenangle-gap gauge gives \(\|H\|\le1+\sqrt2\); generically, selecting an eigenphase gives a singular generator of rank at most three. Neither assertion says the same representative has both properties or satisfies (5).

### A simpler compact domain for the all-real-t proof

For the stronger global quartic approach, the full canonical condition can be replaced by
\[
\boxed{H=H^*,\quad H_{ii}=0,\quad\|H\|_F=1,\quad t\in\mathbb R.}
\tag{7a}
\]
This is another **exact reduction of unrestricted MOC4**, not a sufficient test on a prescribed restricted family. Given the canonical H above, divide it by its nonzero Frobenius norm and absorb that norm into t. H=0 is the commuting equality. Conversely full MOC applies to every such Cayley curve. Every generator in (7a) satisfies (7) automatically.

After diagonal conjugation, (7a) has eight real direction parameters; t supplies the ninth parameter. The distinction is important: (7a) requires positivity for all real t, whereas the compact canonical-domain route only needs t in [-1,1]. One cannot combine the normalized sphere with the shorter interval and still assert full coverage.

## 3. A closed even-part bound, with a strict quantitative margin

We use the previously proved [reflection-average SOS](../../research/REFLECTION_AVERAGE_SOS.md):
\[
 \frac{F(U)+F(U^*)}{2}\le h
\tag{8}
\]
whenever identity maximizes the permutation values. Its established scope includes arbitrary real linear combinations of squared compound minors, not only spectral determinant costs. This extra scope will be used only for the even part.

Since \(U_{-t}=U_t^*\), (1) and (8) give
\[
 A+Ct^2+Et^4\ge0\quad\forall t\in\mathbb R.
\]
Consequently
\[
\boxed{C\ge-2\sqrt{AE}.}
\tag{9}
\]
This really is a universal middle-coefficient lower bound. It does not control B and D.

For strict-support data define
\[
 r(U)=\sum_{i\ne j}|U_{ij}|^2,\qquad
 \kappa=\min_{\pi\ne\mathrm{id}}
 \frac{\delta_\pi}{4-\#\operatorname{Fix}(\pi)}>0.
\]
The modified compound cost \(F+\kappa r\) still has identity as a permutation maximizer. Applying (8) to it proves
\[
 h-\frac{F(U)+F(U^*)}{2}\ge\kappa r(U).
\tag{10}
\]
This does not assert that the modified cost comes from spectra; the even theorem explicitly permits it.

Let \(\rho=\|H\|_{\rm op}\) and \(H_{\rm off}\) be H with its diagonal removed. For real \(t\ne0\), commutation with the coordinate projections and
\[
 H=\frac1{it}\{I-2(U_t+I)^{-1}\}
\]
give
\[
 r(U_t)\ge
 \frac{4t^2}{(1+t^2\rho^2)^2}\|H_{\rm off}\|_F^2.
\tag{11}
\]
For example, use
\([P,H]=\frac2{it}(U_t+I)^{-1}[P,U_t](U_t+I)^{-1}\),
\(\|(U_t+I)^{-1}\|^2=(1+t^2\rho^2)/4\), and sum the squared Frobenius inequalities over coordinate projections.

For A,E>0, set \(t_0=(A/E)^{1/4}\). Equations (10)–(11) yield
\[
\boxed{
 C+2\sqrt{AE}\ge
 \frac{4\kappa d_H(t_0)}{t_0^2(1+t_0^2\rho^2)^2}
 \|H_{\rm off}\|_F^2>0.
}
\tag{12}
\]
The strict inequality holds for nondiagonal H. This prunes the zero-even-budget boundary on the strict-support route.

## 4. Edge-sensitive pruning: the zero-even-budget boundary is settled

Now use the exhaustive edge route (4). Let
\[
 \mathcal S_\sigma=\{(i,i),(i,\sigma(i)):1\le i\le4\},\qquad
 p_\sigma(U)=\sum_{(i,j)\notin\mathcal S_\sigma}|U_{ij}|^2.
\]
Our permutation-matrix convention places its nonzero entries at \((i,\pi(i))\); reversing this convention just replaces \(\sigma\) by its inverse.

Put
\[
 \kappa_\sigma=
 \min_{\tau:p_\sigma(P_\tau)>0}
 \frac{\delta_\tau}{p_\sigma(P_\tau)}>0.
\]
All active permutations have zero penalty; any permutation with positive penalty is inactive. Applying (8) to \(F+\kappa_\sigma p_\sigma\) gives the proved inequality
\[
\boxed{
 h-\frac{F(U)+F(U^*)}{2}
 \ge\frac{\kappa_\sigma}{2}
       \{p_\sigma(U)+p_\sigma(U^*)\}.
}
\tag{13}
\]
It follows that zero even gap forces U to have support inside
\(\mathcal S_\sigma\cap\mathcal S_\sigma^T\).

| Relative edge permutation | Forced U when the even gap is zero |
|---|---|
| (12) | a 2-by-2 block on 12 and diagonal entries on 3,4 |
| (12)(34) | a 2-by-2 block on 12 and a 2-by-2 block on 34 |
| (123) | diagonal |
| (1234) | diagonal |

The last two claims follow because a directed cycle of length at least three shares no off-diagonal edge with its reverse. In those branches the right side of (13) is at least \(\kappa_\sigma r(U)/2\).

Every configuration in this table already satisfies MOC, by the elementary 2-by-2 Birkhoff formula and direct sums. More strongly, for those 2-by-2 block configurations \(F(U)=F(U^*)\), so the even inequality itself proves the individual support inequality.

**Consequent quartic pruning.** Suppose A,E>0 and equality holds in (9). At \(t_0=(A/E)^{1/4}\) the even gap is zero. The table forces \(U_{t_0}\) to be block diagonal with blocks of size at most two. The inverse Cayley map makes H block diagonal with the same blocks. Then \(F(U_t)=F(U_t^*)\) for every t, hence
\[
\boxed{B=D=0,\qquad Q_H(t)=(\sqrt A-\sqrt E\,t^2)^2\ge0.}
\tag{14}
\]
For the global quartic route, the other endpoint degeneracies can also be removed rigorously, rather than assumed away:

- If A=0, every nonzero off-diagonal entry of H must be on a zero-gap transposition. On a generic edge of type (12), this confines H to the 12 block, so its support gap is identically zero. On the other three edge types all transposition gaps are positive, and A=0 forces the zero-diagonal H to be zero.
- Invertible zero-diagonal Hermitian matrices are dense on the sphere (7a). Explicitly, let K be the real symmetric permutation matrix (12)(34), with det K=1 and zero diagonal. The polynomial det(H+epsilon K) has leading coefficient 1, hence only finitely many roots. Choose nonzero epsilon tending to zero outside those roots and normalize H+epsilon K to Frobenius norm one. The resulting invertible zero-diagonal Hermitian matrices converge to H.
- For an invertible zero-diagonal H, E cannot vanish on a generic edge. In the last three edge types, E=0 would make adj(H) diagonal, hence H diagonal, an impossibility. In the transposition type it would make adj(H), and hence H, a 12 block plus two scalar blocks; zero diagonal would make those scalar blocks zero, again contradicting invertibility.

It therefore suffices to prove the all-real-t quartic inequality on the dense invertible sphere. Polynomial continuity then handles singular generators. Combined with (14), the genuinely coupled target on all four branches is
\[
\boxed{A,E>0,\qquad C>-2\sqrt{AE}.}
\tag{15}
\]
This is a reduction, not an independent positivity proof for the singular cases: their conclusion is obtained only after proving the remaining dense target. The canonical interval formulation below instead keeps all degeneracies in its undivided coefficient equations.

## 5. Replace scalar guessing by at most three explicit tests

For a general real quartic with A,E>0, let
\[
 G(u)=\begin{pmatrix}A&B/2&u\\B/2&C-2u&D/2\\u&D/2&E\end{pmatrix},
 \quad r=\sqrt{AE},
\]
\[
 I=C^2-3BD+12AE,\qquad
 J=72ACE+9BCD-27AD^2-27EB^2-2C^3.
\tag{16}
\]
These are the classical binary-quartic invariants in this coefficient convention. Direct expansion gives
\[
 f(u):=\det G(u)
 =2u^3-Cu^2+(BD/2-2AE)u+AEC-(EB^2+AD^2)/4,
\]
\[
\boxed{108f(u)=(6u-C)^3-3I(6u-C)+J.}
\tag{17}
\]
For \(|u|<r\), the A,E corner is positive definite. Its Schur complement shows that \(G(u)\succeq0\) iff \(f(u)\ge0\).
At the endpoints, \(f(-r),f(r)\le0\). The only possible interior local maximum is
\[
 u_*=(C-\sqrt I)/6,\qquad
 f(u_*)=(J+2I^{3/2})/108.
\]
Therefore a PSD Gram exists **if and only if at least one** of the following tests succeeds:

1. **Interior:**
   \[
   I>0,\quad-r<u_*<r,\quad J+2I^{3/2}\ge0.
   \tag{18}
   \]
2. **Endpoint:** for u=r or u=-r,
   \[
   D=(u/A)B,\qquad C-2u\ge B^2/(4A).
   \tag{19}
   \]

To justify necessity of the interior candidate, if some interior u has f(u)>=0, a maximum over [-r,r] is attained at an interior local maximum unless feasibility is already at an endpoint. If the maximum is zero at an interior point, it is still a local maximum. When I<=0 the derivative has no such local maximum (the I=0 stationary point is an inflection). This proves the exhaustive list. Formula (19) is the range and pseudoinverse Schur-complement condition for a rank-one corner.

**Cheap pruning before the determinant test.** Every feasible u must lie in
\[
 -r\le u\le
 \min\left\{r,\ C/2-B^2/(8A),\ C/2-D^2/(8E)\right\}.
\tag{20}
\]
This follows from the two 2-by-2 principal minors involving the middle row. In particular, necessary odd-budget bounds are
\[
 B^2\le4A(C+2r),\qquad D^2\le4E(C+2r).
\tag{21}
\]
If J>=0, the last inequality in (18) is automatic. If J<0, it is equivalent to the polynomial test \(4I^3-J^2\ge0\).

Equations (18)–(21) are proved algebraic tests, **not proved universal spectral inequalities**. A full all-real-t quartic proof can now target these finite tests instead of guessing u or optimizing it numerically.

## 6. A weaker, exact certificate on the canonical interval

The canonical set (5) is star-shaped: if H is canonical and |s|<=1, then
\[
 \det(I+T(sH))^2\le\prod_i(1+s^2t_i^2)\le\prod_i(1+t_i^2).
\]
To prove unrestricted MOC4, it is enough to prove Q_H>=0 on [-1,1] for canonical H. The forward direction follows from MOC for all U_t; the reverse direction uses t=1 and the complete canonical coverage.

A real quartic is nonnegative on [-1,1] iff it has the interval SOS
\[
 Q(t)=v_2(t)^TGv_2(t)+(1-t^2)v_1(t)^TWv_1(t),
 \quad G\succeq0,\ W\succeq0,
\tag{22}
\]
where \(v_2=(1,t,t^2)^T\), \(v_1=(1,t)^T\). This is the quartic Markov–Lukács theorem. Here is a direct proof. The polynomial
\(P(x)=(1+x)^4Q((1-x)/(1+x))\) is nonnegative on x>=0. Factor it over the reals. Positive roots have even multiplicity; nonpositive linear factors and positive irreducible quadratics each have the form a(x)^2+x b(x)^2. For a quadratic x^2+2cx+d use
\((x-\sqrt d)^2+2(c+\sqrt d)x\). Products preserve this form by
\[
 (a^2+xb^2)(c^2+xd^2)=(ac-xbd)^2+x(ad+bc)^2.
\]
The highest-degree terms of a^2 and x b^2 have opposite parity, so they cannot cancel. Thus deg P<=4 gives deg a<=2, deg b<=1. Substitution back explicitly gives
\[
 q(t)=\frac{(1+t)^2}{4}a\!\left(\frac{1-t}{1+t}\right),\qquad
 \ell(t)=\frac{1+t}{4}b\!\left(\frac{1-t}{1+t}\right),
\]
which are polynomials of degrees at most two and one. Consequently
\(Q=q^2+(1-t^2)\ell^2\), giving (22) even with each Gram of rank at most one. The polynomial identity extends to t=-1; P identically zero is immediate. The converse is immediate.

Coefficient matching leaves four free scalars r_0,s_0,v_0,u:
\[
 W=\begin{pmatrix}r_0&s_0\\s_0&v_0\end{pmatrix},\quad
 G=\begin{pmatrix}
 A-r_0&B/2-s_0&u\\
 B/2-s_0&C-v_0+r_0-2u&D/2+s_0\\
 u&D/2+s_0&E+v_0
 \end{pmatrix}.
\tag{23}
\]
This is a genuinely less restrictive certificate for an individual quartic than global nonnegativity. It is nevertheless **equivalent to full MOC4 when required on the complete canonical domain**. It does not remove the odd terms: it gives them a larger, precisely specified certificate space. The remaining task is to construct (23) from actual spectral products and (5), or to prove the stronger tests (18)–(19).

## 7. Canonical pruning does not repair u=-T: exact obstruction

Let
\[
 a=(-1,-2,-1,2),\qquad b=(1,0,-1,0),\qquad\eta=1,
\]
\[
 H_0=\begin{pmatrix}
 0&-1-i&1-i&1\\
 -1+i&0&-2&0\\
 1+i&-2&0&-1+i\\
 1&0&-1-i&0
 \end{pmatrix}.
\]
Identity is maximizing with h=0. Exact coefficient extraction gives
\[
 (A,B,C,D,E)=(80,64,576,1024,3584).
\]
With
\(T=4\sum_{i<j}\delta_{(ij)}\Re(\overline{H_{ij}}\operatorname{adj}(H)_{ij})\),
\[
 T(H_0)=512,\qquad \det G(-T)=-2097152<0.
\tag{24}
\]
But G(0) is positive definite, with leading principal minors
\[
 80,\quad45056,\quad140509184.
\]
This is not a MOC counterexample.

Crucially, H=H_0/3 **is canonical**, not just traceless: the squared row norms of H_0 are 5,6,8,3, so (7) applies to H_0/3. Under H_0->sH_0,
\[
 (A,B,C,D,E,T)\mapsto(s^2A,s^3B,s^4C,s^5D,s^6E,s^4T),
\]
and G(-T) undergoes congruence by diag(s,s^2,s^3). Its determinant stays negative. Since \(\|H_0\|_F^2=22\), the alternative scaling \(H_0/\sqrt{22}\) puts the same obstruction on the normalized sphere (7a). Thus zero diagonal, bounded entries, and the full canonical maximality condition do not rescue this fixed prescription.

The witness was found in a bounded 386-instance near-real stress test, then rounded and verified with exact Gaussian integers. Those searches are not proof of any positive statement.

## 8. An explicit commuting-tube cutoff on the strict-support route

Normalize |a_i|,|b_j|<=1 and |eta|=1, and suppose all nonidentity gaps are at least m>0. For canonical H, put rho=||H||op. Since its diagonal is zero,
\[
 A\ge2m\|H\|_F^2\ge2m\rho^2.
\]
In the cleared determinant, the column norms of the constant, linear and quadratic matrix coefficients are bounded by 2,4rho,2rho^2. Multilinearity and Hadamard's inequality majorize its coefficient of degree k by
\(16\binom8k\rho^k\). The support denominator contributes at most
\(16\binom4{k/2}\rho^k\) for even k. Therefore
\[
 |B|\le896\rho^3,\quad |C|\le1216\rho^4,\quad |D|\le896\rho^5.
\]
Using E>=0 and rho<=1,
\[
 Q_H(1)\ge\rho^2(2m-3008\rho).
\]
Thus
\[
\boxed{0<\|H\|_{\rm op}<m/1504\ \Longrightarrow\ h-F(U_1)>0.}
\tag{25}
\]
Because m<=32 under the normalization, this cutoff lies below 1. H=0 is the commuting equality. This is a certified neighborhood exclusion, not evidence from a local optimizer.

For each fixed lower gap bound m, the unresolved canonical parameters can consequently be restricted to a compact annulus. As m decreases these annuli exhaust the generic strict-support problem. This does not assert a uniform positive margin on the annulus, a finite certificate for all m, or guaranteed termination of subdivision.

## 9. What a complete proof must still supply

The proved architecture is:

1. Normalize the spectra; use either the dense strict-support route or the exhaustive four-edge route.
2. Use either the nine-real-coordinate canonical domain with (5)/(6) and |t|<=1, or the normalized zero-diagonal sphere (7a) with all real t. These are separate complete routes.
3. Use the even SOS and (13) to remove zero-even-energy nonreducing configurations. On the global quartic edge route, use the proved density reduction to reach (15). On the strict canonical route, also remove the explicit commuting tube (25).
4. For every remaining input, prove the interval Gram feasibility (23), or the global three-candidate conditions (18)–(19).
5. Pass to degenerate spectra/support directions by continuity.

**The missing implication is step 4.** In particular, (9) and positivity of its margin do not imply either (21) or (18). Calling the surviving odd coupling a contraction without proving its norm at most one would simply assume MOC.

A subsequent direct attempt proves [joint odd-coefficient bounds](analysis_moc4_joint_odd_budget.md): a Segre-conditioned covariance inequality for (B,D), an exact four-breakpoint support function for its stated triangle-budget relaxation, and B²≤AS on the normalized Hermitian sphere, with D²≤ES also on the real skew specialization. Here S=2∑δ_(ij). It also derives the exact middle-coefficient identity C=4C₀+8p∑(2dᵢ−Sᵢ)rᵢ−16P for every real skew 4×4 generator, retaining the full-rank Pfaffian term. The same note composes the existing realification and contact-transfer theorems, so a terminal proof on real mixers with at least six distinct supporting products would suffice. These are stronger usable constraints, not a completion of step 4: domination by the actual even energy is still unproved.

A separate first-contact pruning result is also valid: at a spectral pair already satisfying *all* MOC support inequalities, a nonzero uniquely exposed permutation vertex can only be attained by a commuting pair. Equality at that vertex makes the same U maximize an open interval of support directions; the adjugate stationarity equation for two non-collinear multipliers gives [D_b^U,adj(D_a+D_b^U)]=0. Distinct spectra and a nonzero determinant then force D_b^U diagonal. The positive transverse quadratic form prevents nearby violations from emerging there. A first-contact proof must therefore confront tied faces or singular limits. It cannot assume that spectral first derivatives vanish merely because a Cayley quartic has a double root.

Exact checks: `code/research/verify_quartic_pruning.py`, with output in `build/direct_attack/quartic_pruning_exact_checks.json`. The checks validate identities and the obstruction, not the universal feasibility required in step 4.

A bounded seeded census of 128 complex spectral pairs found 704 transposition edges, 84 double-transposition edges, 127 three-cycle edges and 66 four-cycle edges (`build/direct_attack/quartic_edge_census.json`). This is only a floating-point check that all four branches occur in the sample; it is neither a coverage proof nor a justification for dropping any branch. The exact exhaustive reduction is Section 1.

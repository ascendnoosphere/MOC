## Round 071 — Couple all triple-cycle chiralities on a Lorentz quadric

For an oriented triple (i,j,k) and remaining index ℓ, direct expansion gives

\[
z_{(ijk)}-z_{(ikj)}
=(a_\ell+b_\ell)
\det\begin{pmatrix}
1&b_i-a_i&a_ib_i\\
1&b_j-a_j&a_jb_j\\
1&b_k-a_k&a_kb_k
\end{pmatrix}.
\]

To see the cancellation, separate the terms into det[1,b,ab]−det[1,a,ab]. Put s_i=b_i−a_i, t_i=a_ib_i, m_i=a_i+b_i. Then

\[
m_i^2=s_i^2+4t_i.
\]

All four triple-cycle differences are weighted complementary3-minors of the same4×3 matrix[1,s,t]. Their alternating combination is

\[
T=-\det[1,s,t,m]=-2\det[1,a,b,ab],
\]

the same chirality as −2(α₁β₂−α₂β₁).

**Outcome.** This gives an exact spectral constraint tying the four Cayley triangle differences to one conic/quadric configuration. A positivity certificate from those nonlinear identities has not yet been obtained.


## Round 077 — Solve the relevant B-zero star capacity exactly

Suppose e₁₂=e₁₃=e₂₃=0, d₂=0, and d₁,d₃,e₀₂>0, with all remaining coefficients nonnegative. Then

\[
\boxed{\operatorname{cap}(d,e)=
2\sqrt2\sqrt{e_{02}}(d_1d_3)^{1/4}.}
\]

For the lower bound, discard all terms except d₁x₁²+d₃x₃²+e₀₂x₀x₂ and use x₀x₂=1/(x₁x₃). The same minimization used below gives the displayed bound. For the matching upper bound, use the product constraint to write x₂=1/(x₀x₁x₃). The objective becomes

\[
d_0x_0^2+e_{01}x_0x_1+e_{03}x_0x_3
+d_1x_1^2+d_3x_3^2+\frac{e_{02}}{x_1x_3}.
\]

Send x₀→0 while holding x₁,x₃ at their positive minimizers. Writing y=x₁x₃, minimize the last terms first over their ratio, obtaining2√(d₁d₃)y+e₀₂/y, whose minimum is the displayed value.

**Consequence.** B can vanish on a star while true capacity stays positive. Excluding every nonzero-chirality B-zero star is unnecessary and may be false. The correct spectral obligation on this stratum is χ⁴≤64e₀₂²d₁d₃. This inequality is not proved for every actual-spectral star.

## Round 078 — Derive an exact entropy dual for capacity, beyond selected AM–GM circuits

Let the nonzero coefficients c_s be d_i or e_ij, with exponents a_s=2e_i or e_i+e_j. For x_i>0, ∏x_i=1,

\[
\operatorname{cap}(c)=\inf_{\sum y_i=0}\sum_sc_s e^{a_s\cdot y}.
\]

The exponential variational identity

\[
ce^t=\sup_{w\ge0}w(1+t+\log c-\log w)
\]

gives the convex dual. Setting S=Σw_s and λ_s=w_s/S, stationarity in y imposes

\[
\lambda_s\ge0,\quad \sum_s\lambda_s=1,\quad
\sum_s\lambda_sa_s=(1/2,1/2,1/2,1/2).
\]

Optimization in S then yields the exact expression

\[
\boxed{\operatorname{cap}(c)=
\max_{\lambda\text{ balanced}}\prod_s(c_s/\lambda_s)^{\lambda_s}.}
\]

Terms with λ_s=0 are interpreted by continuity. With positive coefficients, ordinary geometric-program duality applies and the log minimizer exists. Zero coefficients follow by adding ε to coefficients and taking ε↓0; monotonicity and evaluation at a fixed x prove continuity of the primal value in this limit.

**Outcome.** The full capacity has a finite-dimensional entropy certificate. The edge-plus-two-loops repair uses weights(1/2,1/4,1/4). The failed B is only one restricted assembly of available certificates. A proof must produce balanced weights, or a sum of balanced circuit allocations, from actual spectral data; arbitrary nonnegative gaps still do not suffice.

## Round 079 — Solve the exact fixed-row SDP on every simplex vertex

### Fixed-row setup for Rounds 079–080

Fix β=(β₁,β₂,β₃,β₄)∈ℂ⁴ and gauge row 2 of U to a real unit vector v. Put D_β=diag(β), C=U D_β U*, and P_β=∏_jβ_j. The coefficient-hull coordinates are D₁=C₁₁+det C[12] and D₀=det C[124]+det C[14], where C[I] denotes a principal submatrix. Their permutation vertices are

\[
V_\pi=\bigl(\beta_{\pi(1)}(1+\beta_{\pi(2)})\beta_{\pi(4)},\ \beta_{\pi(1)}(1+\beta_{\pi(2)})\bigr).
\]

For a real support functional written Re(λ₀D₀+λ₁D₁), define h=max_π Re(λ₀(V_π)₀+λ₁(V_π)₁). This is the support height used below; an actual CH facet is a supporting facet of this actual spectral vertex hull.

Define the complex symmetric pencil

\[
T_\beta(v)=\left(1+\sum_j\beta_jv_j^2\right)D_\beta-(D_\beta v)(D_\beta v)^T.
\]

For the transposes x_i of rows i=1,3,4, let E_i=Re(x_i x_i*). On v⊥ these are real PSD effects with tr E_i=1 and E₁+E₃+E₄=I₃. The coordinate identities are D₁=tr(T_βE₁) and D₀=tr(P_βT_{1/β}E₃). The reciprocal product P_βT_{1/β} is interpreted by entrywise polynomial cancellation when any β_j=0. Define, and then compress to v⊥,

\[
M(v)=\Re(\lambda_1T_\beta(v)),\qquad N(v)=\Re(\lambda_0P_\beta T_{1/\beta}(v)).
\]

The exact fixed-row maximum is

\[
\max\{\operatorname{tr}(ME_1)+\operatorname{tr}(NE_3):E_i\succeq0,\ \operatorname{tr}E_i=1,\ E_1+E_3+E_4=I_3\}.
\]

Its dual is

\[
\min\{\operatorname{tr}Y+\alpha_1+\alpha_3:Y\succeq0,\ Y+\alpha_1I_3\succeq M,\ Y+\alpha_3I_3\succeq N\},
\]

where Y is real symmetric and α₁,α₃ are real. The real three-effect frame lemma makes the primal exact; E_i=I₃/3 gives strict feasibility and hence equality with the attained dual optimum. Complete retained proofs are in [algebra_unitary_realification.md](algebra_unitary_realification.md), §§1, 3, 6–7; the actual CH vertices and supporting-facet formulation are in [root_ch_facet_reduction.md](root_ch_facet_reduction.md). This restores the setup of original Rounds 066/068 without requiring their omitted surrounding material. Below, the older symbol p in the reciprocal formulas means P_β; the simplex coordinates p_j in Round 080 instead mean v_j².

At v=e_j, the compression to v⊥ is diagonal. The pencil definition gives, for k≠j,

\[
M_{kk}=\Re(\lambda_1(1+\beta_j)\beta_k),
\]

\[
N_{kk}=\Re\left(\lambda_0p(1+1/\beta_j)/\beta_k\right).
\]

For β_j=0 use the canceled polynomial expression. The SDP objective depends only on effect diagonals. Their3×3 matrix is doubly stochastic: each effect has trace1 and their sum isI. Hence its maximum is attained at a permutation assignment of the remaining three coordinates, by the elementary doubly stochastic decomposition.

These assignments are exactly the CH permutation vertices with π(2)=j. Therefore the exact fixed-row objective at v=e_j is bounded by h, and an assignment dual supplies diagonal Y and scalar trace multipliers in Round068.

**Outcome.** All four outer simplex vertices satisfy the full spectral support obligation, with exact dual certificates. Extending this by asserting convexity of the fixed-row value in p_j=v_j² is unproved; the square-root off-diagonal coupling prevents an immediate interpolation argument.

## Round 080 — Reduce the remaining outer optimization to a simplex while retaining all coupling

For any real diagonal sign matrix S, the diagonal spectral matrices commute with S, so

\[
T_\beta(Sv)=S T_\beta(v)S.
\]

The reciprocal pencil obeys the same identity. Conjugating the three effects and the dual matrices by S identifies the fixed-row SDPs at v and Sv. Thus their common value depends only on p_j=v_j², with p in the standard3-simplex. We may take v_j=√p_j≥0 without changing the maximum.

Combining this with the exact fixed-row SDP and dual stated above gives an exact full-MOC4 proof obligation:

For every β, every actual CH facet (h,λ₀,λ₁), and every p∈Δ₃, the pair of reciprocal compressed pencils at v=√p admits a dual certificate with objective≤h.

The boundary vertices are solved in Round079. The interior problem still couples M,N through the same p and the frame constraint. The [retained realification theorem](algebra_unitary_realification.md) proves that solving this real simplex/SDP family would settle all complex U(4). It does not settle higher n: its real three-effect lemma and complementary-two-minor argument are dimension-specific, as explained in that theorem's Limits section.

**Scope.** The full conjecture and the universal isoclinic true-capacity inequality remain unproved here. No universal proof or MOC counterexample is claimed.

---


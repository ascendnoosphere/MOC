# Joint odd-coefficient budgets for the unrestricted MOC4 quartic

**Status.** The inequalities in Sections 2–5 are proved for all supported spectral inputs; Section 6 gives an exact full-rank middle-coefficient identity. They do **not** close the unrestricted quartic proof: the missing comparison with its even energy is stated in Section 8. No numerical search is used. The Segre/Plücker identities, reflection-average SOS, realification, and contact-transfer results are imported explicitly, not claimed as new here. The bounded-box support calculation is elementary linear programming.

This note addresses the remaining proof step in [the quartic architecture](analysis_moc4_quartic_pruning.md), rather than introducing another isolated spectral family.

## 1. The actual spectral constraints to retain

Use indices 0,1,2,3. Suppose identity maximizes the permutation support values, and write

\[
 z_\pi=\prod_i(a_i+b_{\pi(i)}),\qquad
 h=\Re(\eta z_{\rm id}),\qquad
 \delta_\pi=h-\Re(\eta z_\pi)\ge0.
\]

Order the four increasing triples as \(\mathcal T=(012,013,023,123)\). Define

\[
 j_{ijk}=\delta_{(ijk)}-\delta_{(ikj)},\qquad
 s_{ijk}=\delta_{(ij)}+\delta_{(ik)}+\delta_{(jk)}.
\]

The rank-two additive-matrix identity gives

\[
 \delta_{(ijk)}+\delta_{(ikj)}=s_{ijk},\qquad |j_r|\le s_r.
 \tag{1}
\]

Set

\[
 \ell=(1,-1,1,-1),\qquad
 S=\sum_rs_r=2\sum_{i<j}\delta_{(ij)},\qquad k=\ell\cdot j.
 \tag{2}
\]

These are not independent formal parameters. In the notation of
[the actual spectral linkage](../../research/ODD_PROFILE_LINKAGE.md),

\[
 \mathcal D=\det\begin{pmatrix}
 1&a_0&b_0&a_0b_0\\
 1&a_1&b_1&a_1b_1\\
 1&a_2&b_2&a_2b_2\\
 1&a_3&b_3&a_3b_3
 \end{pmatrix},\qquad k=-2\Re(\eta\mathcal D).
 \tag{3}
\]

For completeness, put

\[
 \alpha=(a_0-a_1)(a_2-a_3),\quad
 \beta=(a_0-a_2)(a_1-a_3),\quad
 \gamma=(a_0-a_3)(a_1-a_2),
\]

and define \(\alpha',\beta',\gamma'\) from b. Then
\(\alpha-\beta+\gamma=0\), its primed version holds, and
\(\mathcal D=\alpha\beta'-\beta\alpha'\). With

\[
 z_0=\alpha\alpha',\quad z_1=\beta\beta',\quad z_2=\gamma\gamma',\qquad
 W=\eta^2\{(z_0+z_1-z_2)^2-4z_0z_1\},
\]

we have \(W=(\eta\mathcal D)^2\). Consequently

\[
 \boxed{k^2=2(|W|+\Re W).}
 \tag{4}
\]

Indeed \(2(\Re u)^2=|u^2|+\Re(u^2)\). Formula (4) uses the **complex** paired products, not just their real support projections. Replacing them by their real parts is not valid.

If S=0, every j vanishes and the odd coefficients below vanish. Assume S>0 in all divided formulas; zero-weight coordinates can be omitted.

## 2. A Segre-conditioned covariance inequality

For a real four-vector v define

\[
 a_r=\ell_rv_r,\qquad
 \mu_v=\frac1S\sum_rs_ra_r,\qquad
 V_{uv}=\sum_rs_r(\ell_ru_r-\mu_u)(\ell_rv_r-\mu_v).
\]

Then

\[
 \boxed{(v\cdot j-k\mu_v)^2
 \le \left(S-\frac{k^2}{S}\right)V_{vv}.}
 \tag{5}
\]

**Proof.** Let \(p_r=\ell_rj_r/s_r\) on positive-weight coordinates. Equation (1) gives \(|p_r|\le1\) and \(\sum_rs_rp_r=k\). Therefore

\[
 v\cdot j-k\mu_v
 =\sum_rs_r(a_r-\mu_v)(p_r-k/S).
\]

Weighted Cauchy–Schwarz applies, and

\[
 \sum_rs_r(p_r-k/S)^2
 =\sum_rs_rp_r^2-k^2/S\le S-k^2/S.
\]

This proves (5). In particular its residual budget is nonnegative. By (4) it equals

\[
 S-\frac{2(|W|+\Re W)}S.
 \tag{6}
\]

Thus fixing the actual Segre component quantitatively restricts the three remaining odd directions. This is a necessary bound, not a claim that the relaxed odd profiles are realizable.

## 3. Apply it to B and D together, not independently

For an invertible Hermitian H, write the established Cayley support numerator as

\[
 \det(I+t^2H^2)\{h-F(U_t)\}
 =t^2(A+Bt+Ct^2+Dt^3+Et^4),\qquad
 U_t=(I+itH)(I-itH)^{-1}.
\]

The coefficient identities from
[the full Cayley derivation](analysis_full_cayley_quartic.md) give

\[
 w_{ijk}=\Im(H_{ij}H_{jk}H_{ki}),\qquad
 q_{ijk}=-\det(H)^2\Im\{(H^{-1})_{ij}(H^{-1})_{jk}(H^{-1})_{ki}\},
\]
\[
 B=8w\cdot j,\qquad D=8q\cdot j.
 \tag{7}
\]

Apply (5) to every real combination \(v=xw+yq\). Equivalently,

\[
 \boxed{
 \left(S-\frac{k^2}{S}\right)
 \begin{pmatrix}V_{ww}&V_{wq}\\V_{wq}&V_{qq}\end{pmatrix}
 -\begin{pmatrix}B/8-k\mu_w\\D/8-k\mu_q\end{pmatrix}
  \begin{pmatrix}B/8-k\mu_w&D/8-k\mu_q\end{pmatrix}
 \succeq0.}
 \tag{8}
\]

In particular, for \(v(t)=tw+t^3q\),

\[
 |Bt+Dt^3|\le8\left[|k\mu_{v(t)}|+
 \sqrt{(S-k^2/S)V_{v(t)v(t)}}\right].
 \tag{9}
\]

The inverse formula is used only on the dense invertible domain. No inverse is asserted to exist at a singular H; the original coefficient identities and eventual quartic inequality would extend polynomially there.

## 4. The sharp envelope using only these constraints

For S>0, the exact support function of the relaxation

\[
 \mathcal P(s,k)=\{j\in\mathbb R^4: |j_r|\le s_r,\ \ell\cdot j=k\}
 \tag{10}
\]

is also elementary. For \(a_r=\ell_rv_r\), set

\[
 L_\varepsilon(v)=\min_{j:s_j>0}
 \left\{\varepsilon k a_j+\sum_rs_r|a_r-a_j|\right\},
 \qquad \mathcal M(v)=\max\{L_+(v),L_-(v)\}.
 \tag{11}
\]

Then

\[
 \boxed{\max_{j\in\mathcal P(s,k)}|v\cdot j|=\mathcal M(v).}
 \tag{12}
\]

Here the dummy minimization index j in (11) labels a coordinate, not an odd-profile vector. Only four evaluations per sign are needed. If S=0, define \(\mathcal M(v)=0\); the feasible odd profile is then the zero vector.

**Proof.** Put \(x_r=\ell_rj_r\). For any real \(\lambda\),

\[
 \sum_ra_rx_r\le\lambda k+\sum_rs_r|a_r-\lambda|.
 \tag{13}
\]

The right side is convex piecewise linear. Because \(|k|\le S\), its minimum is attained at some breakpoint \(a_j\), including the endpoints \(|k|=S\). The bound is attained by assigning \(x_r=-s_r\) below that threshold, \(x_r=s_r\) above it, and choosing values at the threshold to obtain \(\sum_rx_r=k\). Thus its minimum is the exact maximum of \(v\cdot j\). Replacing a by -a gives the other sign and proves (12).

Consequently every actual spectral input obeys

\[
 \boxed{|Bt+Dt^3|\le8\mathcal M(tw+t^3q).}
 \tag{14}
\]

This is sharp **for (10)**, not for the smaller set of actual spectral profiles. It retains the box constraints as well as the Segre sum, whereas (8) is a convenient joint ellipsoidal bound. In particular

\[
 \mathcal M(v)\le\min\left\{
 \sum_rs_r|v_r|,
 |k\mu_v|+\sqrt{(S-k^2/S)V_{vv}}
 \right\}.
 \tag{15}
\]

## 5. Explicit universal coefficient bounds on the normalized domain

Suppose \(H=H^*\), \(H_{ii}=0\), and \(\|H\|_F=1\). Then

\[
 \boxed{B^2\le AS.}
 \tag{16}
\]

More precisely,

\[
 \boxed{(B-8k\mu_w)^2
 \le(S-k^2/S)(A-64S\mu_w^2).}
 \tag{17}
\]

**Proof of the constants.** Put \(p_{ij}=|H_{ij}|^2\), so \(\sum_{i<j}p_{ij}=1/2\), and use \(w_{ijk}^2\le p_{ij}p_{ik}p_{jk}\). Then

\[
 \sum_rs_rw_r^2
 \le\sum_{i<j}\delta_{(ij)}p_{ij}
       \sum_{k\notin\{i,j\}}p_{ik}p_{jk}.
\]

For the two complementary indices k,l,

\[
 p_{ik}p_{jk}+p_{il}p_{jl}
 \le\tfrac14(p_{ik}+p_{jk}+p_{il}+p_{jl})^2\le1/16.
\]

Since \(A=4\sum_{i<j}\delta_{(ij)}p_{ij}\), it follows that

\[
 \sum_rs_rw_r^2\le A/64.
\]

Weighted Cauchy–Schwarz and \(\sum_rj_r^2/s_r\le S\) give (16). Also
\(V_{ww}\le A/64-S\mu_w^2\); applying (5) proves (17). If S=0, use B=0 directly.

### Symmetric endpoint bounds on the sufficient real domain

For \(H=-iK\), K real skew-symmetric and \(\|K\|_F=1\), let p=pf K and use the Hodge dual convention from the Cayley derivation. The identities are

\[
 A=\mathcal A(K),\quad B=\mathcal B(K),\quad
 D=-p\mathcal B(*K),\quad E=p^2\mathcal A(*K).
\]

Since \(\|*K\|_F=1\), apply (16) also to \(-i*K\). This gives the joint list

\[
 \boxed{B^2\le AS,\qquad D^2\le ES.}
 \tag{18}
\]

The covariance bound (8), with \(q=-p\,w(-i*K)\), additionally retains their correlation. This dual formula has no singular-generator denominator.

## 6. An explicit middle-energy formula for every real skew generator

This calculation does not impose rank two on K. Use indices 1,2,3,4 in this section, and write

\[
 K_{12}=a,\ K_{13}=b,\ K_{14}=c,\ K_{23}=d,\ K_{24}=e,\ K_{34}=f,
\]
\[
 r_1=af,\qquad r_2=-be,\qquad r_3=cd,\qquad p=r_1+r_2+r_3.
\]

For the matchings \(12|34,13|24,14|23\), let S_i be the sum of the two transposition deficits and d_i the double-transposition deficit. Set

\[
 C_0=\sum_{i<j}\delta_{(ij)}(K^2_{ij})^2,\qquad
 P=\sum_{i=1}^3(d_i-S_i)r_jr_k,\quad\{i,j,k\}=\{1,2,3\}.
\]

Then the full real Cayley quartic has middle coefficient

\[
 \boxed{C=4C_0+8p\sum_{i=1}^3(2d_i-S_i)r_i-16P.}
 \tag{19}
\]

In particular p=0 recovers the existing rank-two formula \(C=4(C_0-4P)\). The additional full-rank term is retained in (19), not discarded as nonnegative.

### Proof

Let V_i be the sum of the two inverse four-cycle deficits whose cycles omit matching i. Direct rank-two product expansion gives

\[
 V_i=S_i+d_j+d_k-d_i.
 \tag{20}
\]

For example the complex identity for i=1 is

\[
 z_{(1324)}+z_{(1423)}=
 z_{(12)}+z_{(34)}+z_{(13)(24)}+z_{(14)(23)}
 -z_{(12)(34)}-z_{\rm id}.
\]

Taking support deficits gives (20). These identities do not assume active four-cycles.

For real O with determinant one,

\[
 \det(D_a+OD_bO^T)=\sum_\pi\lambda_\pi(O)z_\pi,
 \qquad\lambda_\pi(O)=\operatorname{sgn}(\pi)\prod_iO_{i,\pi(i)},
 \qquad\sum_\pi\lambda_\pi=1.
\]

This follows from \(\det(D_aO+OD_b)=\det(D_a+OD_bO^T)\). Thus the support deficit is \(\sum_\pi\lambda_\pi\delta_\pi\), even though the individual coefficients need not be nonnegative.

Expand \(O(t)=I+2tK+2t^2K^2+2t^3K^3+O(t^4)\) and clear the denominator \((1+s t^2+p^2t^4)^2\), with \(s=\sum_{i<j}K_{ij}^2=\tfrac12\|K\|_F^2\). A transposition ij contributes to its degree-four coefficient

\[
 c_{ij}=-4(K^2_{ij})^2+8K_{ij}(K^3)_{ij}
       +8K_{ij}^2\{(K^2)_{kk}+(K^2)_{ll}+s\},
\]

where k,l are complementary. A pair of inverse three-cycles on ijk contributes \(8T_{ijk}s_{ijk}\), where

\[
 T_{ijk}=(K^2)_{ij}K_{jk}K_{ki}
          +K_{ij}(K^2)_{jk}K_{ki}
          +K_{ij}K_{jk}(K^2)_{ki}.
\]

The double transpositions contribute \(16\sum_i d_i r_i^2\), and the inverse four-cycle pairs contribute \(16\sum_iV_i r_jr_k\).

The transposition and three-cycle contributions together are

\[
 \sum_{i<j}\delta_{(ij)}c_{ij}+8\sum_{i<j<k}s_{ijk}T_{ijk}
 =4C_0-8p\sum_iS_i r_i.
 \tag{21}
\]

Here is a direct coefficient check explaining (21), not a sign assumption. Put \(R_2=r_1r_2+r_1r_3+r_2r_3\). For each triangle,
\(T_{ijk}\) is the sum of its three products of squared edges, minus R_2. For the edge 12, the coefficient on the left of (21) is

\[
 c_{12}+8(T_{123}+T_{124})
 =4(bd+ce)^2-8paf
 =4(K^2_{12})^2-8pr_1.
\]

Use \(K^3=-sK+p*K\) for the first equality. Relabeling gives the same identity for all six edges, proving (21).

Finally the total middle coefficient is

\[
 C=4C_0-8p\sum_iS_i r_i
       +16\sum_i d_i r_i^2+16\sum_iV_i r_jr_k.
\]

Substitute (20) and use
\(p\sum_i d_i r_i=\sum_i d_i r_i^2+\sum_i(d_j+d_k)r_jr_k\).
This gives (19). All steps are polynomial identities and therefore include singular K.

Formula (19) supplies the even energy needed for comparison with (8), but its terms are not all nonnegative. Six support contacts have not here been shown to control those competing terms.

## 7. Use the strongest existing pruning, not a weaker replacement

Two existing results combine exactly:

1. [Realification](algebra_unitary_realification.md) expresses every full U(4) squared-minor profile as a convex combination of SO(4) profiles, with the same spectra. Any strict support violation therefore has a strict real-orthogonal witness. Row signs let it be chosen in SO(4).
2. [Contact transfer](../../closing/high_contact_reductions.md) preserves a fixed mixer, support direction, and positive gap while moving to actual finite spectra with at least six nonzero, pairwise-distinct active products. A prescribed dense conic Zariski-open condition may be retained.

Thus a proof of the real skew-generator quartic for **all such terminal spectral inputs** would prove unrestricted MOC4. This is stronger pruning than merely requiring four tied permutations. The order of reductions matters: first realify and perform contact transfer. At the resulting terminal spectra, relabel an active permutation to identity and restore determinant +1 by a diagonal row sign, which preserves the objective. Finally perturb the real mixer into the dense Cayley chart, preserving the strict violation by continuity. This last perturbation does not change any spectral products, their nonzero/pairwise-distinct property, or the at-least-six support contacts. It therefore gives an identity-anchored, real Cayley witness on terminal spectra. Its nonzero skew generator can be normalized to Frobenius norm one, absorbing its scale into t. We do not assume the preliminary generic perturbation inside contact transfer preserves an earlier prescribed anchor.

The separate terminal results in
[MOC4_Verified_Results.md](../../geometry/MOC4_Verified_Results.md) exclude the localized height-zero frontier; Drury's external-vertices theorem covers negative support height. Positive-height six-through-nine-contact residual faces are **not** all solved. Neither (8) nor six contacts alone is an automatic Gram certificate.

## 8. Exact remaining gap

Let \(R(t)=A+Ct^2+Et^4\). Reflection averaging proves R>=0. The above work bounds the correlated odd expression; it does **not** prove

\[
 R(t)\ge8\mathcal M(tw+t^3q)\quad\text{for all }t.
 \tag{22}
\]

Equation (22) would be sufficient, not necessary: the relaxation (10) discards other spectral constraints and can overestimate the odd expression.

Even the necessary quartic inequalities

\[
 B^2\le4A(C+2\sqrt{AE}),\qquad
 D^2\le4E(C+2\sqrt{AE})
\]

do not follow from (16) or (18). Those bounds compare to AS and ES, not to the actual even slack. Positivity of \(C+2\sqrt{AE}\) alone does not bridge the difference.

A complete proof must allocate enough **even** quartic energy to the residual covariance in (8), or exploit the remaining actual spectral constraints to sharpen it. No argument here establishes the required Gram determinant inequality. **Unrestricted MOC4 remains unproved by this attempt.**

## Exact verification

`code/research/verify_moc4_joint_odd_budget.py` checks the middle-coefficient identity in six independent skew coordinates and nine independent even gaps, all three paired four-cycle product identities in eight independent spectral symbols, 13 exact bounded-box support examples (including zero weights and endpoint sums), and an actual spectral/Cayley regression at t=1,-1,2. It also checks the covariance constants and both normalized endpoint bounds on that regression. Output: `build/direct_attack/moc4_joint_odd_budget_exact_checks.json` (PASS). The finite regression examples are not a universal positivity certificate; the general inequalities have the proofs above.

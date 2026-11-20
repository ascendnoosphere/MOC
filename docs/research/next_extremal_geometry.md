# Extremal geometry: a rank-one no-escape theorem and the compact obstruction

This note proves an exact obstruction to monotone rank-one phase algorithms and a quantitative open-set obstruction to one-step rank-one reducing moves. It also proves a canonical balancing theorem and computes the limitations of compact mixed variations. The global reducing-move theorem needed for unrestricted Marcus–de Oliveira remains open (Section 5).

The target is, for arbitrary complex spectra and every unitary U,

\[
 F(U)=\Re\{\eta\det(D_a+UD_bU^*)\}
 \leq\max_\pi\Re\{\eta\prod_i(a_i+b_{\pi(i)})\}.
\]

## 1. A complete rank-one no-escape theorem

Use the Walsh matrix

\[
 W=\frac12\begin{pmatrix}1&1&1&1\\1&-1&1&-1\\1&1&-1&-1\\1&-1&-1&1\end{pmatrix},
\quad a=(1,-1,-3i,3i),\quad b=(-3,3,-i,i),\quad\eta=i.
\]

The existing exact calculation gives d(W)=-43-24i and F(W)=24, while the permutation maximum is 48. For a unit vector v, put P=vv*, and define

\[
 q(P)=48\bigl(|P_{12}-P_{34}|^2+
 |P_{13}-\overline{P_{24}}|^2+|P_{14}-P_{23}|^2\bigr).
 \tag{1}
\]

The entire rank-one projector-phase fiber, not only its second derivative, satisfies

\[
 F(W)-F((I+(e^{it}-1)P)W)=(1-\cos t)q(P).
 \tag{2}
\]

One way to obtain (2) is the rank-two determinant lemma applied to the conjugation update. Its sine coefficient vanishes by stationarity; its cosine coefficient is (1). The new verifier independently checks this coefficient as a quartic polynomial in all eight real coordinates of v. For unnormalized v, it homogenizes the term linear in the projector by ||v||².

**Theorem.** The zero set of (1), among rank-one orthogonal projectors, consists exactly of the four coordinate projectors and the four Walsh-column projectors.

Proof. Write v=(z1,z2,z3,z4). Vanishing is equivalent to

\[
 z_1\bar z_2=z_3\bar z_4,\qquad
 z_1\bar z_3=\bar z_2z_4,\qquad
 z_1\bar z_4=z_2\bar z_3.                 \tag{3}
\]

If one coordinate vanishes, these equations force at most one nonzero coordinate. If none vanish, taking absolute values in (3) forces all four moduli to agree, hence each is 1/2. Writing zj=(1/2)e^{i theta_j}, the three phase equations imply that all relative phases are 0 or pi. Their signs have product +1. Up to a common phase, the four resulting vectors are precisely the columns of W. This proves the classification.

A coordinate-projector phase is a left diagonal gauge, which commutes with D_a. A Walsh-column projector is a spectral projector of W D_b W*, so its phase does not change that matrix. These are the only zero-loss moves in (2), except e^{it}=1.

**Corollary.** Every finite sequence of arbitrary rank-one projector phases, each accepted only when its endpoint support does not decrease, starting at W remains in its left/right diagonal gauge orbit. It cannot reach a permutation matrix or a point of support greater than 24. The same holds for limits of such sequences, since the gauge orbit is compact.

Indeed, at a gauge-equivalent point LWR, conjugate a proposed projector by L*. Equation (2) and the classification apply again. Thus every accepted move is another gauge move. This is stronger than a trap for coordinate-pair polishing or a failure of a single reducing pivot. It concerns discrete monotone rank-one phase updates, not arbitrary time-dependent controls with temporary losses.

The archive supplies the repair for this particular example: a coupled rank-two phase or the explicit skew generator K with K²=-3I and

\[
 F((cI+sK)W)=24+384cs^3,\qquad c^2+3s^2=1.
\]

At c=s=1/2 this reaches a signed permutation of support 48. The correction requires a coordinated move; rank-one monotonicity cannot discover it.

## 2. The one-step rank-one reducing obstruction persists for generic spectra

The existing exact cross-pivot calculation gives, for every row i and column j, a scalar Hessian block Gij=36 I2. Since |Wij|=1/2, every rank-one projector phase R mapping column j to a coordinate has endpoint loss

\[
 F(W)-F(RW)=\frac{18}{|1-\bar\lambda W_{ij}|^2}\geq 8.
 \tag{4}
\]

This strict loss persists under arbitrary small spectral perturbations. Keep W and eta=i fixed, and assume

\[
 \max_i|a_i-a_i^0|\leq\delta,\qquad
 \max_j|b_j-b_j^0|\leq\delta.
\]

For every unitary V, the original sum has operator norm at most 6 and its perturbation has norm at most 2 delta. A telescoping replacement of the four columns, followed by Hadamard's inequality, gives

\[
 |F_{a,b}(V)-F_{a^0,b^0}(V)|\leq 8\delta(6+2\delta)^3.
\]

Consequently every reducing endpoint in (4) has perturbed support loss at least

\[
 8-16\delta(6+2\delta)^3.                         \tag{5}
\]

At delta=1/1000 the error term is exactly 27027009001/7812500000 < 7/2. Thus every rank-one reducing endpoint loses more than 9/2 throughout this open spectral neighborhood. Its generic points avoid any prescribed proper real-algebraic exceptional conditions. A genericity assumption cannot repair the one-step rank-one reducing inequality. The arbitrary-rank-two reducing inequality remains open.

This does not prove an irreducible local maximum. Walsh has cubic ascent and is not a local maximum. The robust statement (5) concerns full reducing endpoints, not all sufficiently small rank-one moves at the perturbed spectra.

## 3. Canonical common SL2 balancing in every dimension

Let 2n unit spinors wk be divided into row labels ui and column labels vj. Put

\[
 p_\pi=\prod_i[u_i,v_{\pi(i)}],\quad
 d=\det(([u_i,v_j]U_{ij}))/\det U,\quad
 h=\max_\pi\Re(p_\pi-d).
\]

Common normalized SL(2,C) action multiplies every p_pi and d by the same positive number

\[
 R(S)=\prod_k\|Sw_k\|^{-1}.
 \tag{6}
\]

There is a useful pointwise boundary statement. If a projective point occurs more than n times, every matching product is zero by counting, and d=0 by Leibniz expansion. If it occurs exactly n times, suppose r occurrences are row labels. In every nonzero matching, the r row occurrences must pair with the r column labels outside that point. All nonzero matching products have the same value p. After ordering these groups, the masked matrix has two blocks with scalar row/column factors. Jacobi's complementary-minor identity gives

\[
 d=p\,|\det U_{11}|^2.
 \tag{7}
\]

For 0<r<n some matching products are zero, so d lies in [0,p]. At r=0 or n all matching products equal p and d=p. This argument does not require the other n spinors to coincide or already be orthogonal to the repeated point. Thus every multiplicity-at-least-n configuration is safe pointwise.

**Balancing theorem.** If maximal projective multiplicity r is strictly less than n, there is a unique balancing positive metric S*S, up to the corresponding left SU2 action on S, such that the normalized transformed labels satisfy

\[
 \sum_k w_kw_k^*=nI_2.                              \tag{8}
\]

Proof. Minimize L(S)=sum_k log||Swk|| on SL2/SU2. Along a geodesic e^{tH}, H traceless Hermitian,

\[
 L''(t)=2\sum_k\operatorname{Var}_{\widehat w_k(t)}(H)\geq0.
 \tag{9}
\]

If S has singular values e^t,e^{-t}, a fixed sufficiently small neighborhood of any projective point contains at most r labels. Outside the contracting singular line's neighborhood, at least 2n-r labels have expanding component uniformly bounded below. The remaining r norms are at least e^{-t}. Hence, uniformly in the singular lines,

\[
 L(S)\geq 2(n-r)t+O(1).
\]

This proves coercivity and existence. At a critical point the derivative against every traceless Hermitian H yields (8). Equality in (9) along a nonzero geodesic would put every label on its two eigenlines. A balanced two-point configuration has n labels on each line, contrary to r<n. Thus the convexity is strict between distinct metrics, proving uniqueness.

This gives an attained canonical representative of every potentially violating common projective orbit; constructing a positive permutation law is a separate step.

A separate extremal boundary is also safe: if |d|=1, the contraction M=([ui,vj]Uij) must itself be unitary. Its row norm identities force |[ui,vj]|=1 on every nonzero Uij. Within each connected component of U's bipartite support graph, all row labels therefore lie on one projective line and all column labels on its orthogonal line. The bracket phases factor into row and column phases on that component. Factoring them out of M shows that d equals a matching product supported on U. Therefore |d|=1 cannot occur at a negative minimizer.

## 4. Exact compact-minimizer conditions and their symmetry limitation

At a negative local minimum m<0, multiplicity-at-least-n is excluded by (7), and (6) forces balance. Let A be the active matching labels. First-order separation produces one common probability law lambda supported on A such that, for

\[
 P=\sum_\pi\lambda_\pi p_\pi-d,
\]

\[
 P=m,\qquad \partial_{w_k}P=m\bar w_k\quad(1\leq k\leq2n).
 \tag{10}
\]

The phase tangents are essential, but their number is misleading: every individual phase tangent has the same derivative -Im(p_pi-d). The 2n-1 phase differences are exact gauge directions.

There is a finite support bound stronger than leaving the active law unrestricted. At a balanced stable tuple, the 2n-1 phase gauges and the six common normalized SL2 directions are independent. All active differentials annihilate them. The real product-sphere tangent dimension is 6n, so the active gradients lie in a space of dimension at most 4n-5. Carathéodory therefore permits

\[
 |\operatorname{supp}\lambda|\leq 4n-4.              \tag{11}
\]

The independence follows because an infinitesimal traceless complex 2-by-2 matrix fixing three distinct projective points must vanish. Unitary derivatives are common to all contacts and vanish at this minimum, so they impose no further multiplier dimensions. Equation (11) is not a three-contact theorem and does not bound the total number of active labels.

Common balancing directions provide no mixed-Hessian contradiction. For traceless Hermitian H at a balanced tuple,

\[
 \frac{d^2}{dt^2}h\left(\frac{e^{tH}w_k}{\|e^{tH}w_k\|},U\right)_{t=0}
 =-2m\sum_k\operatorname{Var}_{w_k}(H)>0\quad(H\ne0).
 \tag{12}
\]

Furthermore, for every unitary tangent K, invariance before normalization gives d(t,s)=R(e^{tH})d(U(s)); since R'(0)=0,

\[
 D_HD_Kd=0.                                        \tag{13}
\]

Thus these guaranteed contact-critical directions are strictly stable normalization directions with zero mixed block. Treating balance as a latent descent theorem would reverse its actual curvature sign.

For genuine spectral critical directions z the archive's acceleration-LP argument remains the correct test. With Lambda the full common KKT-law set, H the nonnegative unitary loss Hessian, and bz(K)=-Re D_zD_Kd,

\[
 b_z|_{\ker H}=0,\qquad
 b_z^TH^\dagger b_z\leq\max_{\lambda\in\Lambda}Q_\lambda(z).
 \tag{14}
\]

The maximizer lambda can depend on z. A minimum of a maximum need not admit any single positive-semidefinite weighted Hessian. At high contact rank, the common critical spectral space can consist largely of the symmetry directions (12)-(13), so nominal tangent counting supplies no bridge.

Another compatibility issue prevents an immediate combination with high-contact localization. That holomorphic transfer keeps an **unnormalized** complex gap fixed. Subsequent unit-spinor normalization multiplies it by R(S), which generally changes the compact minimum. It is not justified to assign both the transferred contact count >=2n-2 and the compact all-label equations (10) to one witness without a joint construction.

## 5. Stationarity and the missing global theorem

Write B=UD_bU*, M=A+B. Direct differentiation gives

\[
 F'(K)=\Re\operatorname{tr}\bigl(K[B,\eta\operatorname{adj}M]\bigr),\quad K^*=-K.
\]

Therefore exact support stationarity is

\[
 [B,\eta\operatorname{adj}(A+B)]
 =[B,\eta\operatorname{adj}(A+B)]^*,                 \tag{15}
\]

not vanishing of this commutator. The verifier checks the singular example A=diag(i,-i), B=((0,1),(1,0)), eta=1: the commutator is the nonzero Hermitian matrix ((0,2i),(-2i,0)). No off-diagonal product has been replaced by an absolute square for complex spectra.

A generic benign-local-landscape statement is already false at permutation matrices. The exact archived example a=(2+5i,2-3i,-2+i,5+4i), b=(1+i,-2+2i,3+3i,1-5i), eta=1 has F(I)=129 and six strictly positive swap gaps (472,96,42,1104,1218,126), hence a strict local maximum on the orbit, although permutation (2,1,4,3) has support 1099. The strict inequalities persist under perturbation. This does not settle the irreducible-local-maximum question.

A sufficient all-dimensional induction theorem would be:

> Every actual support maximum strictly above all matching supports has a support-preserving reducing move, or admits a genuine coordinated ascent contradicting maximality.

Equations (5) and Section 1 exclude rank-one reducing moves and monotone rank-one phase sequences as universal mechanisms. The rank-two endpoint family remains a candidate, with a universal domination inequality still to prove. The other routes have distinct obligations: root-pair affine identities give swap-gap inequalities, Ward kernel identities need a positive weighting, and the n4 neutral-adjugate sheet needs a positive fourteen-feature Gram theorem.

## 6. Verification and reading inventory

Run:

```
PYTHONDONTWRITEBYTECODE=1 python code/research/next_extremal_geometry.py
```

The exact run passed the full eight-real-variable rank-one quartic identity, zero sine coefficient, all sixteen cross-pivot blocks, rational perturbation margin, singular stationary-commutator example, balanced six-spinor variance formula, and the strict suboptimal permutation trap. The continuum proofs are the arguments above; enumerating sign vectors alone would not prove the rank-one zero-set theorem. The script writes only stdout.

I read these files completely:

* Every file under docs/early (the five proof notes and both LaTeX files).
* Every file directly under docs/closing: closing_algebraic_notes.txt, closing_contact_audit.txt, closing_contact_geometry_audit.txt, closing_cycle_notes.txt, closing_deformation_notes.txt, closing_geometry_notes.txt, closing_variational_notes.txt, high_contact_reductions.md.
* docs/geometry: MOC4_Verified_Results.md; structural_identities_and_audit.md; full4_bridge_metaproof_audit.txt (all 714 lines); terminal_profile_geometry_notes.txt; profile_cancellation_notes.txt; plucker_moc4_notes.txt; global_weighted_minor_notes.txt; profile_geometry_audit.txt. These include the actual weighted-minor analytic argument, contact-transfer argument and profile convexification proof. I grouped the repetitive contact-type files through the long combined audit and did not inspect their individual certificates.
* docs/research: global_variational_bridge_lemmas.md; session_variational.txt; moc_visual_variational_20261031.txt; moc_moonshot_variational_20261031.txt; moc_variational_strict_branch_20261031.txt; moc_compact_spinor_minimax_20261031.txt; moc_compact_mixed_hessian_20261031.txt; moc_global_root_pair_affine_20261031.txt; moc_global_flag_ward_identity_20261031.txt; moc_global_flag_ward_independent_audit_20261031.txt; moc_toric_walsh_common_law_20261031.txt; moc_toric_flag_support_20261031.txt; moc_unrestricted_neutral_20261031.md; moc_unrestricted_variational_20261031.md; branch_A_maximizer_geometry.md; flat_resonance_closure.md; moc_pair_maximum_moonshot.txt.
* Code: code/closing/closing_variational_verify.py; code/geometry/global_weighted_minor_verify.py; code/geometry/profile_geometry_verify.py; code/research/moc_compact_spinor_exact_audit.py; moc_compact_mixed_hessian_verify.py; moc_global_root_pair_affine.py; moc_global_flag_ward_identity.py; moc_unrestricted_variational_rounders.py; moc_unrestricted_neutral_adjugate.py; moc_toric_walsh_common_law.py; moc_walsh_stationary_linear.py (the latter nine names are under code/research). I also read build/moc_walsh_stationary_symbolic_20261031.json completely. I did not execute the old scripts because several overwrite old build artifacts.

Not read under docs/geometry: closing_high_contact_standalone.txt, closing_moc4_notes.txt, cone82_completeness_notes.txt, contact_complex_audit.txt, global_moc4_nine_lift_notes.txt, global_moc4_weighted_propagation_notes.txt, global_six_row_notes.txt, plucker_positive_metaproof_audit.txt, positive_height_terminal_constraints.md, profile_family_edges_independent_review.txt, profile_safe_cone_audit.txt, proposal_algebraic_terminal_notes.txt, proposal_universal_polytope_audit.txt, source_record_selected_sections.txt, terminal_nine_notes.txt, terminal_ten_notes.txt, zero_height_geometry_notes.txt, zero_height_type1_notes.txt, zero_height_type26_notes.txt, zero_height_types34_notes.txt. Other research documents, individual n4 contact code/certificate batches, and other code were not read. In particular I did not inspect the neutral numerical search implementations or the rank-two adversary implementation.

Two finite exploratory toric searches, without artifact writes, found no bounded strict toric local maximum: 250 n3 integer-spectrum cases at the fixed real Householder mixer, and 300 n4 cases with complex Haar mixers, with respectively three and two BFGS starts. They were heuristic, allowed boundary escapes, and do not test or prove the full irreducible-local-maximum assertion. The existing archive's 200 stationary Walsh unfoldings also found no strict irreducible maximum. I did not repeat that campaign. A two-query web search about general modulus bounds supplied no proof mechanism; no theorem in this note depends on its result.

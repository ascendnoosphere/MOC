# Exact SOS for the full Hermitian reflection average

## Scope and status

**New partial result, not unrestricted MOC4.** The exact verifier passes for every one of the 70 compound coefficient directions, using all nine Hermitian coordinates and all 838 polynomial coefficient positions. [The independent mathematical review](reflection_average_independent_review.md) returned **VALID** within the averaged scope, independently checking the full Hermitian Cayley/compound geometry, all atom identities, extraction, common phase invariance and global limits.

For a fixed support direction put
\[
 F(U)=\Re\{\eta\det(D_a+UD_bU^*)\},\qquad
 h=F(I)=\max_{\pi\in S_4}F(P_\pi).
\]
Then the result is
\[
 \boxed{\frac{F(U)+F(U^*)}{2}\le h\quad\text{for every }U\in U(4).}
\]
It does **not** give either summand's individual bound. The maximizing contact is identity in this statement. The analogous statement at a maximizing permutation matrix \(P\) replaces the partner by \(PU^*P\), not by \(U^*\) independently of the contact.

The proof actually works for arbitrary real linear combinations of squared compound minors with identity maximizing their permutation values; it uses no extra spectral linkage. That generality is possible because it controls only the reflection average. The unsymmetrized universal common-minor law is known to fail.

## 1. Canonical even polynomial

Global unitary Sinkhorn reduction and the Cayley chart give
\[
 U(T)=ee^T+Y(I+iT)(I-iT)^{-1}Y^T,\quad T=T^*,\quad
 D(T)=\det(I+T^2)>0.
\]
Here \(Y\) is the fixed real orthonormal basis used by `exact_geometry()` and \(e=(1,1,1,1)^T/2\). Write
\[
 t=\operatorname{coords}T,\quad C=\operatorname{adj}T,\quad
 c=\operatorname{coords}C,\quad d=\det T.
\]
The actual numerator is \(G(T)=D(T)[h-F(U(T))]\). Since \(U(-T)=U(T)^*\) and \(D(-T)=D(T)\), its even part is
\[
 G_{\rm ev}(T)=\frac{G(T)+G(-T)}2
 =D(T)\left[h-\frac{F(U(T))+F(U(T)^*)}{2}\right].
\]
Absorbing degree-two constant/cofactor terms and degree-four \(td\) terms by the polynomial adjugate identities gives
\[
 G_{\rm ev}(T)=t^TAt+c^TD_0c+g d^2.
\]
This equality is verified coefficientwise on all 70 formal compound profiles, not inferred from a special family. No assertion about the odd part has been used.

## 2. Nine original even gap coordinates

Let \(\Delta_\pi=h-F(P_\pi)\ge0\). Put
\[
 w_{ij}=\Delta_{(ij)}/4,\qquad
 (d_1,d_2,d_3)=(\Delta_{(12)(34)},\Delta_{(13)(24)},\Delta_{(14)(23)}).
\]
Then \(g=\sum_{i<j}w_{ij}\). All entries of the full nine-coordinate matrices \(A,D_0\) are linear combinations of these nine gaps. The rank-nine reconstruction is checked against all 70 rows. This is **not** a rank-nine assertion about the complete unsymmetrized comparison data, whose rank is 13.

Define
\[
 \alpha=(d_1+d_2-d_3)/2,\quad
 \beta=(d_1+d_3-d_2)/2,\quad
 \gamma=(d_2+d_3-d_1)/2.
\]
The three residual boundary forms, now on a general Hermitian \(C\), are
\[
 L_\alpha=(C_{11}-C_{22})^2+4(\Im C_{12})^2,
\quad L_\beta=(C_{22}-C_{33})^2+4(\Im C_{23})^2,
\quad L_\gamma=(C_{11}-C_{33})^2+4(\Im C_{13})^2.
\]
These are actual sums of squares, including the imaginary-coordinate contributions omitted in the earlier real restriction.

## 3. Explicit full-Hermitian atoms

For any Hermitian matrix \(H\), write its real coordinates as
\((r_1,r_2,r_3,u,v,w)=(H_{11},H_{22},H_{33},\Re H_{12},\Re H_{13},\Re H_{23})\)
and its imaginary coordinates as \((p,q,r)=(\Im H_{12},\Im H_{13},\Im H_{23})\).

The linear forms below are evaluated at either \(T\) or \(C\) as indicated in the formulas. The six coefficients in the \(l_e\) column multiply the real coordinates in the displayed order.

| Edge | \(l_e\) | \(m_e\) | \(b_e\) | \(n_e\) | \(s_e\) | Special double gap |
|---|---|---|---|---|---|---|
|12|\((-1,1,-1,0,-2,0)\)|\(p-r\)|\(u-w\)|\(q\)|\(r_2-v\)|\(d_1\)|
|13|\((1,-1,-1,0,0,-2)\)|\(p+q\)|\(u-v\)|\(r\)|\(r_1-w\)|\(d_2\)|
|14|\((-1,-1,1,-2,0,0)\)|\(q+r\)|\(v-w\)|\(p\)|\(r_3-u\)|\(d_3\)|
|23|\((-1,-1,1,2,0,0)\)|\(q-r\)|\(v+w\)|\(p\)|\(r_3+u\)|\(d_3\)|
|24|\((1,-1,-1,0,0,2)\)|\(p-q\)|\(u+v\)|\(r\)|\(r_1+w\)|\(d_2\)|
|34|\((-1,1,-1,0,2,0)\)|\(p+r\)|\(u+w\)|\(q\)|\(r_2+v\)|\(d_1\)|

A baseline atom has one transposition gap equal to 4, all others and all double gaps zero. A special atom has the same transposition gap and the indicated double gap equal to 4. They are algebraic coefficient atoms; they need not individually come from spectra or satisfy all permutation support inequalities.

Their **even** polynomials are respectively
\[
 \boxed{G_e^-=(l_e(T)-d)^2+4m_e(T)^2+4b_e(C)^2+4n_e(C)^2,}
\]
\[
 \boxed{G_e^+=(l_e(T)+d)^2+4m_e(T)^2+4s_e(C)^2+4m_e(C)^2.}
\]
These identities hold for every Hermitian \(T\), including singular matrices. They use the polynomial identity
\(\operatorname{adj}(\operatorname{adj}T)=dT\), not an inverse formula.

Equivalently, if \(L(l)\) represents \(l(\operatorname{adj}C)\), the exact matrices have
\[
 A_e-l_el_e^T=4m_em_e^T\succeq0,
\]
\[
 D_e+2L(l_e)=4b_eb_e^T+4n_en_e^T\succeq0,
\quad
 D_e^{\rm special}-2L(l_e)=4s_es_e^T+4m_em_e^T\succeq0.
\]
All 18 factor identities are verified over the rationals. Setting the imaginary coordinates to zero recovers the independently validated [real-Cayley SOS](REAL_COFACTOR_BOUND.md).

## 4. Why the atoms have nonnegative weights

The extraction proof from the real branch applies unchanged to the full nine-coordinate matrices, because their nine gap coordinates and the special-atom changes are the same.

Let \(W_1=w_{12}+w_{34}\), \(W_2=w_{13}+w_{24}\), \(W_3=w_{14}+w_{23}\). Original inverse-four-cycle gap sums give
\[
 2\alpha+4W_3\ge0,\quad 2\beta+4W_2\ge0,\quad 2\gamma+4W_1\ge0.
\]
Also \(\alpha+\beta=d_1\ge0\), \(\alpha+\gamma=d_2\ge0\), \(\beta+\gamma=d_3\ge0\), so at most one edge weight is negative.

If all are nonnegative, use \(w_eG_e^-\) plus the three weighted \(L\)'s. If \(\alpha=-t<0\), then \(\beta,\gamma\ge t\) and \(W_3\ge t/2\). Extract amounts \(a_{14},a_{23}\) totaling \(t/2\) from those two baseline weights and replace them by the corresponding special atoms. This changes the represented edge weights by \((-t,t,t)\), leaving the nonnegative residual \((0,\beta-t,\gamma-t)\). Explicitly, \(a_{14}=\min(w_{14},t/2)\), \(a_{23}=t/2-a_{14}\) satisfy the capacities. The other two cases use groups 2 and 1 respectively.

The full matrices, not only their real restrictions, are preserved by this extraction. Every remaining term is one of the displayed squares. This proves \(G_{\rm ev}\ge0\), with no strict-support hypothesis and no division by \(g\).

## 5. Global unitary coverage and the correct reflected partner

For every unitary \(U\), Idel–Wolf gives diagonal unitaries \(D_L,D_R\) with \(W=D_LUD_R\) fixing \(e\). Both support values are unchanged:
\[
 F(W)=F(U),\quad F(W^*)=F(D_R^*U^*D_L^*)=F(U^*).
\]
This follows either from diagonal conjugation invariance of the determinant or from invariance of all absolute minor squares under left/right diagonal phases. Approximate the residual \(V\in U(3)\) by matrices whose eigenvalues avoid \(-1\); the Cayley chart covers those matrices. Continuity of both summands proves the averaged inequality for every \(U\). No extra symmetry, nonzero-entry or generic-spectrum assumption is needed for this averaged statement.

For a general maximizing permutation matrix \(P\), let \(D_b'=PD_bP^*\) and \(U'=UP^*\). Then \(F_{a,b'}(U')=F_{a,b}(U)\), while the reflected term is
\[
 F_{a,b'}(U'^*)=F_{a,b}(PU^*P).
\]
Thus the support-contact reflection is the involution \(R_P(U)=PU^*P\), fixing \(P\). It is not conjugation by \(P\).

## 6. The unresolved odd part

The original target is \(G(T)\ge0\). What remains is
\[
 G_{\rm ev}(T)\ge |G_{\rm odd}(T)|,\qquad
 G_{\rm odd}(T)=\tfrac12[G(T)-G(-T)].
\]
Equivalently, the full Gram must also handle the cubic and quintic couplings. The even SOS supplies a natural nonzero u and positive degree-parity diagonal blocks, but does not prove the cross-parity block is a contraction. Universal full completion remains unproved.

No independent assignment/Procrustes bounds, complex Bloch-Gram positivity, positive-map conclusion from nonnegative entries, or independent four-cycle orientation choices are used here.


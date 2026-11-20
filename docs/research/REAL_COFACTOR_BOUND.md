# Real-Cayley support branch and the full six-dimensional real-cofactor bound

**Two precise conclusions:**

1. The scalar necessary Schur bound holds for every **real symmetric** formal cofactor matrix (six real dimensions).
2. More strongly, the original support-gap numerator has an explicit SOS for every **real symmetric Cayley parameter** \(T\), when identity maximizes the original 24 comparison products in the chosen support direction.

[Independent mathematical audit](real_cayley_independent_review.md): both conclusions VALID, including the canonical absorption, exact extraction capacity, singular matrices and symmetric chart boundary. This is an exact symbolic audit, not a Lean formalization.

Neither conclusion treats arbitrary complex Hermitian \(T\), proves a simultaneous full 25-parameter Gram completion, or proves unrestricted MOC4. The second conclusion is a **contact-specific support theorem**, not all support directions for every pair or an invariant unitary family. Column relabeling a maximizing permutation need not preserve symmetry of the dephased relative unitary.

## 1. Universal coefficient identities

Let \(\tau_{ij}=\Delta_{(ij)}\ge0\), let \(w_{ij}=\tau_{ij}/4\), and put
\[
 d_1=\Delta_{(12)(34)},\quad d_2=\Delta_{(13)(24)},\quad
 d_3=\Delta_{(14)(23)},\qquad g=\sum_{i<j}w_{ij}.
\]
For a real symmetric matrix write
\[
 C=\begin{pmatrix}r_1&u&v\\u&r_2&w\\v&w&r_3\end{pmatrix},
 \quad c=(r_1,r_2,r_3,u,v,w)^T,
 \quad \ell(c)=\operatorname{coords}\operatorname{adj}C.
\]
Only in this display does the scalar \(w=C_{23}\) differ from the indexed weights \(w_{ij}\).

The following table defines linear vectors \(l_e\) and linear forms \(b_e(c),s_e(c)\):

| Transposition \(e\) | \(l_e^T\) | \(b_e(c)\) | \(s_e(c)\) | Double-gap index \(q(e)\) |
|---|---|---|---|---:|
| 12 | \((-1,1,-1,0,-2,0)\) | \(u-w\) | \(r_2-v\) | 1 |
| 13 | \((1,-1,-1,0,0,-2)\) | \(u-v\) | \(r_1-w\) | 2 |
| 14 | \((-1,-1,1,-2,0,0)\) | \(v-w\) | \(r_3-u\) | 3 |
| 23 | \((-1,-1,1,2,0,0)\) | \(v+w\) | \(r_3+u\) | 3 |
| 24 | \((1,-1,-1,0,0,2)\) | \(u+v\) | \(r_1+w\) | 2 |
| 34 | \((-1,1,-1,0,2,0)\) | \(u+w\) | \(r_2+v\) | 1 |

Write \(z_e(c)=l_e^T\ell(c)\). Exact identities in the canonical coefficient model give
\[
 A_{\mathbb R}=\sum_e w_e l_el_e^T,\qquad e_{\mathbb R}=0,
\]
and
\[
 c^T(D_0)_{\mathbb R}c=
 \sum_e w_e\bigl(4b_e(c)^2-2z_e(c)\bigr)
 +\alpha(r_1-r_2)^2+\beta(r_2-r_3)^2+\gamma(r_1-r_3)^2,
\]
where
\[
 \alpha=(d_1+d_2-d_3)/2,\quad
 \beta=(d_1+d_3-d_2)/2,\quad
 \gamma=(d_2+d_3-d_1)/2.
\]
These formulas hold on all 70 formal identity-contact compound coefficient directions, not merely actual spectral samples.

## 2. Original supporting inequalities control the signed Laplacian

Set
\[
 W_1=w_{12}+w_{34},\quad W_2=w_{13}+w_{24},\quad
 W_3=w_{14}+w_{23}.
\]
The original inverse-four-cycle gap sums satisfy
\[
 S_\alpha=\Delta_{(1243)}+\Delta_{(1342)}=2\alpha+4W_3\ge0,
\]
\[
 S_\beta=\Delta_{(1234)}+\Delta_{(1432)}=2\beta+4W_2\ge0,
\]
\[
 S_\gamma=\Delta_{(1324)}+\Delta_{(1423)}=2\gamma+4W_1\ge0.
\]
Also \(\alpha+\beta=d_1\ge0\), \(\alpha+\gamma=d_2\ge0\), and \(\beta+\gamma=d_3\ge0\). Thus at most one of \(\alpha,\beta,\gamma\) is negative.

A **baseline atom** has \(\tau_e=4\), the other transposition gaps zero, and all \(d_q=0\). Its blocks have \(g=1\), \(A=l_el_e^T\), and quadratic cofactor form
\[
 Q_e(c)=4b_e(c)^2-2z_e(c).
\]
A **special atom** has the same transposition data and \(d_{q(e)}=4\), other double gaps zero. Direct polynomial expansion gives
\[
 Q_e^{\rm sp}(c)=4s_e(c)^2+2z_e(c).
\]
The table supplies every one of these 12 exact square identities.

If the three Laplacian weights are nonnegative, the data decompose into baseline atoms and a nonnegative Laplacian remainder. Otherwise, for example \(\alpha=-t<0\), we have \(\beta,\gamma\ge t\) and \(W_3\ge t/2\). Choose nonnegative extraction amounts from \(w_{14},w_{23}\) totaling \(t/2\), not exceeding their respective capacities. Replace those portions of their baseline atoms by special atoms. Their Laplacian contribution is \((\alpha,\beta,\gamma)=(-t,t,t)\); the remaining weights are \((0,\beta-t,\gamma-t)\ge0\). All baseline capacities left over are nonnegative.

The other two cases extract from groups 2 or 1. This is an explicit decomposition valid also on ties and zero-capacity faces; there is no genericity assumption. It preserves \(A,D,g\) exactly.

## 3. Scalar bound for every real symmetric formal cofactor

Weighted Cauchy–Schwarz gives
\[
 \sqrt g\sqrt{\ell^TA_{\mathbb R}\ell}
 =\sqrt{\sum_e w_e}\sqrt{\sum_e w_e z_e^2}
 \ge\sum_e w_e|z_e|.
\]
For each baseline atom,
\[
 Q_e(c)+2|z_e|=4b_e(c)^2+2(|z_e|-z_e)\ge0,
\]
and for each special atom,
\[
 Q_e^{\rm sp}(c)+2|z_e|=4s_e(c)^2+2(|z_e|+z_e)\ge0.
\]
Apply the decomposition above and add the remaining nonnegative Laplacian squares. This proves
\[
 c^T(D_0)_{\mathbb R}c+
 2\sqrt g\sqrt{\ell^TA_{\mathbb R}\ell}\ge0.
\]
Because \(e_{\mathbb R}=0\), multiplying by \(g>0\) is exactly the scalar necessary Schur inequality. If \(g=0\), all transposition weights vanish and the original reserve inequalities force \(\alpha,\beta,\gamma\ge0\), so the restricted quartic is directly a nonnegative Laplacian; no division is needed. This subsumes the [earlier three-dimensional diagonal proof](DIAGONAL_COFACTOR_BOUND.md).

## 4. Stronger support SOS when the Cayley matrix is real symmetric

Use the existing exact dephased model
\[
 U(T)=ee^T+Y(I+iT)(I-iT)^{-1}Y^T,
\quad G(T)=|\det(I-iT)|^2\bigl(h-F(U(T))\bigr).
\]
Here \(e\) is the normalized all-ones vector, not the Gram coefficient vector. If \(T\) is real symmetric, \(U(-T)=\overline{U(T)}\), so all minor absolute squares, and hence \(G\), are even in \(T\). In the canonical model, therefore,
\[
 G(T)=x^TA_{\mathbb R}x+c^T(D_0)_{\mathbb R}c+g\,d^2,
\]
where \(x=\operatorname{coords}T\), \(c=\operatorname{coords}\operatorname{adj}T\), and \(d=\det T\). No cubic or quintic term survives.

The adjugate identity \(\operatorname{adj}(\operatorname{adj}T)=dT\), valid also for singular matrices, gives \(z_e(c)=d\,l_e^Tx\). Thus each baseline and special atom has the **actual polynomial** SOS
\[
 \boxed{G_e(T)=(l_e^Tx-d)^2+4b_e(c)^2,}
\]
\[
 \boxed{G_e^{\rm sp}(T)=(l_e^Tx+d)^2+4s_e(c)^2.}
\]
The nonnegative Laplacian remainder contributes its three diagonal-cofactor squares. Applying the same decomposition proves \(G(T)\ge0\) for every real symmetric \(T\). The Cayley denominator is strictly positive, so this proves the support inequality on that entire six-parameter branch, not just the scalar necessary test.

Equivalently, it covers dephased **symmetric unitaries fixing the all-ones vector** in this identity-contact chart; excluded Cayley-boundary points follow by continuity within that symmetric class. It does not say that arbitrary unitaries can be made symmetric by diagonal phase scaling. Nor can an arbitrary maximizing permutation be relabeled without checking what it does to this class. The full complex-Hermitian Cayley branch remains open.


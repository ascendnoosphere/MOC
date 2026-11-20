## 1. Original polynomial model and the rank-nine reduction

The universal part comes from `exact_geometry()`, **not** the special spectral family in `exact_model()`.

For arbitrary spectra and support direction, the complementary-minor determinant expansion writes
\[
F(U)=\sum_{|R|=|S|} k_{R,S}\,|\det U[R,S]|^2,
\]
with real coefficients
\[
k_{R,S}=\Re\!\left(\eta\prod_{i\notin R}a_i\prod_{j\in S}b_j\right).
\]
At a permutation matrix, the corresponding minor square is the indicator that the permutation maps \(R\) onto \(S\). Thus the verifier’s
\[
M_{R,S}=Z_{(R,S),\mathrm{id}}D_G-B_{R,S}
\]
really does represent the identity-contact numerator coefficientwise. Linearity extends identities on these 70 directions to arbitrary actual spectra; no special-family interpolation is involved. See `organized/research/rational_sinkhorn_certificates.py:117–146` and `organized/research/verify_real_cofactor_bound.py:26–36`.

The model’s Cayley formulas are correct. Setting \(C=\operatorname{adj}T\), \(d=\det T\),
\[
\delta=\det(I-iT)=1-\operatorname{tr}C+i(d-\operatorname{tr}T),
\]
and
\[
N=(1+\operatorname{tr}C-id)I-2C+i(2T-\operatorname{tr}T\,I)
\]
satisfies
\[
N=(I+iT)\operatorname{adj}(I-iT).
\]
The signed complementary-index matrix \(J\) gives the exterior-square numerator \(J\bar N J\). This justifies the compound blocks and the common denominator used in `organized/research/rational_sinkhorn_certificates.py:119–130`. I independently checked these polynomial identities on a fully symbolic real symmetric matrix.

**Rank-nine precision.** The six transposition and three double-transposition gap columns are independent. Independently constructing their indicator matrix, I obtained a \(9\times9\) minor of determinant **1**, using zero-based rows
\[
1,2,3,6,7,11,17,18,24.
\]
The verifier then checks reconstruction against **all 70 rows**, not just the nine selected rows (`organized/research/verify_real_cofactor_bound.py:31–51`).

Moreover, the restricted even-profile map genuinely has rank nine: the six transposition \(A\)-matrices are independent, and the three double-gap \(D\)-matrices are independent through their invertible transformation to the three diagonal-difference Laplacian forms.

An important qualification: **rank nine does not describe all original comparison-gap data.** The full matrix of 23 identity-relative comparison-gap columns has rank **13**. Rank nine describes the data retained by these restricted even blocks. The manuscript’s actual formulation is consistent with that distinction (`organized/research/REAL_COFACTOR_BOUND.md:36–52`).

## 2. Claim 1: scalar real-cofactor bound

### Coefficients and signs

The table and coefficient formulas are correct:
\[
A_{\mathbb R}=\sum_e w_e l_el_e^T,\qquad
g=\sum_e w_e,\qquad e_{\mathbb R}=0,
\]
and
\[
Q(c):=c^T(D_0)_{\mathbb R}c
=\sum_e w_e(4b_e^2-2z_e)
+\alpha L_\alpha+\beta L_\beta+\gamma L_\gamma,
\]
where \(z_e=l_e^T\operatorname{coords}(\operatorname{adj}C)\) and the \(L\)’s are the three displayed diagonal-difference squares. The factors \(w_e=\Delta_e/4\), the baseline minus sign, and special plus sign all agree with the original model. See `organized/research/REAL_COFACTOR_BOUND.md:27–50` and `organized/research/verify_real_cofactor_bound.py:35–63`.

For a direct sign/factor check, the double-gap changes contributed by special atoms in groups \(1,2,3\) are respectively
\[
(2,2,-2),\quad(2,-2,2),\quad(-2,2,2)
\]
in \((\alpha,\beta,\gamma)\). The six table identities are exactly
\[
4b_e^2-2z_e+\text{corresponding Laplacian change}
=4s_e^2+2z_e.
\]
I checked all six by symbolic expansion independently of the verifier’s PSD routine.

### Required inequalities and extraction capacity

The proof uses:
- six nonnegative transposition gaps;
- three nonnegative double-transposition gaps;
- the three specified inverse-four-cycle **gap sums**.

All follow from identity maximizing the original 24 costs. The reserve identities have the correct cycle labels and factors:
\[
S_\alpha=2\alpha+4W_3,\quad
S_\beta=2\beta+4W_2,\quad
S_\gamma=2\gamma+4W_1.
\]
They are checked coefficientwise, not inferred from sampled spectra (`organized/research/REAL_COFACTOR_BOUND.md:61–71`; `organized/research/verify_real_cofactor_bound.py:65–68`).

The negative-weight case has sufficient capacity. If \(\alpha=-t<0\), then
\[
\beta\ge t,\qquad\gamma\ge t,\qquad W_3\ge t/2.
\]
Choose, explicitly,
\[
a_{14}=\min(w_{14},t/2),\qquad a_{23}=t/2-a_{14}.
\]
Then \(0\le a_e\le w_e\). Replacing those baseline portions by special atoms contributes
\[
2(a_{14}+a_{23})(-1,1,1)=(-t,t,t),
\]
leaving \((0,\beta-t,\gamma-t)\ge0\). The other two cases are identical with the appropriate groups. Pairwise nonnegative sums prohibit two negative Laplacian weights. Thus no genericity or strictly positive capacity is hidden in `organized/research/REAL_COFACTOR_BOUND.md:73–85`.

These are **algebraic atoms**; they need not individually be realizable spectral instances. That is harmless: their polynomial identities and nonnegative decomposition weights are what the argument needs.

### Scalar conclusion, including \(g=0\)

The decomposition gives
\[
Q(c)+2\sum_e w_e|z_e|\ge0.
\]
Weighted Cauchy–Schwarz gives
\[
\sum_e w_e|z_e|
\le\sqrt{\sum_e w_e}\sqrt{\sum_e w_ez_e^2}
=\sqrt g\sqrt{\ell^TA_{\mathbb R}\ell}.
\]
Consequently,
\[
Q(c)+2\sqrt g\sqrt{\ell^TA_{\mathbb R}\ell}\ge0
\]
for **every formal real symmetric \(C\)**, whether or not it is an actual adjugate. This proves Claim 1 (`organized/research/REAL_COFACTOR_BOUND.md:89–108`).

For \(g>0\), multiplication by \(g\), together with \(e_{\mathbb R}=0\), gives precisely the stated scalar necessary Schur condition.

For \(g=0\), all \(w_e=0\). The reserve inequalities then force \(\alpha,\beta,\gamma\ge0\), so \(Q(c)\ge0\) directly. Thus the degenerate case is covered without division by \(g\). It would be useful to state this explicitly beside `organized/research/REAL_COFACTOR_BOUND.md:108`; its omission is explanatory, not a proof failure.

## 3. Claim 2: actual real-Cayley SOS

### Evenness is justified

For real symmetric \(T\), the real basis \(Y\) gives
\[
U(-T)=\overline{U(T)}.
\]
Crucially, the complementary-minor formula above ensures
\[
F(\bar U)=F(U)
\]
even for complex spectra: it is a real linear combination of **minor absolute squares**. Also \(|\det(I-iT)|^2\) is even. Hence \(G(-T)=G(T)\), so its homogeneous cubic and quintic parts vanish. The verifier additionally checks this for every one of the 70 profiles (`organized/research/REAL_COFACTOR_BOUND.md:112–121`; `organized/research/verify_real_cofactor_bound.py:39–44`).

### Canonical absorption is correct

Evenness alone would not identify the remaining blocks; the absorption step matters. Here it is correctly implemented:

- degree-two \(1\cdot c_j\) terms are absorbed using
  \[
  c_j(T)=x^TL_jx;
  \]
- degree-four \(x_jd\) terms are absorbed using
  \[
  dx_j=c^TL_jc;
  \]
- degree six is \(gd^2\).

The factors **2** in both absorptions are exactly those required by the symmetric Gram cross terms (`organized/research/verify_real_cofactor_bound.py:32–37`). The constant term vanishes at identity contact. Therefore
\[
G=x^TA_{\mathbb R}x+c^T(D_0)_{\mathbb R}c+gd^2
\]
is the actual numerator, not a proposed replacement.

### SOS and singular matrices

The polynomial identity
\[
\operatorname{adj}(\operatorname{adj}T)=dT
\]
gives \(z_e(c)=d\,l_e^Tx\), including when \(T\) is singular. Thus baseline atoms yield
\[
(l_e^Tx)^2-2d\,l_e^Tx+d^2+4b_e(c)^2
=(l_e^Tx-d)^2+4b_e(c)^2,
\]
and special atoms yield
\[
(l_e^Tx+d)^2+4s_e(c)^2.
\]
The same nonnegative extraction decomposition therefore proves the actual polynomial SOS; this is stronger than merely passing the scalar test (`organized/research/REAL_COFACTOR_BOUND.md:123–130`).

For real symmetric \(T\), with eigenvalues \(\lambda_j\),
\[
|\det(I-iT)|^2=\prod_j(1+\lambda_j^2)>0.
\]
There is no finite-chart denominator singularity.

### Symmetric Cayley boundary

The continuity assertion is also sound. A symmetric unitary on \(e^\perp\) has the form \(A+iB\), with \(A,B\) real symmetric. Unitarity implies \(AB=BA\), so they are simultaneously diagonalizable by a real orthogonal matrix. Approximate any eigenphase \(-1\) by phases different from \(-1\); these have real Cayley parameters. This approximates within the same symmetric, \(e\)-fixing class, without changing the spectral support hypothesis. See `organized/research/REAL_COFACTOR_BOUND.md:132`.


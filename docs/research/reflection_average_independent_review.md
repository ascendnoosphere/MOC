## 2. The underlying polynomial really represents the determinant

For arbitrary diagonal complex spectra, complementary-minor expansion gives
\[
F(U)=\sum_{|R|=|S|}k_{R,S}|\det U[R,S]|^2,
\]
where
\[
k_{R,S}=\Re\!\left(
\eta\prod_{i\notin R}a_i\prod_{j\in S}b_j
\right).
\]
At permutation matrices, these minor squares become assignment indicators. Thus checking all 70 formal profiles is sufficient by linearity; no special spectral-family interpolation is required.

Importantly, the new verifier calls `exact_geometry()`, **not** the specialized `exact_model()` family. See `organized/research/rational_sinkhorn_certificates.py:117–146`.

Here is my independent check of the shared geometry. For a general Hermitian \(3\times3\) matrix \(T\), put \(C=\operatorname{adj}T\), \(d=\det T\). Then
\[
\delta=\det(I-iT)
=1-\operatorname{tr}C+i(d-\operatorname{tr}T),
\]
and
\[
N=(1+\operatorname{tr}C-id)I-2C
+i(2T-\operatorname{tr}T\,I)
=(I+iT)\operatorname{adj}(I-iT).
\]
Consequently \(V=N/\delta\).

With the signed complementary-index matrix
\[
J=\begin{pmatrix}0&0&1\\0&-1&0\\1&0&0\end{pmatrix},
\]
direct symbolic minor expansion gives
\[
\bigwedge\nolimits^2N=\delta\,J\bar N J.
\]
Therefore \(\bigwedge^2V=J\bar N J/\delta\), justifying the common-denominator compound blocks in `organized/research/rational_sinkhorn_certificates.py:119–130`. This check retained all three independent imaginary entries.

## 3. Canonical absorption is correct, including all nine coordinates

The canonical expression
\[
G_{\rm ev}(T)=t^TAt+c^TD_0c+gd^2
\]
is the **actual even numerator**, not merely a candidate Gram expression.

If \(L_j\) represents the quadratic polynomial \((\operatorname{coords}\operatorname{adj}T)_j\), then
\[
c_j=t^TL_jt,\qquad dt_j=c^TL_jc.
\]
The second identity follows from
\[
\operatorname{adj}(\operatorname{adj}T)=dT.
\]
Hence the constant/cofactor Gram cross terms contribute \(2M_{0,c_j}L_j\) to \(A\), and the \(t_jd\) cross terms contribute \(2M_{t_j,d}L_j\) to \(D_0\). The factors of two and signs are correct.

The verifier additionally subtracts these canonical blocks from the **complete even polynomial** and checks that every residual coefficient vanishes. It does not rely merely on matching selected Gram entries. See `organized/research/verify_reflection_average_sos.py:25–35`.

The reconstruction of every entry of both \(9\times9\) matrices is then checked against all 70 profile rows, using the six transposition and three double-transposition gap columns; also
\[
g=\frac14\sum_{i<j}\Delta_{(ij)}=\sum_e w_e.
\]
See `organized/research/verify_reflection_average_sos.py:21–43`.

The manuscript correctly distinguishes this rank-nine even-data reduction from the rank-13 unsymmetrized comparison data: `organized/research/REFLECTION_AVERAGE_SOS.md:45–50`.

## 4. All twelve atoms survive the imaginary-coordinate audit

The imaginary terms in the displayed table are essential and correctly included. For example, edge \(12\) has
\[
l=-r_1+r_2-r_3-2v,\quad m=p-r,\quad
b=u-w,\quad n=q,\quad s=r_2-v.
\]
Thus its baseline atom contains both \(4(p-r)^2\) on \(T\) and \(4q^2\) on \(C\); its special atom contains \(4(p-r)^2\) on both.

For an explicit independent sign check, on a general Hermitian matrix \(H\), write
\[
z=l(\operatorname{adj}H).
\]
Direct expansion gives
\[
z=(u-w)^2+(p+r)^2-v^2-q^2
-r_1r_2+r_1r_3-r_2r_3+2r_2v.
\]
Using the manuscript’s \(L_\alpha,L_\beta,L_\gamma\), this yields
\[
4s^2+4m^2-4b^2-4n^2+4z
=2(L_\alpha+L_\beta-L_\gamma).
\]
This is exactly the change associated with adding double gap \(d_1=4\).

I independently verified the corresponding identity for all six edges, with double-gap changes
\[
2(L_\alpha+L_\beta-L_\gamma),\quad
2(L_\alpha-L_\beta+L_\gamma),\quad
2(-L_\alpha+L_\beta+L_\gamma)
\]
for groups \(1,2,3\), respectively.

For an actual Cayley parameter, \(z(C)=d\,l(T)\). Therefore the baseline and special completions are precisely
\[
(l(T)-d)^2+4m(T)^2+4b(C)^2+4n(C)^2,
\]
\[
(l(T)+d)^2+4m(T)^2+4s(C)^2+4m(C)^2.
\]
All six pairs agree with `organized/research/REFLECTION_AVERAGE_SOS.md:66–104` and the exact factors obtained in `organized/research/verify_reflection_average_sos.py:46–56`.

## 5. Extraction preserves the full matrices—not only their real restrictions

The decomposition argument is valid.

The double-gap inequalities give
\[
\alpha+\beta=d_1\ge0,\quad
\alpha+\gamma=d_2\ge0,\quad
\beta+\gamma=d_3\ge0,
\]
so at most one of \(\alpha,\beta,\gamma\) is negative. The original inverse-four-cycle gap sums give the required reserves:
\[
2\alpha+4W_3\ge0,\quad
2\beta+4W_2\ge0,\quad
2\gamma+4W_1\ge0.
\]
These are exact profile identities, checked at `organized/research/verify_reflection_average_sos.py:57–60`.

If \(\alpha=-t<0\), then
\[
\beta,\gamma\ge t,\qquad w_{14}+w_{23}\ge t/2.
\]
The explicit choice
\[
a_{14}=\min(w_{14},t/2),\qquad
a_{23}=t/2-a_{14}
\]
satisfies both capacities. Replacing these baseline portions by special atoms contributes \((-t,t,t)\) to the represented boundary weights, leaving
\[
(0,\beta-t,\gamma-t)\ge0.
\]

The crucial extension beyond the real branch is sound: the special-minus-baseline changes are identities of the **full nine-coordinate quadratic forms**, including the imaginary squares. Thus the replacements preserve \(A,D_0,g\), not just their real restrictions. See `organized/research/REFLECTION_AVERAGE_SOS.md:106–118`.

The atoms need not separately arise from spectra or satisfy every comparison inequality. They are algebraic coefficient atoms used with nonnegative weights; that is sufficient.

### Degenerate cases

- **\(g=0\):** Since all \(w_e\ge0\), every \(w_e=0\). The reserve inequalities then force \(\alpha,\beta,\gamma\ge0\). Only the nonnegative boundary SOS remains.
- **Ties:** All arguments use non-strict inequalities, so ties and saturated capacities are covered.
- **Singular \(T\):** The adjugate identity is polynomial. No inverse of \(T\), \(C\), or division by \(d\) is used.
- **Denominator:** For Hermitian \(T\),
  \[
  D(T)=\det(I+T^2)=\prod_j(1+\lambda_j^2)>0.
  \]

These cases require no additional hypothesis.

## 6. Global Sinkhorn reduction preserves BOTH summands

This potentially dangerous step is correct.

For any diagonal unitaries \(L,R\) and any unitary \(X\),
\[
F(LXR)=F(X),
\]
because \(R\) commutes with \(D_b\), \(L\) commutes with \(D_a\), and the resulting matrix sum is conjugated by \(L\).

Thus if Sinkhorn gives \(W=LUR\), then
\[
F(W)=F(U),
\]
and, independently,
\[
F(W^*)=F(R^*U^*L^*)=F(U^*).
\]
The **same** phase choice works for the pair. No adjoint-equivariant choice of Sinkhorn phases is necessary.

The external existence theorem indeed applies to every unitary, not merely matrices with nonzero entries or instances where an iterative algorithm converges. See `organized/research/external/1408.5728v3.txt:943–999` and `organized/research/SINKHORN_GLOBAL_REDUCTION.md:5–15`.

After dephasing, \(W\) fixes \(e\), hence has residual block \(V\in U(3)\). Approximate its eigenphases to avoid \(-1\), retaining the same eigenvectors. The resulting residual unitaries lie in the Hermitian Cayley chart and converge to \(V\); their adjoints converge simultaneously. Continuity therefore extends the averaged inequality to the entire boundary. This validates `organized/research/REFLECTION_AVERAGE_SOS.md:120–126`.

## 7. The partner at another maximizing contact is exactly \(PU^*P\)

For a maximizing permutation matrix \(P\), set
\[
D_b'=PD_bP^*,\qquad U'=UP^*.
\]
Then identity is maximizing for the relabeled problem and
\[
F_{a,b'}(U')=F_{a,b}(U).
\]
Reflection gives
\[
F_{a,b'}(U'^*)=F_{a,b}(PU^*P).
\]
Therefore
\[
\boxed{\frac{F(U)+F(PU^*P)}2\le F(P).}
\]

There is no missing adjoint on the final \(P\). Indeed,
\[
R_P(R_P(U))=U,\qquad R_P(P)=P.
\]
The manuscript’s formula is correct even for non-involutive permutation matrices: `organized/research/REFLECTION_AVERAGE_SOS.md:128–132`.


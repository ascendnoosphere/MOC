# Scalar Schur bound on the full real diagonal cofactor subspace

This earlier derivation is now subsumed by [the stronger six-dimensional real-cofactor bound and real-Cayley support SOS](REAL_COFACTOR_BOUND.md). It is retained for its transparent three-variable atom argument.

**Scope:** a necessary condition for the canonical Gram completion, for every real diagonal formal cofactor matrix. This is not the full nine-coordinate inequality, not a simultaneous PSD completion, and not unrestricted MOC4. It uses only the original support-gap inequalities and universal coefficient identities; the stronger nonlinear actual-spectral trace linkage is not needed for this subspace.

## 1. Coefficients read from the original 24 gaps

Write \(t_{ij}=\Delta_{(ij)}\ge0\), and
\[
 d_1=\Delta_{(12)(34)},\quad d_2=\Delta_{(13)(24)},\quad
 d_3=\Delta_{(14)(23)}.
\]
Define
\[
 w_1=(t_{12}+t_{34})/4,\quad
 w_2=(t_{13}+t_{24})/4,\quad
 w_3=(t_{14}+t_{23})/4,
\quad g=w_1+w_2+w_3,
\]
\[
 s_1=(-1,1,-1)^T,\quad s_2=(1,-1,-1)^T,\quad
 s_3=(-1,-1,1)^T.
\]
For \(C=\operatorname{diag}(r_1,r_2,r_3)\), its adjugate coordinates are
\(\ell=(r_2r_3,r_1r_3,r_1r_2)^T\). The restricted coefficient blocks satisfy
\[
 A_{\rm diag}=\sum_j w_js_js_j^T,\qquad e_{\rm diag}=0.
\]
Put
\[
 \alpha=(d_1+d_2-d_3)/2,\quad
 \beta=(d_1+d_3-d_2)/2,\quad
 \gamma=(d_2+d_3-d_1)/2.
\]
Let \(L(\alpha,\beta,\gamma)\) be the signed graph Laplacian with edge weights \(\alpha\) on 12, \(\gamma\) on 13, and \(\beta\) on 23. Then
\[
 \boxed{(D_0)_{\rm diag}=L(\alpha,\beta,\gamma)+gI-A_{\rm diag}.}
\]
Do **not** assume all three edge weights are nonnegative when \(g>0\).

The original inverse-four-cycle gap sums are exactly
\[
 S_\alpha=2\alpha+4w_3\ge0,\quad
 S_\beta=2\beta+4w_2\ge0,\quad
 S_\gamma=2\gamma+4w_1\ge0.
\]
Also \(\alpha+\beta=d_1\ge0\), \(\alpha+\gamma=d_2\ge0\), \(\beta+\gamma=d_3\ge0\). These are precisely the constraints used below.

## 2. An elementary atom decomposition

Set \(z_j=s_j^T\ell\). Cauchy–Schwarz gives
\[
 \sqrt g\sqrt{\ell^TA_{\rm diag}\ell}
 =\sqrt{\sum_jw_j}\sqrt{\sum_jw_jz_j^2}
 \ge\sum_jw_j|z_j|.
\]
A baseline atom with weight one has \(g=1\), \(A=s_js_j^T\), and \(L=0\). Its quartic quadratic form is
\[
 r^TDr=r^T(I-s_js_j^T)r=-2z_j,
\]
so adding \(2|z_j|\) is nonnegative.

If \(\alpha,\beta,\gamma\ge0\), the full data are the sum of the weighted baseline atoms and a PSD graph Laplacian. This already proves the desired bound.

Otherwise at most one edge weight is negative, by the three nonnegative pair sums. For example, let \(\alpha=-t<0\). Then \(\beta,\gamma\ge t\), and \(S_\alpha\ge0\) gives \(w_3\ge t/2\). Extract weight \(\mu=t/2\) from the third baseline atom and replace it by the special atom
\[
 g=1,\quad A=s_3s_3^T,\quad
 (\alpha,\beta,\gamma)=(-2,2,2).
\]
The remaining Laplacian has weights \((0,\beta-t,\gamma-t)\ge0\), and every remaining baseline weight is nonnegative. The special atom satisfies exactly
\[
 r^TDr=2z_3+4r_3^2,\qquad
 r^TDr+2|z_3|=4\max(z_3,0)+4r_3^2\ge0.
\]
The cases \(\gamma<0\) and \(\beta<0\) use the first and second atoms, respectively, with \(4r_2^2\) and \(4r_1^2\). Each special atom has the negative edge opposite the positive coordinate of its \(s_j\).

The decomposition preserves \(A,g,D\) exactly. Because Cauchy–Schwarz supplies at least the sum of the individual weighted absolute-value reserves, summing these nonnegative atom bounds and the remaining PSD Laplacian proves
\[
 \boxed{r^T(D_0)_{\rm diag}r+
       2\sqrt g\sqrt{\ell^TA_{\rm diag}\ell}\ge0.}
\]
Multiplying by \(g>0\), and using \(e_{\rm diag}=0\), is the scalar necessary Schur bound on every real diagonal cofactor vector. The \(g=0\) branch has the separately proved complete boundary completion.


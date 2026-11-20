# An explicit four-scalar odd profile and its actual spectral determinant

**Status:** independently **VALID** exact symbolic reduction and actual-spectral identities; not a positivity theorem or an unrestricted MOC4 proof. The [independent audit](odd_profile_independent_review.md) also reconstructs the entire odd polynomial by a separate Cayley-series calculation without importing the shared compound model. This supplements the [14-variable completion](PARITY_REDUCED_COMPLETION.md) and [reflection-average SOS](REFLECTION_AVERAGE_SOS.md) with explicit formulas for the part those positive averages do not bound.

## 1. Four original three-cycle comparisons give the entire odd part

At an identity support contact write
\[
 \delta_\pi=\prod_{i=0}^3(a_i+b_{\pi(i)}),\qquad
 \Delta_\pi=\Re\{\eta(\delta_{\rm id}-\delta_\pi)\}\ge0.
\]
The support scalar eta need not be normalized. For increasing triples define
\[
 J_{ijk}=\Delta_{(ijk)}-\Delta_{(ikj)}
 =\Re\{\eta(\delta_{(ikj)}-\delta_{(ijk)})\}.
\]
Use the order \(J=(J_{012},J_{013},J_{023},J_{123})^T\). In the canonical coordinates
\[
 t=(T_{11},T_{22},T_{33},\Re T_{12},\Im T_{12},\Re T_{13},\Im T_{13},\Re T_{23},\Im T_{23}),
\]
the three quintic coefficients and fourth cubic coefficient satisfy
\[
 \begin{pmatrix}e_4\\e_6\\e_8\\\chi\end{pmatrix}
 =\begin{pmatrix}
 -1/4&-1/4&1/4&1/4\\
 -1/4&1/4&1/4&-1/4\\
 1/4&1/4&1/4&1/4\\
 2&-2&2&-2
 \end{pmatrix}J.
\]
Here chi is precisely the coefficient of \(t_4t_6t_8\) in the cubic part G3. The complete odd part is
\[
 G_{\rm odd}=G_3+G_5
 =e_4p_0(t)+e_6p_1(t)+e_8p_2(t)+\chi p_3(t)
 +2d(e_4c_4+e_6c_6+e_8c_8),
\]
with \(c=\operatorname{coords}\operatorname{adj}T\), \(d=\det T\), and
\[
 p_3(t)=t_4t_6t_8+\tfrac12(t_1t_5t_6-t_0t_7t_8-t_2t_3t_4).
\]
All four explicit cubics, including the three longer p0,p1,p2, are given as exact expressions and a rational monomial table in the machine-readable record. Their extraction/reconstruction was checked on **all 70 compound-coefficient directions**: cubic rank4, e rank3, joint rank4. This is a full coefficient identity, not a sampled fit.

The scaled transformation \((e_4,e_6,e_8,\chi/8)=HJ/4\) has a real Hadamard matrix H with \(HH^T=4I\). In particular
\[
 e_4^2+e_6^2+e_8^2+\chi^2/64=\tfrac14\sum_rJ_r^2.
\]
This makes all four odd parameters explicit in the **original comparisons**, without imposing a fictitious independent positivity constraint on them.

## 2. Supported three-cycle budgets, with their exact normalization

The additive matrix \((a_i+b_j)\) has rank at most two, so its principal order-three determinants vanish. Equivalently, directly expanding three products gives
\[
 \Delta_{(ijk)}+\Delta_{(ikj)}
 =\Delta_{(ij)}+\Delta_{(ik)}+\Delta_{(jk)}=:S_{ijk}.
\]
Thus \(|J_{ijk}|\le S_{ijk}\). The canonical highest coefficient also obeys
\[
 g=\tfrac14\sum_{i<j}\Delta_{(ij)}.
\]
Both identities are checked in every formal coefficient direction. Summing the triangle budgets gives \(\sum S_{ijk}=8g\), hence \(|e_j|\le2g\) and \(|\chi|\le16g\). These are **necessary supported bounds only**. They do not by themselves establish domination of the odd polynomial.

## 3. The fourth parameter is an actual Segre determinant

Define
\[
 \mathcal D=\det\begin{pmatrix}
 1&a_0&b_0&a_0b_0\\
 1&a_1&b_1&a_1b_1\\
 1&a_2&b_2&a_2b_2\\
 1&a_3&b_3&a_3b_3
 \end{pmatrix}.
\]
The entries in each row are coordinates of a rank-one tensor, up to fixed column order. Exact expansion of the four oriented comparisons gives
\[
 \boxed{\chi=-4\Re(\eta\mathcal D).}
\]
This is an actual spectral linkage, not a replacement by arbitrary unrelated 70 coefficients.

Set
\[
 A=(a_0-a_1)(a_2-a_3),\quad B=(a_0-a_2)(a_1-a_3),\quad C=(a_0-a_3)(a_1-a_2),
\]
and define A',B',C' with b in place of a. Then
\[
 A-B+C=0,\quad A'-B'+C'=0,\quad
 \mathcal D=AB'-BA'.
\]
The first two are the order-two three-term Plücker relations. The third follows by expanding the displayed determinant. When the relevant denominators are nonzero, \(\mathcal D=0\) is exactly equality of the ratios A/B and A'/B' (one cross-ratio convention). The polynomial identities themselves have **no distinctness or denominator assumptions**.

Let
\[
 z_0=AA',\quad z_1=BB',\quad z_2=CC'.
\]
The same Plücker relation now supplies a nonlinear odd/even spectral identity:
\[
 \boxed{\mathcal D^2=(z_0+z_1-z_2)^2-4z_0z_1.}
\]
For opposite pairs \((ij),(kl)\), direct multiplication further gives
\[
 \Re\{\eta[(a_i-a_j)(b_i-b_j)(a_k-a_l)(b_k-b_l)]\}
 =\Delta_{(ij)}+\Delta_{(kl)}-\Delta_{(ij)(kl)}.
\]
Thus the **support-direction real projections** \(\Re(\eta z_r)\) of the three z coefficients are already in the supported even data; the fourth odd parameter comes from their actual common spectral factorization.

The verifier checks these formulas as identities in **eight independent complex symbols**, including all three opposite-pair relations. These are not numerical spectral examples. Repeated spectra, eta=0, and vanishing paired sums cause no division problem.


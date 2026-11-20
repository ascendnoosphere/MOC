## 2. Four signed gaps and the normal form

The orientation convention is internally consistent:
\[
J_{ijk}=\Delta_{(ijk)}-\Delta_{(ikj)}
=\Re\{\eta(\delta_{(ikj)}-\delta_{(ijk)})\}.
\]
With triples ordered \(012,013,023,123\), I independently recovered exactly
\[
\begin{pmatrix}e_4\\e_6\\e_8\\\chi\end{pmatrix}
=
\begin{pmatrix}
-\frac14&-\frac14&\frac14&\frac14\\
-\frac14&\frac14&\frac14&-\frac14\\
\frac14&\frac14&\frac14&\frac14\\
2&-2&2&-2
\end{pmatrix}J.
\]
The signs depend on the specified permutation action and upper-triangular imaginary-coordinate convention; under those conventions they are correct.  
**Reference:** `organized/research/ODD_PROFILE_LINKAGE.md:14-29`.

For every formal compound direction, the independent series calculation verified
\[
G_3=\sum_{r=0}^2e_{2r+4}p_r+\chi p_3,\qquad
G_5=2d(e_4c_4+e_6c_6+e_8c_8),
\]
including all coefficients of the three longer saved cubics. In particular,
\[
p_3=t_4t_6t_8+\frac12(t_1t_5t_6-t_0t_7t_8-t_2t_3t_4)
\]
is correct, and none of \(p_0,p_1,p_2\) contributes to \(t_4t_6t_8\). Thus **\(\chi\) really is that cubic coefficient**, not merely a convenient fourth parameter.  
**Reference:** `organized/research/ODD_PROFILE_LINKAGE.md:31-41`.

The Hadamard normalization also checks:
\[
(e_4,e_6,e_8,\chi/8)^T=HJ/4,\qquad HH^T=4I,
\]
so
\[
e_4^2+e_6^2+e_8^2+\chi^2/64=\frac14\sum J_r^2.
\]
No support or positivity hypothesis is needed for this equality.  
**Reference:** `organized/research/ODD_PROFILE_LINKAGE.md:43-46`.

## 3. What “all 70 directions” proves—and does not prove

The coefficientwise argument is legitimate. The determinant expansion has terms
\[
\det(D_a+UD_bU^*)
=\sum_{\substack{I,J\subseteq\{0,1,2,3\}\\|I|=|J|}}
\left(\prod_{i\notin I}a_i\right)
\left(\prod_{j\in J}b_j\right)
|\det U[I,J]|^2,
\]
and
\[
\sum_{k=0}^4\binom4k^2=70.
\]
Consequently, an identity checked on every formal compound direction specializes to every actual complex spectrum after taking the real support functional.

This does **not** assert that the 70 formal coefficients are independently realizable by spectra. Nor does formal rank four mean that four odd parameters can be chosen freely while holding supported even spectral data fixed. The document correctly distinguishes the linear normal-form statement from the additional nonlinear actual-spectral identities.  
**References:** `organized/research/ODD_PROFILE_LINKAGE.md:41`, `organized/research/ODD_PROFILE_LINKAGE.md:73-77`.

My independent calculation confirmed the formal cubic rank four and the four-dimensional signed-comparison map. The first three rows of the displayed extraction matrix have rank three. Thus the reported ranks are not merely accepted from the shared model.

## 4. Triangle budgets and the factor \(1/4\)

The three-cycle sum identity is correct:
\[
\Delta_{(ijk)}+\Delta_{(ikj)}
=\Delta_{(ij)}+\Delta_{(ik)}+\Delta_{(jk)}.
\]
One direct proof expands the zero determinant of the \(3\times3\) additive matrix \((a_r+b_s)\) and multiplies by the untouched fourth factor. This is a polynomial proof and does not require that factor to be nonzero. I independently checked all four spectral identities by expansion.  
**Reference:** `organized/research/ODD_PROFILE_LINKAGE.md:51-55`.

The highest coefficient satisfies
\[
g=\frac14\sum_{i<j}\Delta_{(ij)}.
\]
Besides the supplied verifier, I checked it independently direction-by-direction using the limiting Cayley matrix
\[
U_\infty=2ee^T-I,
\]
whose squared compound minors determine the coefficient multiplying \(d^2\).  
**Reference:** `organized/research/ODD_PROFILE_LINKAGE.md:56-60`.

At an identity support contact, all gaps are nonnegative, hence
\[
|J_{ijk}|\le S_{ijk}.
\]
Every edge occurs in two of the four triangles, giving
\[
\sum S_{ijk}=2\sum_{i<j}\Delta_{(ij)}=8g.
\]
The displayed extraction matrix then yields precisely
\[
|e_j|\le2g,\qquad |\chi|\le16g.
\]
These are necessary bounds, not domination of the odd polynomial. If \(g=0\), these inequalities do force all four odd parameters to vanish; no division by \(g\) is involved.

## 5. Segre determinant, Plücker relation, and quadratic linkage

Independent expansion gives
\[
2(J^{\mathbb C}_{012}-J^{\mathbb C}_{013}
  +J^{\mathbb C}_{023}-J^{\mathbb C}_{123})
=-4\mathcal D,
\]
where \(J^{\mathbb C}_{ijk}=\delta_{(ikj)}-\delta_{(ijk)}\). Applying \(\Re(\eta\,\cdot)\) proves the stated sign and factor:
\[
\boxed{\chi=-4\Re(\eta\mathcal D)}.
\]
**Reference:** `organized/research/ODD_PROFILE_LINKAGE.md:64-75`.

The bracket identities are likewise correct:
\[
A-B+C=0,\quad A'-B'+C'=0,\quad
\mathcal D=AB'-BA'.
\]
The cross-ratio interpretation is valid when \(BB'\ne0\); otherwise only the division-free polynomial identity should be used, as the document already specifies.  
**Reference:** `organized/research/ODD_PROFILE_LINKAGE.md:79-88`.

There is a short transparent derivation of the quadratic identity. Since \(C=B-A\) and \(C'=B'-A'\),
\[
z_0+z_1-z_2=AB'+BA'.
\]
Therefore
\[
(z_0+z_1-z_2)^2-4z_0z_1
=(AB'+BA')^2-4AB'BA'
=(AB'-BA')^2=\mathcal D^2.
\]
This proves the boxed relation directly, without genericity assumptions or interpreting a complex square as an ordered quantity.  
**Reference:** `organized/research/ODD_PROFILE_LINKAGE.md:90-96`.

## 6. Double-transposition signs and the wording correction

For disjoint transpositions \(p=(ij)\), \(q=(kl)\), direct factorization gives
\[
\delta_{\rm id}-\delta_p-\delta_q+\delta_{pq}
=(a_i-a_j)(b_i-b_j)(a_k-a_l)(b_k-b_l).
\]
Thus
\[
\Re(\eta z_r)=\Delta_p+\Delta_q-\Delta_{pq}.
\]
I independently checked all three opposite-pair cases. The minus sign on the double-transposition gap is correct.  
**Reference:** `organized/research/ODD_PROFILE_LINKAGE.md:98-102`.

**Minor correction:** the next sentence says the “real parts” of the \(z\) coefficients are in the supported even data. For arbitrary complex \(\eta\), what is known is **\(\Re(\eta z_r)\), not generally \(\Re z_r\)**. Replace that phrase by “their support-direction real projections \(\Re(\eta z_r)\).” The displayed equation is already correct, so this is a wording issue rather than a failed identity.  
**Finding location:** `organized/research/ODD_PROFILE_LINKAGE.md:103`.

## 7. Original-source attribution

Frieden, arXiv:1706.02844v1, Section 3.1 defines the minor conventions and states
\[
P_{Iab}P_{Icd}+P_{Iad}P_{Ibc}=P_{Iac}P_{Ibd}.
\]
Taking \(k=2,n=4,I=\varnothing\), with rows \((1,a_i)\), gives minors \(a_j-a_i\). The products therefore give exactly \(A+C=B\), including the signs. Rank-deficient matrices need not represent Grassmannian points, but the same identity remains valid there by direct polynomial expansion.  
**Reference:** Frieden, [arXiv:1706.02844v1](https://arxiv.org/abs/1706.02844v1), Section 3.1; [ODD_PROFILE_LINKAGE.md](ODD_PROFILE_LINKAGE.md), Section 3.

The source explicitly directs readers elsewhere for a proof of the classical general relation. Accordingly, the accurate attribution is: **Frieden states/cites the classical relation; this project directly proves the specialization it uses.** The project says this correctly.



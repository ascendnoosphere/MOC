# The remaining canonical SOS completion reduces from 25 to 14 real variables

## Exact statement and non-claim

For every identity-contact MOC4 support polynomial, existence of a positive semidefinite Gram in the established 19-coordinate Cayley SOS basis is equivalent to existence of one with **eight cubic gauge parameters and six real-coordinate u parameters**, split into PSD blocks of sizes **9 and 10**.

This is an exact reduction **within the SOS approach**. It neither constructs the remaining completion nor asserts that a nonnegative support polynomial must be SOS. It does not prove unrestricted MOC4. The parameter count and coefficient patterns are independently reproducible by `verify_parity_reduced_completion.py`; [The independent mathematical review](parity_reduction_independent_review.md) returned **VALID** within this SOS-equivalence scope, including an independent audit of the noncubic multiplication-map ranks and raw constant/linear vanishings. It does not certify universal feasibility.

## 1. A second involution, different from the reflection average

For Hermitian T in the fixed real Sinkhorn basis,
\[
 U(-\bar T)=\overline{U(T)}.
\]
Every absolute compound minor square is invariant under entrywise conjugation. Thus for arbitrary complex spectra and any support direction,
\[
 F(\bar U)=F(U),\qquad G(-\bar T)=G(T).
\]
Also \(D(T)=\det(I+T^2)\) is unchanged. This is invariance of the **full original polynomial**, not just its even part. It must not be confused with \(T\mapsto-T\), which interchanges U and U* and generally changes the gap.

Use coordinate order
\[
 (11,22,33,\Re12,\Im12,\Re13,\Im13,\Re23,\Im23).
\]
Let \(R=(0,1,2,3,5,7)\), \(I=(4,6,8)\) be zero-based real and imaginary index lists, and set \(P=\operatorname{diag}(1,1,1,1,-1,1,-1,1,-1)\).

Writing \(q=(t,c,d)\), with \(c=\operatorname{coords}\operatorname{adj}T\), the involution acts by
\[
 t\mapsto-Pt,\quad c\mapsto Pc,\quad d\mapsto-d.
\]
Indeed \(\operatorname{adj}(-\bar T)=\overline{\operatorname{adj}T}\) in order three, while \(\det(-\bar T)=-\det T\). Its matrix on q is the real orthogonal involution
\[
 S=\operatorname{diag}(-P,P,-1).
\]
The +1 coordinates are \((t_I,c_R)\), dimension 9; the -1 coordinates are \((t_R,c_I,d)\), dimension 10.

## 2. Averaging preserves every feasible Gram

If \(G=q^TXq\) with \(X\succeq0\), then
\[
 \bar X=\tfrac12(X+SXS)\succeq0,
\quad q^T\bar Xq=\tfrac12[G(T)+G(-\bar T)]=G(T).
\]
The mixed +/− block of \(\bar X\) vanishes. Conversely, a PSD block-diagonal Gram is of course a feasible Gram for the original problem. Thus the averaging is equivalence-preserving, not a relaxation or an additional positivity assumption.

This is the order-two case of the finite-group invariant-SOS theorem:

- Raymond, Saunderson, Singh and Thomas, [*Symmetric Sums of Squares over k-Subset Hypercubes*, arXiv:1606.05639v2](https://arxiv.org/abs/1606.05639v2), **Theorem A.8**, Appendix A, especially pp. 29–30. The original statement, full Appendix A.1–A.2 proof and all its preceding hypotheses were read.
- Hypotheses here: group \(\mathbb Z/2\), zero ideal, finite-dimensional real invariant polynomial space \(V=\operatorname{span}(t,c,d)\), invariant polynomial G, and the conditional assumption that G is V-SOS. Both irreducible representations are one-dimensional real characters, so no complex/quaternionic real-representation issue enters. The theorem applies to general V, not only homogeneous monomials or discrete hypercubes.
- **Source-level qualification:** Appendix A's unrestricted real-representation preliminaries overstate uniqueness of invariant bilinear forms: a real plane with a 120-degree rotation also has an invariant alternating form. That broad claim is not used here. Both order-two characters in this application are real and one-dimensional, and the elementary averaging proof above independently proves the exact assertion needed.
- The theorem does **not** turn nonnegativity into SOS. No unrestricted claim about complex-type or quaternionic-type real representations is imported.


## 3. The canonical gauge is preserved

The established completion is
\[
 X(K,u)=\begin{pmatrix}
 A&B_0+K&u\\
 (B_0+K)^T&D_0-2L(u)&e\\
 u^T&e^T&g
 \end{pmatrix},\qquad
 c^TL(u)c=u\cdot\operatorname{coords}\operatorname{adj}C.
\]
All original coefficient directions obey
\[
 PAP=A,\quad PD_0P=D_0,\quad PB_0P=-B_0,\quad Pe=-e.
\]
Quartic gauge equivariance is
\[
 PL(u)P=L(Pu).
\]
Consequently averaging replaces
\[
 K\longmapsto(K-PKP)/2,\qquad
 u\longmapsto(u+Pu)/2,
\]
without changing A, B0, D0, e or g. Thus u has zero imaginary-coordinate entries; only its six R entries remain.

The verifier checks these identities on **all 70** coefficient directions, including the full raw 20-coordinate conjugation pattern before absorption. In particular the raw constant/determinant coefficient is zero, so no hidden cubic correction is omitted from B0.

## 4. An explicit basis of the eight remaining cubic identities

Let \(E_{ij}\) denote a matrix unit. For a trace-free Hermitian H,
\[
 \operatorname{tr}(HT\operatorname{adj}T)=d\operatorname{tr}H=0.
\]
Define the coefficient matrix K by the bilinear polynomial \(t^TKc\), with T and C temporarily independent Hermitian matrices.

The eight required gauges are:

1. \(\Im\operatorname{tr}(HTC)\) for the five real symmetric trace-free matrices
   \[
   E_{11}-E_{22},\ E_{22}-E_{33},\ E_{12}+E_{21},\ E_{13}+E_{31},\ E_{23}+E_{32};
   \]
2. \(\Re\operatorname{tr}(HTC)\) for the three imaginary Hermitian matrices
   \[
   i(E_{12}-E_{21}),\ i(E_{13}-E_{31}),\ i(E_{23}-E_{32}).
   \]

Each has \(PKP=-K\), hence only R×I and I×R entries. No skew-Hermitian variable is introduced: T, C and H are all Hermitian; the trace of their triple product may be complex before C is set to adj T.

The exact noncubic multiplication maps have (columns, rank, kernel) equal to (45,45,0), (54,45,9), (9,9,0), (1,1,0) in degrees 2,4,5,6. Thus the canonical quartic gauge has exactly nine dimensions, and no additional degree-five/six gauges are omitted. The exact cubic product map has 81 columns and rank 65, giving the known 16-dimensional full kernel. Its cross-parity restriction has **36 columns and rank 28**. The eight displayed matrices are independent and lie in that kernel, hence form the complete cross-parity kernel. All calculations are rational; the verifier checks actual polynomial coefficients rather than sample evaluations.

## 5. The two explicit coupled PSD blocks

Put \(B=B_0+\sum_{j=1}^8k_jK_j\), \(D=D_0-2L(u_R)\). In +/− order, the conditions become
\[
 X_+=\begin{pmatrix}A_{II}&B_{IR}\\B_{IR}^T&D_{RR}\end{pmatrix}\succeq0
 \quad(3+6=9),
\]
\[
 X_-=\begin{pmatrix}
 A_{RR}&B_{RI}&u_R\\
 B_{RI}^T&D_{II}&e_I\\
 u_R^T&e_I^T&g
 \end{pmatrix}\succeq0
 \quad(6+3+1=10).
\]
There are eight k's plus six u entries. **The blocks remain coupled** through those same parameters. Their separate small sizes are not a proof that simultaneous feasibility holds.

The [reflection-average SOS](REFLECTION_AVERAGE_SOS.md) gives a constructive u_R for which the parity-in-degree diagonal pieces are PSD. It does not show that the original B/e couplings fit the two shared-parameter blocks. Universal simultaneous completion remains open.

## 6. Connecting the remaining problem to the actual block-contraction theorem

A second TheoremSearch query returned Moradi–Furuichi–Sababheh, [*Further Properties of Accretive Matrices*, arXiv:2210.08678v1](https://arxiv.org/abs/2210.08678v1), **Lemma 2.3** (p. 11), citing Bhatia's *Positive Definite Matrices*, Proposition 1.3.2:
\[
 \begin{pmatrix}A&Z\\Z^*&B\end{pmatrix}\succeq0
 \iff A,B\succeq0\ \text{and}\ Z=A^{1/2}CB^{1/2},\quad\|C\|\le1.
\]
The original lemma and its surrounding hypotheses were read; that paper cites rather than proves this standard characterization. Its rectangular version follows by zero padding or by the following elementary argument, so no invertibility hypothesis is silently added.

For a PSD block matrix, evaluating on kernel vectors forces Z to vanish on ker B and Z* on ker A. On the two ranges use the inverse square roots, obtaining \(C=A^{\dagger/2}ZB^{\dagger/2}\). Congruence on the ranges gives \(\begin{pmatrix}I&C\\C^*&I\end{pmatrix}\succeq0\), equivalent to \(\|C\|\le1\). Conversely, any such contraction gives a PSD middle block and hence the original block by congruence. This treats singular matrices as well.


This theorem converts the remaining completion into exact **range and contraction** obligations. It supplies neither their hypotheses nor their conclusion for the actual spectral B/e blocks. Nonnegative minor entries, positivity of the even average, and complex bilinear trace identities are not sufficient substitutes. Proving the simultaneous range/contraction conditions for every actual supported spectrum is still open.


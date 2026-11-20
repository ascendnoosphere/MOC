### 1. Invariance holds for arbitrary complex spectral data

The claim in `organized/research/PARITY_REDUCED_COMPLETION.md:9–20` does not require real spectra.

For diagonal spectra, the complementary-minor expansion is
\[
\det(D_a+UD_bU^*)
=\sum_{\substack{I,J\\|I|=|J|}}
\left(\prod_{i\notin I}a_i\right)
\left(\prod_{j\in J}b_j\right)
|\det U[I,J]|^2.
\]
Conjugating **\(U\) alone** preserves every absolute minor square, while leaving the possibly complex spectral coefficients untouched. Consequently
\[
F(\bar U)=F(U)
\]
for arbitrary complex \(a,b,\eta\).

Because the fixed Sinkhorn basis is real,
\[
U(-\bar T)=\overline{U(T)}.
\]
Also \(D(-\bar T)=D(T)\): conjugation preserves the real polynomial \(\det(I+T^2)\). Thus
\[
G(-\bar T)=G(T).
\]

This is fundamentally different from \(T\mapsto-T\), which implements \(U\mapsto U^*\) and generally preserves only the reflection average—not the original gap.

### 2. The sign action and Gram averaging are exact

With \(P\) and the real/imaginary index sets specified in `organized/research/PARITY_REDUCED_COMPLETION.md:22–35`,
\[
t\mapsto-Pt,\qquad c\mapsto Pc,\qquad d\mapsto-d.
\]
Indeed, for order three,
\[
\operatorname{adj}(-\bar T)=\overline{\operatorname{adj}T},
\qquad \det(-\bar T)=-\det T,
\]
where \(\det T\) is real. Hence
\[
q(-\bar T)=Sq(T),\qquad S=\operatorname{diag}(-P,P,-1).
\]

For any real symmetric feasible Gram \(X\),
\[
\widehat X=\frac{X+SXS}{2}\succeq0,\qquad
q^T\widehat Xq=G.
\]
The converse is immediate because the averaged family is a subfamily of the original Grams.

The eigenspaces are exactly
\[
q_+=(t_I,c_R),\quad \dim=3+6=9,
\qquad
q_-=(t_R,c_I,d),\quad \dim=6+3+1=10.
\]
Thus `organized/research/PARITY_REDUCED_COMPLETION.md:37–44` establishes an equivalence, not a relaxation.

### 3. Averaging stays in the same canonical gauge

For the canonical family in `organized/research/PARITY_REDUCED_COMPLETION.md:54–80`, direct congruence gives
\[
S X(K,u)S=X(-PKP,Pu),
\]
provided
\[
PAP=A,\quad PD_0P=D_0,\quad PB_0P=-B_0,\quad Pe=-e,
\quad PL(u)P=L(Pu).
\]

The last identity also has a coordinate-independent derivation. Let \(\mathcal C=\operatorname{herm}(c)\). Then
\[
\begin{aligned}
c^TPL(u)Pc
&=u\cdot\operatorname{coords}\operatorname{adj}(\overline{\mathcal C})\\
&=u\cdot P\,\operatorname{coords}\operatorname{adj}\mathcal C\\
&=(Pu)\cdot\operatorname{coords}\operatorname{adj}\mathcal C.
\end{aligned}
\]
Equality of these quadratic forms implies the stated covariance.

Therefore averaging sends
\[
K\longmapsto\frac{K-PKP}{2},\qquad
u\longmapsto\frac{u+Pu}{2},
\]
with the same fixed \(A,B_0,D_0,e,g\). In particular, **the three imaginary-coordinate entries of \(u\) vanish**; no redefinition of the baseline quartic block is needed.

The exact all-direction checks implementing this are in `organized/research/verify_parity_reduced_completion.py:31–38`.

### 4. Raw \(0d\) absorption does not hide a cubic correction

This potential failure mode is correctly excluded.

In the raw 20-coordinate representation, a constant/determinant entry would contribute \(2M_{0d}d\), hence could alter \(B_0\) after using a determinant identity. But the raw involution is
\[
S_{20}=\operatorname{diag}(1,-P,P,-1).
\]
Its invariance forces \(M_{0d}=-M_{0d}\), hence \(M_{0d}=0\).

The verifier checks this explicitly before defining \(B_0=M_{tc}\), in `organized/research/verify_parity_reduced_completion.py:33–36`. I additionally checked that **all raw constant/linear entries vanish**, as well as \(M_{00}\) and \(M_{0d}\), in every one of the 70 identity-contact directions.

The remaining absorptions have the correct factors:
\[
A=M_{tt}+2\sum_jM_{0,c_j}L_j,\qquad
D_0=M_{cc}+2\sum_jM_{t_j,d}L_j.
\]
They affect degrees two and four, respectively—not degree three.

### 5. Kernel dimensions and the eight trace gauges are correct

The rerun confirmed the exact coefficient-map assertions in `organized/research/verify_parity_reduced_completion.py:40–50`:

| Multiplication map | Columns | Rank | Kernel |
|---|---:|---:|---:|
| All \(t_i c_j\) | 81 | 65 | 16 |
| Cross-parity \(t_i c_j\) | 36 | 28 | 8 |

These are polynomial-coefficient calculations over exact arithmetic, not sampled evaluations.

For every trace-free Hermitian \(H\),
\[
\operatorname{tr}(HT\operatorname{adj}T)=d\,\operatorname{tr}H=0.
\]
Taking real and imaginary parts gives genuine real bilinear identities.

Under simultaneous conjugation of the independent Hermitian matrices \(T,\mathcal C\):

* for real symmetric \(H\), \(\Im\operatorname{tr}(HT\mathcal C)\) changes sign;
* for imaginary Hermitian \(H\), \(\Re\operatorname{tr}(HT\mathcal C)\) changes sign.

Thus the selected five-plus-three gauges have \(PKP=-K\). The exact verification establishes that their coefficient vectors have rank eight and lie in the cross-parity kernel. Since that kernel has dimension eight, they form its complete basis.

The matrices in `organized/research/parity_reduced_completion_verification.json` agree with this construction. Their off-diagonal factors follow the unnormalized coordinate convention in `organized/research/rational_sinkhorn_certificates.py:105–106`.

As an additional check on the underlying 25-parameter completeness claim, I independently recomputed:
\[
\begin{array}{c|ccc}
\text{degree}&\text{columns}&\text{rank}&\text{kernel}\\ \hline
2&45&45&0\\
4&54&45&9\\
5&9&9&0\\
6&1&1&0
\end{array}
\]
Together with the cubic calculation, these justify exactly the \(16+9\) gauge freedom described in `universal_sos_mechanism_lemmas.md`.

### 6. The two PSD blocks are correctly assembled

With \(B=B_0+K\), \(D=D_0-2L(u_R)\), the invariant Gram is
\[
X_+=
\begin{pmatrix}
A_{II}&B_{IR}\\
B_{IR}^T&D_{RR}
\end{pmatrix},
\]
and
\[
X_-=
\begin{pmatrix}
A_{RR}&B_{RI}&u_R\\
B_{RI}^T&D_{II}&e_I\\
u_R^T&e_I^T&g
\end{pmatrix}.
\]
These match `organized/research/PARITY_REDUCED_COMPLETION.md:105–120`.

There are eight cubic coefficients and six real-coordinate \(u\) coefficients. **Fourteen is the dimension of this structural affine parametrization, not necessarily the dimension of a feasible face for every spectrum.** Degeneracies can force additional constraints.

The blocks remain coupled through their shared parameters. Positivity of the reflection-even polynomial does not supply the missing \(B/e\) domination.

### 7. External theorem connection: applicable, with an important source caveat

**Theorem A.8 genuinely concerns general finite-dimensional invariant \(V\)** in \(\mathbb R[x]/I\), not only hypercubes. This is explicit in `organized/research/external/parity_and_contraction/1606.05639v2.txt:1605–1618,1673–1683`; the hypercube specialization begins only at `organized/research/external/parity_and_contraction/1606.05639v2.txt:1724`.

Here its hypotheses specialize correctly to:

* a linear order-two action on the nine real variables;
* zero ideal;
* invariant \(V=\operatorname{span}(t,c,d)\);
* invariant \(G\);
* the **conditional assumption** that \(G\) is \(V\)-SOS.

**Source caveat requiring explicit qualification:** the appendix’s unrestricted real-representation preliminaries overstate uniqueness of invariant bilinear forms. `organized/research/external/parity_and_contraction/1606.05639v2.txt:1559–1564` claims every invariant bilinear form on an irreducible real module is a scalar multiple of one symmetric form; `organized/research/external/parity_and_contraction/1606.05639v2.txt:1590–1594` consequently claims a one-dimensional invariant tensor space. These statements fail for general complex-type real irreducibles—for example, the real plane carrying a \(120^\circ\) rotation has both invariant Euclidean and alternating forms.

This **does not invalidate this application**: both irreducibles of \(\mathbb Z/2\) are one-dimensional real characters. The project already flags the complex/quaternionic caveat in `organized/research/PARITY_REDUCED_COMPLETION.md:48–51`; I recommend explicitly noting this source-level overstatement rather than suggesting that its unrestricted real-representation proof is universally sound. The elementary averaging proof independently settles the present case.

### 8. Contraction theorem, singular cases, and verifier improvements

Lemma 2.3 states the claimed PSD factorization, with **semidefinite**, not merely positive-definite, diagonal blocks: `organized/research/external/parity_and_contraction/2210.08678v1.txt:571–574`.

The rectangular/singular extension in `organized/research/PARITY_REDUCED_COMPLETION.md:124–137` is correct. Positivity forces
\[
Z\ker B=0,\qquad Z^*\ker A=0.
\]
On the ranges,
\[
C=A^{\dagger/2}ZB^{\dagger/2}
\]
is a contraction; extending it by zero gives \(Z=A^{1/2}CB^{1/2}\). Conversely, contraction implies PSD by congruence of the identity-diagonal middle block.

The entire parity reduction uses polynomial identities and finite averaging, with no inversion of \(T\), spectral sums, \(A\), or \(g\). It therefore applies directly to singular \(T\), repeated spectra, tied contacts, and singular Gram blocks—not merely by a generic-limit argument.

Two optional verifier improvements, not mathematical defects:

* Explicitly require `len(cf)==70`; currently the count is reported rather than asserted (`organized/research/verify_parity_reduced_completion.py:26,53`).
* Add explicit assertions for the raw constant/linear vanishings and the noncubic ranks above, making the canonical-family prerequisites locally auditable (`organized/research/verify_parity_reduced_completion.py:34–49`).


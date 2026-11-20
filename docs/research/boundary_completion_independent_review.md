## 1. Conventions and actual spectral linkage

The conventions are consistent:

- Hermitian coordinates use upper off-diagonal entries \(x+iy\).
- Cofactor coordinates have the same ordering.
- The Cayley transform is \(V=(I+iT)(I-iT)^{-1}\).
- The quintic convention is \(G_5=2d\,e^Tc\), not \(d\,e^Tc\).

See `organized/research/rational_sinkhorn_certificates.py:105–106,117–135` and `universal_sos_mechanism_lemmas.md`.

The compound construction correctly uses
\[
\delta_-=1-\operatorname{tr}C+i(d-\operatorname{tr}T),\qquad
N_+=(1+\operatorname{tr}C-id)I-2C+i(2T-\operatorname{tr}T\,I).
\]
The signed complement matrix \(J\), the conjugation in \(N_2=J\overline{N_+}J\), and the five exterior-power blocks agree with the ordered wedge bases. These are substantive sign conventions, not cosmetic choices. See `organized/research/SINKHORN_SOS_CERTIFICATE_ROUTE.md:93–134`.

For actual spectra, the real coefficient attached to a compound term is
\[
w_{I,J}=\Re\!\left(\eta
 \prod_{i\notin I}a_i\prod_{j\in J}b_j\right).
\]
Thus
\[
\Re(\eta F(W))=\sum_{I,J}w_{I,J}|\det W[I,J]|^2.
\]
At a permutation, the squared minor is the set-assignment indicator used by the verifier. Whether a permutation matrix is described by row-to-column or column-to-row convention only inverts its name; the displayed products and verifier use a consistent row-to-column labeling.

**Crucially, the height remains the maximum of the original 24 products.** There is no replacement height or loss in the support inequality.

## 2. Gap identities and vanishing contacts

With identity supporting,
\[
\Delta_\pi=\Re\bigl(\eta(z_{\rm id}-z_\pi)\bigr)\ge0.
\]
The rank-\(\le2\) matrix \((a_i+b_j)\) has vanishing three-by-three determinants. Multiplying the resulting alternating identity by the remaining fixed factor gives
\[
\Delta_{(ijk)}+\Delta_{(ikj)}
=\Delta_{(ij)}+\Delta_{(ik)}+\Delta_{(jk)}.
\]
No division or nondegeneracy assumption is involved.

Summing over the four triples counts each transposition twice. Together with the reflection-average identity, this gives exactly
\[
g=\frac18\sum_{\text{eight 3-cycles}}\Delta_\sigma
 =\frac14\sum_{\text{six transpositions}}\Delta_\tau.
\]
The verifier also checks both identities coefficientwise on all 70 formal compound coefficients, a stronger algebraic check than substitution of actual spectra: `organized/research/verify_boundary_completion.py:24–27`.

Therefore \(g=0\), **using nonnegativity**, forces all six transposition gaps and all eight three-cycle gaps to vanish. The conclusion concerns these **14 gaps**, not all 24 gaps. Double-transposition and four-cycle gaps may remain positive.

The signed formula
\[
\widehat e=\frac14\sum_\sigma\Delta_\sigma s_\sigma
\]
is correct in the stated conventions. In lexicographic permutation order, the eight three-cycles are precisely the order used in the manuscript’s sign table. The checked Gram entries are \(Q_{10+j,19}\), which correctly represent \(e_j\) because symmetric Gram multiplication supplies the factor two. All other coordinates vanish: `organized/research/verify_boundary_completion.py:28–33`.

Consequently \(g=0\Rightarrow e=0\), and the stated estimates
\[
|e_{\Im C_{ij}}|\le2g,\qquad \|e\|_2\le2\sqrt3\,g
\]
also follow. There is no surviving quintic obstruction on this branch.

## 3. Four-cycle weights and the six-square identity

Set
\[
d_1=\Delta_{(12)(34)},\quad d_2=\Delta_{(13)(24)},\quad
d_3=\Delta_{(14)(23)}.
\]
On the 14-contact face,
\[
\alpha=\frac{d_1+d_2-d_3}{2},\quad
\beta=\frac{d_1+d_3-d_2}{2},\quad
\gamma=\frac{d_2+d_3-d_1}{2}
\]
are respectively the actual gaps of
\[
\begin{array}{c|c}
\alpha &(1243),(1342)\\
\beta &(1234),(1432)\\
\gamma &(1324),(1423).
\end{array}
\]
All six identifications passed exact row-space reduction: `organized/research/verify_boundary_completion.py:39–43`.

This is the necessary positivity bridge: the weights are nonnegative **because they equal original support gaps**, not because arbitrary nonnegative \(d_1,d_2,d_3\) automatically satisfy triangle inequalities. The inequalities are consequences of the additional contacts and four-cycle support constraints.

The verified polynomial identity is exactly
\[
\begin{aligned}
G(T)={}&\alpha\bigl[(C_{11}-C_{22})^2+4(\Im C_{12})^2\bigr]\\
&+\beta\bigl[(C_{22}-C_{33})^2+4(\Im C_{23})^2\bigr]\\
&+\gamma\bigl[(C_{11}-C_{33})^2+4(\Im C_{13})^2\bigr].
\end{aligned}
\]
See `universal_sos_boundary_completion_lemmas.md`.

### Why the 838-row verification proves the universal identity

Let \(R\) be the \(14\times70\) contact matrix, and let \(B\) be its nonzero reduced-row-echelon rows, with pivot columns \(P\). Then \(B[:,P]=I\). For a coefficient row \(r\), the verifier checks
\[
r-r[:,P]B=0.
\]
This is precisely membership in \(\operatorname{rowspan}R\), hence \(rw=0\) whenever \(Rw=0\).

The implementation builds every coefficient of the residual after substituting actual cofactor and determinant polynomials, and checks all **838** rows—not just selected monomials or sample matrices: `organized/research/verify_boundary_completion.py:34–56`.

Thus the computation is an exact finite proof of an identity on the entire contact subspace. Its independence is specifically **row-space verification versus the author’s nullspace calculation**; it still shares the audited `exact_geometry()` model and SymPy arithmetic. It is not a separate proof-assistant formalization.

## 4. Gram gauge and rank

The inference \(K=-B_0\) is sound **in the declared canonical gauge**.

The six-square identity shows \(G_3=0\). Therefore
\[
t^TB_0c=0,
\]
so \(-B_0\) belongs to the allowed cubic multiplication kernel. My rank computation confirms its dimension \(81-65=16\).

Likewise, the quartic matrix in the formula is the canonical \(D_0\), defined by \(G_4=c^TD_0c\). Uniqueness follows from the rank-45 cofactor-quadratic multiplication map. One must not silently identify this \(D_0\) with an arbitrary raw \(c,c\) block before absorbing any \(td\) contribution. The manuscript’s definition makes the inference valid: `universal_sos_mechanism_lemmas.md`.

With \(A=0\), \(e=g=0\), take \(u=0\), \(K=-B_0\). The remaining block is a nonnegative weighted three-vertex Laplacian plus three nonnegative imaginary-coordinate diagonal entries. Its rank is at most \(2+3=5\). Hence the displayed block-diagonal completion is genuinely PSD: `universal_sos_boundary_completion_lemmas.md`.

“Nonnegative coefficients” is the accurate wording: strict positivity is neither required nor guaranteed.


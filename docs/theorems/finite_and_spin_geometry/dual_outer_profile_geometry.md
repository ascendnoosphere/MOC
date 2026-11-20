## 1. Twenty anchored coordinates and their thirteen-dimensional affine space

Number rows as \(r,v,s,t\), with \(v\) the second, anchor row. For \(i<j\), use

\[
R_i=|r_i|^2,\quad S_i=|s_i|^2,\qquad
P_{ij}=|r_iv_j-r_jv_i|^2,\quad
Q_{ij}=|s_iv_j-s_jv_i|^2.
\tag{1}
\]

The coordinate order throughout is \(R_4,P_6,S_4,Q_6\), with pairs
\(12,13,14,23,24,34\). A permutation \(\pi=(i,j,k,l)\) has profile

\[
V_\pi=(e_i,e_{\{i,j\}},e_k,e_{\{k,j\}}).
\tag{2}
\]

The twenty coordinates satisfy

\[
\sum_iR_i=\sum_iS_i=\sum_{i<j}P_{ij}=\sum_{i<j}Q_{ij}=1,
\tag{3}
\]

\[
\sum_{j\ne i}(P_{ij}-Q_{ij})=R_i-S_i,\qquad i=1,\ldots,4.
\tag{4}
\]

There are seven independent affine equations: one of the four equations (4) is redundant after (3). The 24 permutation profiles have affine dimension thirteen, as verified by rational elimination in the companion exact script. Hence these equations describe their full affine hull.

For a generic real cost \(c=(u^R,q^R,u^S,q^S)\in\mathbb R^{20}\), write

\[
c\cdot x=\sum_i u^R_iR_i+\sum_{i<j}q^R_{ij}P_{ij}
+\sum_i u^S_iS_i+\sum_{i<j}q^S_{ij}Q_{ij}.
\tag{5}
\]

At a real unit anchor \(v\), this is \(r^*M(v)r+s^*L(v)s\). For example, the first form is

\[
r^*M(v)r=\sum_i u^R_i|r_i|^2
+\sum_{i<j}q^R_{ij}|r_iv_j-r_jv_i|^2,\qquad r\perp v.
\tag{6}
\]

The 54-variable certificate applies to arbitrary real \(u,q\) in (6), not just to spectral product data.

## 2. Definition of the normalized moment lift

Let \(\mathcal L\) consist of the following real variables.

First, let

\[
W\succeq0,\qquad W\ge0\ \text{entrywise},\qquad
\mathbf1^TW\mathbf1=1,\qquad m=W\mathbf1.
\tag{7}
\]

For each \(\alpha\in\{R,S,T\}\), let \(A_\alpha\) be a symmetric matrix and \(Z_\alpha=(z_{\alpha,ij})\) a real matrix satisfying

\[
A_\alpha\succeq0,\quad A_\alpha\mathbf1=0,\quad
\operatorname{diag}Z_\alpha=\operatorname{diag}A_\alpha,\quad
Z_\alpha^T\mathbf1=m.
\tag{8}
\]

Impose the two coupling equations

\[
\sum_\alpha A_\alpha=\operatorname{diag}m-W,
\qquad
\sum_\alpha Z_\alpha=\mathbf1m^T-W,
\tag{9}
\]

and, for every \(\alpha\) and pair \(i<j\),

\[
\begin{pmatrix}
z_{\alpha,ij}&A_{\alpha,ij}\\
A_{\alpha,ij}&z_{\alpha,ji}
\end{pmatrix}\succeq0.
\tag{10}
\]

Its profile projection \(\Pi:\mathcal L\to\mathbb R^{20}\) is

\[
R_i=\sum_jz_{R,ij},\qquad
P_{ij}=z_{R,ij}+z_{R,ji}-2A_{R,ij},
\tag{11}
\]

with the same formula using \(S\) for \(S_i,Q_{ij}\). Set

\[
\mathcal K=\Pi(\mathcal L).
\tag{12}
\]

Every \(Z_\alpha\) is entrywise nonnegative: this follows on its diagonal from (8) and elsewhere from the diagonal entries of (10).

## 3. Affine dimension, a strict interior point, and compactness

The affine constraints admit a direct parametrization with 37 free variables.

Choose nine independent entries of \(W\), recovering its final diagonal entry from (7). Put

\[
E=\begin{pmatrix}1&0&0\\0&1&0\\0&0&1\\-1&-1&-1\end{pmatrix}.
\]

Choose \(A_R=E B_R E^T\) and \(A_S=E B_S E^T\), where each symmetric \(B\) has six free entries. The matrix \(A_T\) is then determined by (9). For each of \(Z_R,Z_S\), its diagonal is prescribed; choose two of the three off-diagonal entries in each column and recover the third from its column sum. This gives eight variables for each \(Z\). The matrix \(Z_T\) is determined by (9).

Thus \(9+12+16=37\). A relative strict interior point is

\[
W=\frac{J+2I}{24},\qquad m=\frac14\mathbf1,
\tag{13}
\]

\[
A_R=A_S=A_T=\frac{4I-J}{72},
\tag{14}
\]

\[
z_{\alpha,ii}=\frac1{24},\qquad
z_{\alpha,ij}=\frac5{72}\quad(i\ne j).
\tag{15}
\]

Here \(W\) is positive definite and entrywise positive, every \(A_\alpha\) is positive definite on \(\mathbf1^\perp\), and all pair blocks are positive definite. Consequently the affine dimension is exactly 37.

The lift is compact. Indeed, the nonnegative entries of \(W\) sum to one. Hence \(0\le m_j\le1\). Every column of \(Z_\alpha\) is nonnegative and has sum \(m_j\), so all its entries lie in \([0,1]\). The entries of \(A_\alpha\) are bounded by its PSD diagonal estimates, or directly by (10). The defining conditions are closed. This proves compactness without quotienting out any variable kernel.

Equations (3)–(4) follow directly from (8) and (11). For instance,

\[
\sum_{j\ne i}P_{ij}=R_i+m_i
\tag{16}
\]

because \(A_R\mathbf1=0\). Since \(\mathcal K\) contains all permutation profiles, its affine dimension is exactly thirteen.

## 4. Exact correspondence with every normalized dual annihilator

The primal certificate has the following blocks, in the order used by code/theorems/finite_and_spin_geometry/dual_full_quadratic_exact_certificate.py:

1. a \(3\times3\) correction matrix \(R_0\);
2. six \(2\times2\) correction-pair matrices;
3. six first-slack pair matrices and a \(3\times3\) first-slack restriction;
4. six second-slack pair matrices and a \(3\times3\) second-slack restriction;
5. a \(4\times4\) budget matrix \(T\);
6. ten scalar nonnegative entries of \(B-T\).

For \(L\in\mathcal L\), assign their dual weights as follows:

| Primal block | Dual weight |
|---|---|
| \(R_0\) | \(E^TA_TE\) |
| Correction pair \(ij\) | the pair block (10) for \(T\) |
| First-slack pair \(ij\) | the pair block (10) for \(R\) |
| First-slack diagonal restriction | \(A_R[123,123]\) |
| Second-slack pair \(ij\) | the pair block (10) for \(S\) |
| Second-slack diagonal restriction | \(A_S[123,123]\) |
| Budget \(T\) | \(W\) |
| Entry \((B-T)_{ii}\) | \(W_{ii}\) |
| Entry \((B-T)_{ij}\), \(i<j\) | \(2W_{ij}\) |

All these weights are PSD or nonnegative. The differing congruences in the first and diagonal-slack rows of the table are intentional. If \(A\mathbf1=0\), then
\(A=E A[123,123]E^T\).

Here is the full annihilation calculation. The notation for primal variables is that of dual_quadratic_cp_cone.md.

- The \(c_j\) and \(d_j\) coefficients vanish exactly when the corresponding \(Z_R,Z_S\) column sums equal \(m_j\).
- The \(t^R_{ij},t^S_{ij}\) coefficients equate the off-diagonal entries of the slack-pair weights with \(A_{R,ij},A_{S,ij}\).
- The \(x_{ij}\) coefficients give
  \(\sum_\alpha z_{\alpha,ij}=m_j-W_{ij}\), for \(i\ne j\).
- The \(\tau_{ij}\) coefficients give
  \(\sum_\alpha A_{\alpha,ij}=-W_{ij}\), for \(i\ne j\).
- The \(R_0\) coefficients give
  \(E^TA_TE=E^T(\operatorname{diag}m-W-A_R-A_S)E\).
- The budget-matrix coefficients equate its PSD dual weight to the symmetric entry-weight matrix \(W\).

For clarity, the budget pairing used in these statements is

\[
\langle B,W\rangle
=\sum_jg_jm_j+\sum_{i<j}(w_{ij}-\delta_{ij})W_{ij},
\]

where \(g,w,\delta\) are the primal quantities in equations (20)–(23) of the preceding note.

The diagonal and remaining column identities in (8)–(9) now follow automatically. Conversely, beginning with arbitrary PSD dual blocks annihilating all 54 primal directions, the same equations recover (7)–(10). There is no additional hidden constraint.

If the dual block tuple is nonzero, its height coefficient \(\mathbf1^TW\mathbf1\) is strictly positive. If it were zero, entrywise nonnegativity would force \(W=0\), then \(m=0\). The nonnegative column sums force \(Z_R=Z_S=0\) and the diagonal entries of \(A_R,A_S\) to vanish, hence those PSD matrices vanish. The remaining annihilation equations force all correction blocks to vanish as well. Thus the entire tuple would be zero. Every nonzero dual annihilator therefore normalizes uniquely to \(\mathcal L\).

Finally, for arbitrary \(c\in\mathbb R^{20}\) and height \(h\), pairing the constant primal blocks with this dual tuple gives exactly

\[
\boxed{\langle C(c,h),\mathrm{dual}(L)\rangle
=h-c\cdot\Pi(L).}
\tag{17}
\]

The exact rational verifier checks this identity on all twenty cost-coordinate basis vectors and on the height coordinate, as well as all 54 variable directions.

## 5. Exact support-function theorem

For every real cost \(c\),

\[
\boxed{
\min\{h:\text{the full 54-variable certificate is feasible for }(c,h)\}
=\max_{L\in\mathcal L}c\cdot\Pi(L).
}
\tag{18}
\]

Both extrema are attained. Indeed, a sufficiently large scalar multiplier in each slack and a sufficiently large height give a feasible primal. The normalized dual has the relative Slater point (13)–(15) and is compact. Standard finite-dimensional semidefinite duality gives equality and primal attainment. Equivalently, the exact dual-annihilator description in Section 4, together with Slater, rules out an unsupported infeasibility gap at the optimal height.

In particular, at the permutation height
\(h(c)=\max_\pi c\cdot V_\pi\),

\[
\text{full54 feasibility}
\quad\Longleftrightarrow\quad
c\cdot x\le h(c)\quad\text{for every }x\in\mathcal K.
\tag{19}
\]

This theorem is an exact characterization of the certificate class. It does not assert (19) for all costs.

The prior strict dual pairing
\(72(h-\operatorname{mean}_\pi c\cdot V_\pi)\)
provides an alternative explicit bound on all feasible primal blocks. Together with injectivity of the primal affine block map, it proves compactness of the full 54-parameter feasible set at a fixed height. This does not force the right side of (19) to hold.

## 6. Actual complex-unitary profiles embed in the lift

Make the anchor \(v\) real by column phases and put \(p_i=v_i^2\). For each of the three other, possibly complex rows \(r_\alpha\), define

\[
W=pp^T,\qquad m=p,
\]

\[
A_\alpha=D_v\,\operatorname{Re}(r_\alpha r_\alpha^*)\,D_v,\qquad
z_{\alpha,ij}=|r_{\alpha,i}|^2p_j.
\tag{20}
\]

Orthonormality gives \(A_\alpha\mathbf1=0\), the column sums in (8), and both sums in (9). Each pair block (10) is PSD because

\[
|A_{\alpha,ij}|^2
=v_i^2v_j^2\bigl(\operatorname{Re}(r_{\alpha,i}\overline{r_{\alpha,j}})\bigr)^2
\le p_ip_j|r_{\alpha,i}|^2|r_{\alpha,j}|^2.
\]

The projection (11) is the original singleton and wedge profile. Consequently

\[
\operatorname{conv}\{\text{actual complex }U(4)\text{ profiles}\}
\subseteq\mathcal K.
\tag{21}
\]

## 7. Boolean reconstruction and the location of the relaxation

The anchor row is \(m\), while the fourth singleton row is

\[
T_i=1-m_i-R_i-S_i.
\tag{22}
\]

The third anchor wedge is

\[
P^T_{ij}=m_i+m_j-P_{ij}-Q_{ij}.
\tag{23}
\]

These coordinates are nonnegative because they are respectively row sums of \(Z_T\) and evaluations of its pair blocks on \((1,-1)\).

Reconstruct level-two rows as

\[
12=P,\quad 23=Q,\quad 24=P^T,
\]

\[
34=P_{\rm complement},\quad
14=Q_{\rm complement},\quad
13=P^T_{\rm complement}.
\tag{24}
\]

Level three is determined by complementary singleton entries. Equations (16), (22)–(24) give the row and column stochasticity and all Boolean incidence intertwining relations. Thus \(\mathcal K\) lies inside the previously studied Boolean profile relaxation.

The marginal \(W\) itself is not an exotic obstruction. In order four, a PSD entrywise nonnegative matrix is completely positive, by duality from the order-four copositive decomposition theorem. Hence \(W=\sum_\nu x_\nu x_\nu^T\) with \(x_\nu\ge0\). Normalize
\(p_\nu=x_\nu/(\mathbf1^Tx_\nu)\) and
\(\theta_\nu=(\mathbf1^Tx_\nu)^2\), omitting zero vectors. Then

\[
W=\sum_\nu\theta_\nu p_\nu p_\nu^T,\qquad
\sum_\nu\theta_\nu=1,\qquad
m=\sum_\nu\theta_\nu p_\nu.
\]

Thus every \(W\) has genuine probability-simplex moments. The difficulty is coupling that disintegration to \(A_\alpha,Z_\alpha\).

## 8. The diagonal moment face is exactly classical

If \(W=\operatorname{diag}m\), equation (9) gives \(\sum_\alpha A_\alpha=0\). All three PSD matrices therefore vanish. The matrices \(Z_\alpha\) have zero diagonal.

Fix an anchor value \(j\) with \(m_j>0\). Form the \(3\times3\) matrix with rows indexed by \(\alpha=R,S,T\), columns \(i\ne j\), and entries

\[
\frac{z_{\alpha,ij}}{m_j}.
\]

It is doubly stochastic: its row sums follow from (8), and its column sums from (9). A Birkhoff decomposition supplies a conditional permutation of the three remaining rows to the three nonanchor columns. Mixing these laws with anchor probability \(m_j\) gives one common permutation law for the entire profile.

Conversely, a permutation has a diagonal \(W\) lift, and convex mixtures preserve that property. Therefore

\[
\Pi\{L\in\mathcal L:W\text{ diagonal}\}
=\operatorname{conv}\{V_\pi\}.
\tag{25}
\]

## 9. A signed assignment interpretation and a sufficient uncrossing criterion

Define

\[
C_\alpha=Z_\alpha-A_\alpha.
\tag{26}
\]

Then

\[
\operatorname{diag}C_\alpha=0,\qquad
C_\alpha^T\mathbf1=m,\qquad
C_\alpha\mathbf1=R^\alpha,
\]

\[
C_{\alpha,ij}+C_{\alpha,ji}=P^\alpha_{ij},\qquad
\sum_\alpha C_\alpha=\mathbf1m^T-\operatorname{diag}m.
\tag{27}
\]

Thus these are oriented assignment weights, with nonnegative unoriented wedge totals.

If every \(C_\alpha\) is entrywise nonnegative, replace

\[
W\mapsto\operatorname{diag}m,\qquad
A_\alpha\mapsto0,\qquad
Z_\alpha\mapsto C_\alpha.
\]

Equations (27) show that the new tuple is a lift with exactly the same profile. Section 8 therefore gives a common permutation law.

A profile outside the classical polytope consequently requires a negative oriented entry in every one of its lifts. Such an entry can only occur where \(A_{\alpha,ij}>0\), since \(Z_\alpha\ge0\). Both orientations cannot be negative, because their sum is the nonnegative wedge coordinate.

A negative entry in one chosen lift is not, by itself, a proof that its projected profile is nonclassical: a different lift might admit nonnegative oriented weights.

## 10. Exact conditional realizability on a rank-one \(W\) fiber

The independent review supplied the following useful sharp criterion.

Suppose \(W=pp^T\), with \(p\) a probability vector, and write
\(R^\alpha=Z_\alpha\mathbf1\). A point of this lift fiber is a convex mixture of actual frame moments if and only if

\[
\boxed{Z_\alpha=R^\alpha p^T\quad\text{for every }\alpha.}
\tag{28}
\]

Necessity follows because a mixture with
\(\mathbb E(p_{\rm anchor}p_{\rm anchor}^T)=pp^T\)
has zero anchor variance, hence \(p_{\rm anchor}=p\) almost surely.

Here the criterion concerns a point of the full normalized moment lift \(\mathcal L\) defined by (7)–(10), with \(\alpha\in\{R,S,T\}\); the rank-one condition on \(W\) alone is not the hypothesis.

For sufficiency, use the [complete rank-one-anchor proof in `review_fourth_batch_proofs.md`, Section 11](review_fourth_batch_proofs.md#11-a-new-exact-rank-one-anchor-fiber-criterion). It constructs the positive effects on \(v^\perp\), where \(v_i=\sqrt{p_i}\), treats coordinates with \(p_i=0\) explicitly, and applies the real three-dimensional orthogonal-frame mixture argument proved in that document's Section 9. Consequently the criterion above includes zero anchor coordinates and reproduces the entire prescribed \(A,Z,W\) tuple, not merely its profile projection.
## 11. Exact nonanchor-row symmetry and assignment endpoints

The moment constraints are invariant under all column permutations and under permutations of \(R,S,T\). The full certificate class therefore has these symmetries.

There is also a constructive primal proof of nonanchor-row covariance. Let its three slacks be

\[
A=Y+\alpha I-M,\quad B=Y+\gamma I-L,\quad C=Y.
\]

Swap the first and third nonanchor rows. The transformed objective can be written with

\[
M'=(\operatorname{tr}_H M)I-M,\qquad L'=L-M.
\]

Choose

\[
Y'=A,\qquad
\alpha'=\operatorname{tr}_H M-\alpha,\qquad
\gamma'=\gamma-\alpha.
\]

The new two slacks are \(Y\) and \(B\). The old first slack is a bilinear SOS modulo orthogonality, so \(Y'\) is itself an allowed quadratic CP correction after projection. Since \(\dim H=3\),

\[
\operatorname{tr}Y'+\alpha'+\gamma'
=\operatorname{tr}Y+\alpha+\gamma.
\]

The trace of a generic pencil (6) is quadratic in the anchor, so the new scalar multipliers remain within the class. Swapping \(R,S\) is immediate.

An exchange of the anchor with another row has not been proved to preserve this moment or certificate class. Its required fourth moments are not supplied by the existing lift. No full shared-Möbius covariance follows from this partial symmetry.

At an anchor vertex \(v=e_j\), the primal certificate reduces to

\[
x_{ij}\ge0,\qquad
c_j+x_{ij}\ge u^R_i+q^R_{ij},\qquad
d_j+x_{ij}\ge u^S_i+q^S_{ij},
\]

\[
c_j+d_j+\sum_{i\ne j}x_{ij}\le h.
\tag{29}
\]

These are exactly the dual inequalities for assigning the three nonanchor rows to the three remaining columns, with row costs
\(u^R_i+q^R_{ij},u^S_i+q^S_{ij},0\).
The full54 problem can therefore be understood as gluing four exact classical assignment duals through the cross-anchor PSD and trace-budget conditions. Solving the endpoints separately does not supply that gluing.

## 12. The actual spectral cost variety

For the CH support problem, the special cost is

\[
u^R_i=\operatorname{Re}(\lambda_1\beta_i),\qquad
q^R_{ij}=\operatorname{Re}(\lambda_1\beta_i\beta_j),
\]

\[
u^S_i=\operatorname{Re}\left(\lambda_0\prod_{k\ne i}\beta_k\right),\qquad
q^S_{ij}=\operatorname{Re}\left(\lambda_0\prod_{k\notin\{i,j\}}\beta_k\right).
\tag{30}
\]

These formulas are polynomial, including at zero spectral entries. At a permutation \((i,j,k,l)\),

\[
c(\beta,\lambda)\cdot V_\pi
=\operatorname{Re}\left((1+\beta_j)\beta_i
(\lambda_1+\lambda_0\beta_l)\right).
\tag{31}
\]

Modulo additive constants and affine profile identities, arbitrary costs have thirteen coordinates. The actual centered cost image has dimension exactly twelve. A \(13\times12\) integer Jacobian has rank twelve, and the map has twelve real input parameters.

Furthermore, no nonzero polynomial of total degree at most three vanishes on the entire actual centered cost image. The exact verifier evaluates homogeneous linear, quadratic, and cubic monomials at 560 Gaussian-integer spectral samples. Their evaluation matrices have respective full ranks

\[
13,\qquad91,\qquad455
\]

modulo the prime \(1000000007\). Full rank modulo a prime proves full rank over the rationals and reals. Since real scaling of \(\lambda\) makes the cost image a cone, a polynomial relation separates into homogeneous relations. Thus inhomogeneous relations of those total degrees are also excluded.

This is a finite exact nonvanishing certificate, not a probabilistic conclusion drawn from fitting. It excludes a low-degree polynomial equality characterization. It does not exclude useful quadratic inequalities, reciprocal identities with auxiliary variables, or parameter-dependent SOS constructions.

All evaluation pivots are checked by dual_spectral_cost_degree_exact.py.

## 13. A compact homogeneous chart for actual costs

Write \(\beta_j=B_j/A_j\), with

\[
A_j=\cos\theta_j\ge0,\qquad
B_j=e^{i\phi_j}\sin\theta_j,\qquad0\le\theta_j\le\pi/2.
\]

Multiplying an affine-chart cost by the common nonnegative factor
\(\prod_jA_j\) gives homogeneous coefficients

\[
u^R_i=\operatorname{Re}\left(\lambda_1B_i\prod_{k\ne i}A_k\right),\qquad
q^R_{ij}=\operatorname{Re}\left(\lambda_1B_iB_j\prod_{k\notin\{i,j\}}A_k\right),
\]

\[
u^S_i=\operatorname{Re}\left(\lambda_0A_i\prod_{k\ne i}B_k\right),\qquad
q^S_{ij}=\operatorname{Re}\left(\lambda_0A_iA_j\prod_{k\notin\{i,j\}}B_k\right).
\tag{32}
\]

The permutation expression is especially simple:

\[
F_\pi=B_i(A_j+B_j)A_k(\lambda_1A_l+\lambda_0B_l).
\tag{33}
\]

Normalize \(|\lambda_0|^2+|\lambda_1|^2=1\). This gives eleven compact angular parameters after overall positive scaling. The formulas extend continuously to poles \(A_j=0\). They do not assume that the first and second spectra can be normalized independently by a shared Möbius action.


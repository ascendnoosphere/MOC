## Round 021 — Zero-diagonal U4 with a row or column of degree one

**Claim proved.** A zero-diagonal unitary U4 having a row or column with exactly one nonzero entry is, after independent row and column permutations, a direct sum of two scalar unitary blocks and one U2 block.

The isolated entry has modulus one and isolates both its row and column. Its position is (i,j) with i different from j. Remove that row and column. The two original diagonal zeros at the remaining indices outside {i,j} survive in the U3 block in distinct rows and columns. Relabel this block so that W11=W22=0. Orthogonality of its first two rows gives W13 conjugate(W23)=0. At least one of these two entries vanishes, so one of those two rows now has just one nonzero entry. Remove this second scalar block. What remains is U2.

Every U2 has its simultaneous minor law on its two permutations with probabilities |u11|² and |u12|². Taking products of the scalar and U2 laws proves the common-minor property here. This argument covers column-degree one by transposition. It does not require a limiting argument through matrices with more nonzero entries.

## Round 022 — Zero-diagonal U4 with a row of degree two

**Claim proved.** Suppose every row and column has at least two nonzero entries, and some row has exactly two. Then independent row and column permutations turn U into U2 direct sum U2.

Use a simultaneous relabeling to put the extra zero at u12=0, with u13 and u14 nonzero. Column 2 can have nonzero entries only in rows 3 and 4, so u32 and u42 are nonzero. Orthogonality of columns 2 and 3 gives u43=0, and that of columns 2 and 4 gives u34=0. Column 3 has only its entries in rows 1 and 2 left, so u23 is nonzero. Orthogonality of columns 1 and 3 then gives u21=0.

The support consists of rows {1,2} into columns {3,4}, and rows {3,4} into columns {1,2}. Each resulting two-by-two block is unitary. The product of its two U2 laws gives a common-minor law on at most four permutations.

This is a complete classification of this support case; no assumption about phases or equal entry moduli was used.

## Round 023 — Every zero-diagonal U4 has a common-minor law

**Theorem proved.** If all four diagonal entries of U4 vanish, U has a common-minor law, and consequently satisfies MOC for arbitrary complex spectra.

Rounds 021 and 022 handle any row or column of degree at most two. In the remaining case all twelve off-diagonal entries are nonzero. Row-pair and column-pair orthogonality then imply

\[
|U|^2=\begin{pmatrix}
0&x&y&z\\x&0&z&y\\y&z&0&x\\z&y&x&0
\end{pmatrix},\qquad x+y+z=1.
\]

For example, orthogonality of rows 1 and 2 and of columns 3 and 4 gives p13 p23=p14 p24 and p13 p14=p23 p24. Positivity allows division, hence p13=p24 and p14=p23; the other pairs give the displayed pattern.

The law on nine derangements is

| Permutation | Weight |
|---|---:|
| (12)(34) | x² |
| (13)(24) | y² |
| (14)(23) | z² |
| (1243), (1342) | xy each |
| (1234), (1432) | xz each |
| (1324), (1423) | yz each |

The weights sum to one. Principal two-minor probabilities are x²,y²,z². The complementary disjoint minors have probabilities (1−x)²,(1−y)²,(1−z)²: the two restricted rows are orthogonal and have equal squared norm 1−x, etc. Any minor with one overlapping index contains a zero entry, so its determinant has one nonzero monomial and gives xy,xz,or yz. The displayed law gives precisely these values. Singletons and three-minors follow from the displayed p and unitary complementarity.

The earlier theorem for twelve nonzero entries therefore extends to the entire zero-diagonal variety by a support classification, not by an unproved density assertion. Independent reviewer has been given the full proof.


## Round 025 — Real quartic zeros force the Gram parameter

**Exact lemma.** If M(z) is positive semidefinite and q(t0)=0, then

\[
M(z)(1,t_0,t_0^2)^T=0.
\]

This is the elementary kernel property of a positive semidefinite quadratic form. For t0 nonzero, its first row gives

\[
z=-\frac{q_0+(q_1/2)t_0}{t_0^2}.
\]

Thus any nonzero real root fixes the Gram parameter uniquely. Two different real roots impose a compatibility identity rather than two independently adjustable SOS choices. This explains the rigidity of Round 024: the roots t=±1 both force z=−64.

**Consequence for a universal proof.** A formula proposed only from generic strictly positive cases must extend to the forced parameter on every support-contact stratum. Choosing a convenient fixed parameter cannot bypass this requirement. This is a local algebraic obstruction to proposed certificates, not an obstruction to MOC itself.


## Round 027 — Reciprocal isoclinic rays reduce the quartic to a quadratic

Assume the identity is a maximizing permutation for the support under consideration, as in the canonical radial reduction, and take a real skew-symmetric K with K²=−I. Then U_t is an isoclinic quaternion circle. Reciprocal Cayley symmetry gives

\[
q_4=q_0,\qquad q_3=-q_1.
\]

For nonzero t, put y=t−1/t. Then

\[
q(t)/t^2=q_0y^2-q_1y+(q_2+2q_0).
\]

The variable y covers the whole real line. Thus, when q0>0, positivity on the entire radial ray is equivalent to the elementary condition

\[
q_2+2q_0\ge q_1^2/(4q_0).
\]

The q0=0 case requires q1=0 and q2 nonnegative. This reduction is exact on these rays. It does not cover a general skew-Hermitian Cayley direction, where the two independent singular frequencies destroy this reciprocal two-coefficient collapse.

## Round 028 — A complete isoclinic determinant expansion with one interference term

Let

\[
U(c,u,v,w)=\begin{pmatrix}
c&u&v&w\\-u&c&w&-v\\-v&-w&c&u\\-w&v&-u&c
\end{pmatrix},\qquad c^2+u^2+v^2+w^2=1.
\]

Because det U=1, the determinant is the ordinary determinant of the matrix with entries (a_i+b_j)u_ij. Its expansion is

\[
\begin{aligned}
d(U)={}&c^4z_{id}+u^4z_{(12)(34)}+v^4z_{(13)(24)}+w^4z_{(14)(23)}\\
&+c^2u^2(z_{12}+z_{34})+c^2v^2(z_{13}+z_{24})+c^2w^2(z_{14}+z_{23})\\
&+u^2v^2(z_{1243}+z_{1342})+u^2w^2(z_{1234}+z_{1432})\\
&+v^2w^2(z_{1324}+z_{1423})+cuvwT,
\end{aligned}
\]

where

\[
T=-(z_{123}-z_{132})+(z_{124}-z_{142})
 -(z_{134}-z_{143})+(z_{234}-z_{243}).
\]

Every coefficient in the even part is nonnegative, and those sixteen coefficients sum to one. All possible failure of convexity on this entire quaternion family is therefore concentrated in the single scalar chiral term cuvwT.

This is considerably smaller than treating all second-minor probabilities as free. It retains the actual unitary and spectral structure simultaneously.

## Round 029 — The chiral term is an exact cross-ratio bracket

Define

\[
\alpha_1=(a_1-a_2)(a_3-a_4),\quad
\alpha_2=(a_1-a_3)(a_2-a_4),
\]

and the corresponding beta1,beta2 from b. Exact expansion yields

\[
\boxed{T=-2(\alpha_1\beta_2-\alpha_2\beta_1).}
\]

The equality has been checked by formal polynomial coefficients in eight independent variables, not by a floating-point fit. The standalone exact certificate is `analysis/quaternion_chirality_exact.py`: it expands all eight permutation terms and the four bracket factors into integer monomial dictionaries, and every residual coefficient is zero.

This identifies the interference with a two-by-two determinant in the two independent pair-difference coordinates. It vanishes when those spectral coordinates are proportional. The identity is valid also for repeated eigenvalues and does not require dividing by a difference.

## Round 030 — A completed matched-cross-ratio isoclinic theorem

**Theorem proved.** If alpha1 beta2=alpha2 beta1, then every U(c,u,v,w) in Round 028 satisfies MOC for these complex spectra.

Indeed T=0, and the sixteen displayed even coefficients are an explicit probability law producing d(U) from the permutation products. No support-direction argument is needed. The equality hypothesis includes degenerate difference cases; when the denominators are nonzero it says that the paired cross-ratio coordinates agree.

A slightly broader directional conclusion holds whenever Re(eta T)=0: the support inequality is immediate even if T itself is nonzero.

**Scope.** This is one isoclinic quaternion factor inside SO4. A general SO4 matrix uses two independent quaternion factors. Arbitrary complex U4 requires additional phases. No step here removes either restriction. Historical overlap with fractional-linear transformations of spectra has not been researched in this batch, so no novelty claim is attached.

## Round 031 — Full isoclinic MOC is exactly a geometric-program capacity bound

Let q=(c,u,v,w). Set

\[
d=(\delta_{id},\delta_{(12)(34)},\delta_{(13)(24)},\delta_{(14)(23)}),
\]

and

\[
\begin{array}{lll}
e_{01}=\delta_{12}+\delta_{34},&e_{02}=\delta_{13}+\delta_{24},&e_{03}=\delta_{14}+\delta_{23},\\
e_{12}=\delta_{1243}+\delta_{1342},&e_{13}=\delta_{1234}+\delta_{1432},&e_{23}=\delta_{1324}+\delta_{1423}.
\end{array}
\]

Write R=Re(eta T). The exact support deficit is

\[
F(q)=\sum_i d_iq_i^4+\sum_{i<j}e_{ij}q_i^2q_j^2-Rq_0q_1q_2q_3.
\]

All even coefficients are nonnegative. If any coordinate vanishes, F is nonnegative. Otherwise divide by |q0 q1 q2 q3| and put x_i=q_i²/sqrt(|q0 q1 q2 q3|), so product x_i=1. Conversely every positive x with product one comes from a ray of quaternion magnitudes. The signs of the q_i can choose the unfavorable sign of R. Therefore

\[
\boxed{F\ge0\text{ for all }q\iff |R|\le
\operatorname{cap}(d,e)},
\]

where

\[
\operatorname{cap}(d,e)=\inf_{x_i>0,\ \prod x_i=1}
\left(\sum_i d_ix_i^2+\sum_{i<j}e_{ij}x_ix_j\right).
\]

After x_i=exp(y_i), this is convex minimization of a sum of exponentials on sum y_i=0. This is an exact direct attack on a substantial MOC subfamily, with a concrete remaining scalar spectral inequality. It is not a proof that the capacity bound always holds.

## Round 032 — Optimal weighted AM–GM certificates for that capacity

Index the ten even monomials by j. Their coefficients are c_j in {d_i,e_ik}; their exponent vectors are a_j=2e_i or e_i+e_k. Let lambda_j be nonnegative and satisfy

\[
\sum_j\lambda_j=1,\qquad
\sum_j\lambda_ja_j=(1/2,1/2,1/2,1/2).
\]

Weighted AM–GM gives, for product x_i=1,

\[
\sum_jc_jx^{a_j}\ge
\prod_j(c_j/\lambda_j)^{\lambda_j}.
\]

For positive coefficients the best bound of this form equals the capacity. At a minimizer of the convex exponential function, set lambda_j=c_j exp(a_j·y)/cap. The first-order condition gives exactly the displayed balancing constraint, and equality holds in AM–GM. Boundary cases follow by positive regularization and a limit.

Thus the isoclinic proof can be sought as an explicit balanced fractional matching on the four quaternion coordinates, with coefficients depending on the spectral gaps. The simplest fixed matching is not guaranteed optimal. The result supplies a complete certificate language for this one-negative-monomial quartic; it does not construct the needed lambda for all spectra.


## Round 034 — Balanced isoclinic directions with identity-maximizing support

A further restricted theorem can be proved from exact rank-two identities among the spectral vertices.

Assume the identity is a maximizing permutation in the chosen support direction, so delta_id=0. Put S=sum of the six transposition gaps and D=sum of the three double-transposition gaps. The matrix (a_i+b_j) has rank at most two. Its three-by-three determinant identities imply that the two opposite three-cycle gaps on any triple sum to the three transposition gaps on that triple. Hence the sum of all eight three-cycle gaps is 2S. Its four-by-four determinant identity then gives

\[
\sum_{\text{six four-cycles}}\delta_\pi=D+S,
\quad
\sum_{\text{nine derangements}}\delta_\pi=2D+S.
\]

On the balanced circle u²=v²=w²=s²/3, the support deficit becomes

\[
s^2(ac^2+bs^2+ecs),\quad
 a=S/3,\quad b=(2D+S)/9,
\]

with |e|≤2S/(3sqrt(3)), by the three-cycle sum and the triangle inequality. Since D≥0,

\[
e^2\le4S^2/27\le4ab.
\]

The quadratic is nonnegative, proving the entire circle for these jointly restricted supports.

**Essential scope restriction:** relabeling a maximizing permutation to the identity changes the unitary. It need not preserve this balanced circle. Therefore the identity-maximizing assumption cannot simply be declared without loss of generality for a fixed balanced U. The result proves exactly the stated conditional support theorem.


## Round 037 — Exact criterion for total freezing on one Bloch fiber

On a two-row unitary fiber the determinant is affine on the Bloch sphere:

\[
d(n)=\alpha+\beta\cdot n,\qquad n\in S^2.
\]

Let L have rows Re beta and Im beta. Suppose rank L=2, and let v span its real nullspace. Starting at n0, any determinant-preserving randomized step must have its mean in

\[
\{n_0+tv:t\in\mathbb R\}\cap\overline B_3.
\]

If n0·v=0, this line is tangent to the unit ball, so the only possible mean is n0. A sphere-valued random vector with mean of norm one is constant almost surely. Hence every such step is frozen.

If n0·v is nonzero, the opposite point of the chord is

\[
n_1=n_0-2\frac{n_0\cdot v}{|v|^2}v.
\]

It lies on the same determinant fiber. This gives an exact nontrivial alternative, but its off-diagonal energy need not decrease. Thus the local problem has a sharp geometric distinction between exposed ellipse points and interior ellipse points; merely allowing randomization does not remove the exposed-point obstruction.

## Round 038 — An actual nonmonomial U4 frozen for all six separate row-pair martingales

For real orthogonal U, C=U diag(b) U^T is complex symmetric. Rotate A instead of C when analyzing a two-row fiber. Its relevant two-by-two Schur complement is symmetric, so the antisymmetric Bloch coefficient vanishes identically:

\[
d(n)=\alpha+\beta_x n_x+\beta_z n_z,\qquad\beta_y=0.
\]

The current point is n0=(0,0,1). If Im(beta_x conjugate(beta_z)) is nonzero, preserving both real and imaginary determinant means forces E nx=0 and E nz=1. The step is therefore constant almost surely.

Use

\[
U=\frac1{\sqrt{13}}\begin{pmatrix}
1&2&2&2\\-2&1&2&-2\\-2&-2&1&2\\-2&2&-2&1
\end{pmatrix},
\]

with the following exact Gaussian-integer spectra:

\[
a=(-i,-1+i,1-2i,-1),\qquad b=(-2+2i,2i,-1-2i,-1+2i).
\]

These are the source data from original Round 026; none of its separate Gram-parameter discussion is needed here. Set A=diag(a), B=diag(b), C=UBUᵀ, d(U)=det(A+C), and V(U)=∑_{r≠s}|C_{rs}|². The Bloch coefficients below refer to d(n)=α+β_x n_x+β_z n_z at n₀=(0,0,1), with β_y=0. Exact calculations give:

| Row pair | Im(beta_x conjugate(beta_z)) |
|---|---:|
| 12 | −8960/2197 |
| 13 | 1376/169 |
| 14 | −7264/2197 |
| 23 | −8256/169 |
| 24 | 272/2197 |
| 34 | −72768/2197 |

All six are nonzero. For completeness, the full rational coefficients from the original `analysis/real_fiber_freeze.json` are:

| Row pair | β_x | β_z |
|---|---|---|
| 12 | (−872+24i)/169 | (88−136i)/169 |
| 13 | (−1208+1720i)/169 | (−348+688i)/169 |
| 14 | (−240+256i)/169 | (−382+14i)/169 |
| 23 | (−1228+2492i)/169 | (−1201+1301i)/169 |
| 24 | (64−56i)/169 | (42−92i)/169 |
| 34 | (1208+232i)/169 | (88+800i)/169 |

For each pair, α=d(U)−β_z, so the spectra, displayed U and this table specify the entire affine determinant fiber without an external data file. These same data are used by the positive compensated-escape results in [analysis_theorem_notes_041_060.md](analysis_theorem_notes_041_060.md), Rounds 055–056.

**Conclusion proved:** any algorithm that first chooses a row pair and then preserves the complex determinant conditionally within that pair cannot move at all from this nonmonomial point. This is stronger than an abstract possible local maximum obstruction. Random steps whose determinant changes compensate between different pairs, or genuinely nonlocal moves, are not excluded.

## Round 039 — The remaining real SO4 problem retains two rotation factors

The root supplied the exact Spin decomposition relevant to a general real O4 attack. In compatible paired coordinates, the SO6 image splits as two SO3 factors Q+ and Q−. Consequently

\[
m_{ij}=(Q_+)_{ij}^2+(Q_-)_{ij}^2,\qquad
h_{ij}=(Q_+)_{ij}(Q_-)_{ij}.
\]

For P=(Q++Q−)/2 and D=(Q+−Q−)/2,

\[
PP^T+DD^T=I.
\]

Writing Q+^T Q− as a rotation by angle 2 theta shows that P has singular values (1,|cos theta|,|cos theta|), and D has singular values (|sin theta|,|sin theta|,0). The rank defect follows directly from the fixed rotation axis.

For a cost sum F_ij m_ij+E_ij h_ij, substitution gives the exact expression

\[
\sum_{ij}(2F_{ij}+E_{ij})P_{ij}^2
+\sum_{ij}(2F_{ij}-E_{ij})D_{ij}^2.
\]

Thus the unrestricted real problem is a coupled quadratic optimization with a common axis and orthogonality relations, rather than two independently optimizable arrays. No inequality completing the interaction with the rank-two spectral coefficient array F is established here.

This records the precise extension beyond one quaternion factor and the remaining obstruction. The capacity theorem of Round 031 does not automatically iterate through the two factors.

## Round 040 — A canonical closed-form Gram parameter for the unrestricted radial target

Return to an arbitrary Cayley ray, with no isoclinic restriction. Suppose q0,q4>0 and put r²=q0q4. Four times the Gram determinant is the cubic

\[
D(z)=8z^3-4q_2z^2+(2q_1q_3-8r^2)z
 +4r^2q_2-q_4q_1^2-q_0q_3^2.
\]

For |z|<r, positivity of the two-by-two corner block and the Schur complement show that M(z) is PSD exactly when D(z)≥0. At the endpoints,

\[
D(\pm r)=-(\sqrt{q_4}q_1\mp\sqrt{q_0}q_3)^2\le0.
\]

The only possible interior local maximum of D is

\[
\boxed{z_*={q_2-\sqrt{q_2^2-3q_1q_3+12q_0q_4}\over6}.}
\]

**Exact certificate lemma.** If the quartic has a PSD Gram matrix in this family, M(z*) is also PSD. Starting with any feasible M(z), add epsilon diag(1,2,1). This is a positive definite Gram matrix for q+epsilon(1+t²)², so the corresponding cubic is positive at an interior parameter. Its positive maximum lies at its smaller critical point. Passing to the limit epsilon→0 proves the assertion, including saturated corner cases. The q0=0 or q4=0 degeneracies reduce to the corresponding two-by-two Gram condition.

Consequently the full radial positivity problem does not require an arbitrary search over z: it suffices to force this canonical radical choice into the feasible range and prove its Schur complement nonnegative. The unresolved universal bridge is now explicit:

> Do the 24 actual spectral support inequalities, together with the exact Cayley coefficient identities and rank-two spectral structure, imply that M(z*) is positive semidefinite for every skew-Hermitian K?

No derivation of this implication was obtained in this batch. The natural replacements z=0 and z=±sqrt(q0q4) are disproved by Rounds 024 and 026, and the low-dimensional moment-cone shortcuts were disproved in earlier batches. The remaining claim must use the actual coupled geometry rather than those relaxations.


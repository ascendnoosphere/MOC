## Conventions used throughout

Let a,b be arbitrary complex spectra of length four, let z_pi=product_i(a_i+b_pi(i)), and fix a support direction eta. Relabel the b-spectrum so that the identity maximizes Re(eta z_pi). Put

\[
h=\operatorname{Re}(\eta z_{id}),\qquad
\delta_\pi=h-\operatorname{Re}(\eta z_\pi)\ge0.
\]

For a zero-diagonal skew-Hermitian K, let

\[
U_t=(I+tK)(I-tK)^{-1},\quad
P_K(t)=h|\det(I-tK)|^2-
\operatorname{Re}\bigl(\eta\det[S+t[A-B,K]-t^2KSK]\bigr),
\]

where S=A+B. Then P_K(t)=t²q_K(t), with q=q0+q1t+q2t²+q3t³+q4t⁴. These are deficit coefficients, so their sign convention is opposite to a numerator-minus-support convention.

For a triple i<j<k, define

\[
\omega_{ijk}=K_{ij}K_{jk}K_{ki},\quad
\Delta_{ijk}=\delta_{(ijk)}-\delta_{(ikj)},\quad
\Sigma_{ijk}=\delta_{ij}+\delta_{ik}+\delta_{jk}.
\]

The three-by-three rank-two determinant identity gives Sigma_ijk=delta_(ijk)+delta_(ikj). Indices outside a displayed cycle are fixed.

## Round 041 — Exact cleared deficit for each principal U3 problem

Set all entries of K outside one triple to zero. The spectator contributes its fixed spectral factor. Let p_e=|K_e|² for the triple's three edges, and put

\[
A_S=\sum_{e\subset S}\delta_e p_e,\qquad
C_S=\sum_{e\subset S}\delta_e\prod_{f\subset S,\,f\ne e}p_f.
\]

Then the exact principal deficit is

\[
\boxed{P_S(t)=4t^2[A_S+2t\operatorname{Re}(\omega_S)\Delta_S+t^2C_S].}
\]

One derivation uses the rank-three common-minor identity from the root's Jordan theorem. For a zero-diagonal three-by-three K, the off-diagonal Cayley numerators are exactly

\[
\det(I-tK)(U_t)_{ij}=2t[K_{ij}+t(K^2)_{ij}].
\]

The symmetric off-diagonal flows produce the transposition gaps; the directed circulation is 16t³ Re(omega), producing half that circulation times the difference of the two three-cycle gaps. This proves the displayed formula, including its signs.

## Round 042 — Explicit spectral SOS for every principal triple

Let kappa=Delta_S/Sigma_S, with the zero-Sigma case interpreted separately. The nonnegative permutation gaps give |kappa|≤1. Choose the cyclic edges (ij),(jk),(ki). Their quantities Re(K_e conjugate((K_S²)_e)) all equal Re(omega_S). Therefore

\[
\boxed{\frac{P_S(t)}{4t^2}=
\sum_{e\text{ cyclic}}\delta_e
|K_e+t\kappa(K_S^2)_e|^2
+t^2(1-\kappa^2)\sum_{e\text{ cyclic}}\delta_e|(K_S^2)_e|^2.}
\]

If Sigma=0, all three transposition gaps and both cycle gaps vanish, so the deficit is zero. This is an exact, parameter-dependent sum of squares over arbitrary complex edge phases. It identifies a concrete rank-three certificate that can be used in a gluing attempt, rather than invoking MOC3 as an unexplained black box.

## Round 043 — The unrestricted low coefficients are sums of local edge and triangle terms

Degree and diagonal-gauge invariance yield

\[
\boxed{q_0=4\sum_{i<j}\delta_{ij}|K_{ij}|^2,}
\]

\[
\boxed{q_1=8\sum_{i<j<k}\operatorname{Re}(K_{ij}K_{jk}K_{ki})\Delta_{ijk}.}
\]

The first formula is the familiar local transposition Hessian. The second is exactly the sum of the four principal-triple cubic terms: no graph involving all four vertices can occur in degree three when the diagonal is zero.

The two formulas remain valid with a nonzero imaginary diagonal of K. Such diagonal terms contribute only purely imaginary edge self-products to the cubic expansion, so their real parts cancel. This observation is needed when applying inverse reciprocity, because K inverse need not have zero diagonal.

The formulas were checked against the retained exact quartic example q=(2960,−3904,26976,−7552,12800); they give exactly its first two entries.

## Round 044 — Full four-dimensional off-diagonal Cayley numerators

For zero-diagonal K4, Cayley–Hamilton gives

\[
\boxed{\det(I-tK)(U_t)_{ij}
=2t[K_{ij}+t(K^2)_{ij}-t^2(\operatorname{adj}K)_{ij}],\quad i\ne j.}
\]

Indeed, with e2 the second characteristic coefficient and e3 the third, the adjugate of I−tK is I+tK+t²(K²+e2I)+t³(K³+e2K−e3I). Multiplication by I+tK and Cayley–Hamilton leave only scalar diagonal terms at degree four; off the diagonal, K³+e2K=−adj K.

Consequently

\[
|\det(I-tK)|^2|(U_t)_{ij}|^2
=4t^2|K_{ij}+t(K^2)_{ij}-t^2(\operatorname{adj}K)_{ij}|^2.
\]

This supplies actual coherent low/middle/high vectors. It does not itself give a positive determinant law: the mixed degree-(2,2) spectral contribution also depends on second minors.

## Round 045 — Exact reciprocal formulas for the high coefficients

For invertible K,

\[
U_K(t)=-U_{-K^{-1}}(1/t),
\qquad
P_K(t)=|\det K|^2t^8P_{-K^{-1}}(1/t).
\]

The scalar minus sign does not affect UBU*. Therefore

\[
\boxed{q_4=4\sum_{i<j}\delta_{ij}|(\operatorname{adj}K)_{ij}|^2,}
\]

and

\[
\boxed{q_3=-8|\det K|^2\sum_{i<j<k}
\operatorname{Re}[(K^{-1})_{ij}(K^{-1})_{jk}(K^{-1})_{ki}]\Delta_{ijk}.}
\]

The second expression is written rationally but agrees with a homogeneous polynomial of degree five. Singular K are covered by continuity of the original coefficients. In particular both end coefficients are nonnegative without a global MOC proof. The odd middle terms remain correlated with them through actual inverse/cofactor geometry.

## Round 046 — Hodge duality makes the entire real high-degree part explicit

For real skew-symmetric K4, define its Pfaffian

\[
\rho=K_{12}K_{34}-K_{13}K_{24}+K_{14}K_{23}
\]

and its real Hodge dual by

\[
(*K)_{12}=K_{34},\quad (*K)_{13}=-K_{24},\quad (*K)_{14}=K_{23},
\]

with the complementary upper entries (*K)23=K14, (*K)24=−K13, (*K)34=K12 and skew symmetry below the diagonal. Then K(*K)=−rho I and det K=rho². The reciprocal formulas simplify to

\[
\boxed{q_3(K)=\rho\,q_1(*K),\qquad
q_4(K)=\rho^2q_0(*K),\qquad q_2(K)=q_2(*K).}
\]

These polynomial identities extend through rho=0. Thus the real problem has a transparent forward/backward duality. A rank-two real K has rho=0 and its entire radial deficit reduces to a quadratic q0+q1t+q2t². That reduction alone does not prove its discriminant condition.

## Round 047 — Classifying every possible degree-four graph

For a zero-diagonal K, conjugation by diagonal phases leaves the determinant question unchanged. Every monomial contributing to q2 therefore has balanced phase degree at each vertex.

There are only three types in degree four: a squared single edge, the product of two squared edge moduli, and an oriented four-cycle plus its conjugate. A squared single edge has zero coefficient, as follows by restricting to a single U2 rotation. The two-edge terms split into adjacent edges supported on a triple and disjoint edges covering all four vertices.

Furthermore d(U conjugate)=d(U): their corresponding minors have identical squared moduli. Hence q2 is unchanged under conjugating K. Its cycle contributions use Re(omega_cycle), not the imaginary part.

This finite classification means that the principal U3 formulas, the two-block formulas, and the three real four-cycle coefficients determine q2 for every complex skew-Hermitian K. No numerical interpolation over arbitrary matrices is needed.

## Round 048 — Exact coefficient for each disjoint matching

Take only Kij=x and Kkl=y nonzero, where the two edges are disjoint. The unitary splits into two U2 blocks. The two mixing probabilities are X=4x²t²/(1+x²t²)² and Y=4y²t²/(1+y²t²)² in the real case; replace x²,y² by squared moduli otherwise.

The degree-four coefficient on |x|²|y|² is

\[
\boxed{B_{ij|kl}=8(2\delta_{(ij)(kl)}-\delta_{ij}-\delta_{kl}).}
\]

This can have either sign even though every permutation gap is nonnegative. It is precisely the signed four-index interaction missed by simply adding positive principal-triple coefficients.

Index the three matchings as 1=12|34, 2=13|24, 3=14|23, and abbreviate their coefficients by B1,B2,B3 below.

## Round 049 — Four-cycle coefficients collapse to the same three matching combinations

For c=(i j k l), the coefficient of Re(Kij Kjk Kkl Kli) can initially be expressed as

\[
8[\delta_{ij}+\delta_{kl}-2\delta_{(ij)(kl)}
-\delta_{(ijkl)}-\delta_{(ilkj)}
+\delta_{(ijlk)}+\delta_{(iklj)}].
\]

The actual rank-two spectral vertex identities simplify the three coefficients to

\[
\begin{array}{c|c}
\text{Cycle}&\text{coefficient}\\\hline
1234&-(B_1+B_3-B_2)\\
1243&-(B_1+B_2-B_3)\\
1324&-(B_2+B_3-B_1).
\end{array}
\]

These identities were verified as formal integer-coefficient polynomial identities in the eight spectral variables. The full symbolic calculation, including extraction of the Cayley coefficient, is retained in `analysis/cayley_real_quartic.py` and its JSON output.

Thus no independent four-cycle spectral coefficient survives in q2. The four-dimensional even residue depends on just three matching-gap combinations; the four antisymmetric three-cycle gap combinations remain in q1 and q3.

## Round 050 — Complete middle-coefficient formula, including unrestricted complex phases

Combining Rounds 047–049 yields

\[
\begin{aligned}
q_2={}&4\sum_{i<j}\delta_{ij}\sum_{k\notin\{i,j\}}|K_{ik}|^2|K_{kj}|^2\\
&+B_1|K_{12}K_{34}|^2+B_2|K_{13}K_{24}|^2+B_3|K_{14}K_{23}|^2\\
&-(B_1+B_3-B_2)\operatorname{Re}\Omega_{1234}\\
&-(B_1+B_2-B_3)\operatorname{Re}\Omega_{1243}\\
&-(B_2+B_3-B_1)\operatorname{Re}\Omega_{1324},
\end{aligned}
\]

where Omega_ijkl=Kij Kjk Kkl Kli. This is an unrestricted coefficient identity, not only a real-matrix statement.

For real K, put r=(K12K34,−K13K24,K14K23). Then Omega1234=−r1r3, Omega1243=−r1r2, and Omega1324=−r2r3. The four-index part is exactly r^T H(B) r, with

\[
H_{ii}=B_i,\qquad H_{ij}=(B_i+B_j-B_k)/2.
\]

Equivalently,

\[
r^THr=(r_1+r_2+r_3)\sum_iB_ir_i-
(B_1r_2r_3+B_2r_1r_3+B_3r_1r_2).
\]

For complex K this three-vector packaging fails because the cycle phases contain different conjugations. The full displayed formula retains them correctly.


## Round 053 — The correct coupled SOS on a disjoint two-block graph

For a single disjoint matching e,f, the full quadratic-in-t² certificate is nevertheless explicit:

\[
\boxed{q(t)=4\delta_e|x|^2(1-|y|^2t^2)^2
+4\delta_f|y|^2(1-|x|^2t^2)^2
+16\delta_{ef}|x y|^2t^2.}
\]

All coefficients outside the squared factors are nonnegative. Expansion gives exactly the matching coefficient from Round 048 and the two reciprocal end coefficients.

This proves that the required negative middle interference is compatible with an exact positive certificate: it belongs inside squares of 1−c t². The unresolved problem is to glue these matching certificates to the triangle-circulation certificates with shared edge and cofactor data. Simply adding them would count the same Hessian resources more than once.

## Round 054 — Necessary and sufficient first-order condition for cross-pair escape

For real row-rotation angles theta_e at a real orthogonal U, write g_e=d'_e(0) in C and v_e=V'_e(0), where V is the off-diagonal Frobenius energy of C=U diag(b) U*. Let J be the real two-by-six matrix with columns (Re g_e,Im g_e).

There is a real tangent w satisfying Jw=0 and v·w<0 exactly when v is not in the row span of J. This is elementary orthogonal decomposition: take minus the projection of v onto ker J when it is nonzero.

If rank J=2, the complex determinant level set is a regular local submanifold. The implicit-function theorem corrects a kernel tangent by terms of order t² to an exact constant-determinant path. Thus this linear criterion provides a genuine local descent result, not only a formal cancellation of first derivatives.

It does not imply that every nonmonomial point has such a tangent. A constrained energy minimum necessarily obstructs this deterministic criterion.

## Round 055 — An exact coupled tangent escapes the earlier fully frozen example

Use the real U, exact spectra and rational Bloch-coefficient table in [Round 038 of analysis_theorem_notes_021_040.md](analysis_theorem_notes_021_040.md). Put C=U diag(b) Uᵀ, d(U)=det(diag(a)+C), and V(U)=∑_{r≠s}|C_{rs}|². For i<j, let G_ij(θ) be the identity except for the block [[cos θ,sin θ],[−sin θ,cos θ]] in rows and columns i,j, and rotate by U↦G_ij(θ)U. In the source Bloch convention this gives n=(sin 2θ,0,cos 2θ), so g_ij=d'_ij(0)=2β_x,ij. In particular,

\[
(g_{12},g_{13},g_{14})=\frac1{169}(-1744+48i,\ -2416+3440i,\ -480+512i).
\]

The source point's separate determinant-preserving row-pair steps are frozen, but cross-pair compensation is allowed. For this rotation convention,

\[
V'_{ij}(0)=-4\Re\bigl((C_{ii}-C_{jj})\overline{C_{ij}}\bigr).
\]

The energy derivatives in the first three pairs 12,13,14 are

\[
(-96,-360,-72)/169.
\]

The tangent weights

\[
\boxed{w_{12}=-809,\quad w_{13}=-1699,\quad w_{14}=11491}
\]

satisfy d'(0)=0 exactly, while

\[
V'(0)=-138048/169<0.
\]

The first two complex determinant derivatives are linearly independent over the reals. Hence an actual real-orthogonal, constant-complex-determinant path with this tangent exists and strictly lowers energy for sufficiently small positive t.

The exact determinant and energy derivatives needed here are now displayed above, and the integer null vector is displayed in the proof. They agree with the original `analysis/compensated_escape.json`, produced by `analysis/compensated_escape.py`; those external files are not needed to check this local result. The step uses compensation between pairs, which the individual-fiber restriction does not exclude.

## Round 056 — A three-atom compensated determinant martingale also escapes

The same calculation gives a randomized step supported on three individual row-pair rotations, with equal probabilities one third. Set theta14(t)=11491t. Solve theta12(t),theta13(t) near zero so that

\[
\frac{d(G_{12}(\theta_{12})U)+d(G_{13}(\theta_{13})U)+d(G_{14}(\theta_{14})U)}3=d(U).
\]

The two real equations have an invertible Jacobian in the first two angles. The implicit-function theorem gives an exact solution, whose derivatives are −809 and −1699. Consequently the expected energy derivative is

\[
\boxed{-46016/169<0.}
\]

This is an actual local determinant martingale step, not just a constant-determinant deterministic path. Each atom changes the determinant, and the three changes compensate in expectation. It proves that allowing cross-pair compensation overcomes the strongest obstruction found in the previous batch.

## Round 057 — A common-dual criterion for all finite cross-pair steps

Consider the union of all six row-pair Bloch spheres, and for each allowed point form the increment vector (Delta Re d,Delta Im d,Delta V). The best finite compensated step is the minimum third coordinate in the convex hull over the slice where the first two coordinates vanish.

At a regular point where the determinant increments span a neighborhood of zero, convex duality gives an exact obstruction to strict improvement: there is one common real multiplier lambda in R² satisfying

\[
\Delta V-\lambda\cdot\Delta d\ge0
\]

for every point on every allowed sphere. Unlike separate-fiber arguments, the multiplier must be the same for all six pairs.

Each sphere inequality is quadratic. If it is c+ell·n−n^T G n≥0 on |n|=1, it is equivalent to existence of a scalar tau such that

\[
\begin{pmatrix}
c-\tau&\ell^T/2\\\ell/2&\tau I-G
\end{pmatrix}\succeq0.
\]

This follows by dualizing the exact sphere-moment cone established in Round 018. Thus the finite cross-pair obstruction has a concrete semidefinite formulation with one shared two-component multiplier and six scalar sphere multipliers. At singular boundary points one must retain the unnormalized supporting-plane form; finite multiplier attainment is not asserted without the stated regularity.

## Round 058 — Exact second-order test at a real constrained critical point

For a real U, write each pair's Bloch data as

\[
d(n)=\alpha+\beta_x n_x+\beta_z n_z,
\quad V(n)=v_0-\tfrac12|\gamma_x n_x+\gamma_z n_z|^2,
\]

where gamma_x=2Cij and gamma_z=Cii−Cjj. Near n0=(0,0,1), let x=nx,y=ny and nz=1−(x²+y²)/2+O((x²+y²)²).

Suppose the first-order energy derivatives equal a common multiplier lambda applied to the determinant derivatives, so first-order compensated descent is unavailable. The quadratic coefficients of V−lambda·d in this pair are

\[
\frac12(|\gamma_z|^2-|\gamma_x|^2+\lambda\cdot\beta_z)
\quad\text{and}\quad
\frac12(|\gamma_z|^2+\lambda\cdot\beta_z)
\]

in x² and y² respectively. If either is negative, symmetric small noise in that coordinate lowers the Lagrangian in expectation. At a rank-two determinant Jacobian, order-t² drifts in other pairs compensate its determinant increment, giving a strict second-order martingale improvement.

If all these coefficients are nonnegative, this particular pair-noise mechanism has no second-order descent. Mixed directions involving simultaneous rotations may still matter. No theorem excluding such stationary obstructions universally was obtained.

## Round 059 — Star-minor plaquettes are tied exactly to singleton probabilities

Write

\[
U=\begin{pmatrix}u&r\\c&V\end{pmatrix},\qquad X=uV-cr.
\]

The earlier collective identity XX*=|u|²I+cc* is supplemented by the exact anchored-minor identity

\[
\det X[\{i,k\},\{j,l\}]
=u\det U[\{1,i,k\},\{1,j,l\}].
\]

Unitary complementary minors therefore give

\[
|X_{ij}X_{kl}-X_{il}X_{kj}|^2=|u|^2p_{rm},
\]

where r,m are the complementary row and column indices. Writing qij=|Xij|² yields the explicit necessary bounds

\[
(\sqrt{q_{ij}q_{kl}}-\sqrt{q_{il}q_{kj}})^2
\le |u|^2p_{rm}\le
(\sqrt{q_{ij}q_{kl}}+\sqrt{q_{il}q_{kj}})^2.
\]

More precisely, the equation fixes the real part of each four-entry phase product. Thus p and q determine every star plaquette cosine; they are not freely adjustable Gram phases. This retains common-unitary information lost in the earlier failed convex relaxations.

## Round 060 — A complete anchor-based U2 parametrization and the remaining bridge

The same blocks satisfy Xr*=−c. Put d=1−|u|², with 0<|u|<1. Since ||c||²=||r||²=d, every actual star matrix has the form

\[
\boxed{X=-cr/d+uZ,}
\]

where

\[
Zr^*=0,\quad c^*Z=0,\quad
ZZ^*=I-cc^*/d,\quad Z^*Z=I-r^*r/d.
\]

Thus Z is a unitary map between the two-dimensional orthogonal complements of the anchored row and column vectors. Conversely these equations give

\[
V=-\overline u\,cr/d+Z
\]

and direct multiplication verifies that the resulting block matrix U is unitary. This is a complete parametrization on the stated anchor stratum; u=0 and |u|=1 are its separate boundary cases.

This improves the star singular-value relaxation by fixing its unit singularvector and both orthogonal complements. After row/column phase gauges, the remaining internal freedom is exactly U2. The determinant objective on this internal fiber still contains correlated second-minor interference; no proof that its maximum occurs on already solved boundary strata was obtained.

The batch therefore leaves two concrete universal bridges. The first is positivity of the fully explicit coupled Cayley quartic in Rounds 043–050 under actual spectral constraints. The second is the absence, or bypass, of a common-multiplier obstruction in Round 057 while descending toward a permutation-supported law. The exact compensated escape is a positive local result; it is not a global termination proof.


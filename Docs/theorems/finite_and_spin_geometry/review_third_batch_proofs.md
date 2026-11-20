## 1. A positive closed boundary chain certifies completeness

Here is the precise geometric lemma needed by `COMMON_MINOR_POLYTOPE.md`.

**Boundary-chain lemma.** Let (P) be a full-dimensional convex polytope of dimension (d\geq2). Suppose a finite formal oriented ((d-1))-chain (C) is given by affine simplices whose vertices are vertices of (P). Assume:

1. Every simplex is contained in one of a specified collection of supporting facets of (P).
2. The formal boundary of (C) is zero.
3. Every nondegenerate simplex has positive orientation relative to the outward orientation of (\partial P), with positive coefficient, and at least one is nondegenerate.

Then the specified collection contains every facet of (P).

**Proof.** Refine the faces of (P), the images of the listed simplices, and their intersections into a common finite polyhedral complex on (\partial P), then triangulate that refinement. The affine chain pushes forward to a top-dimensional polyhedral chain on this refinement. A rank-deficient affine simplex contributes zero in top dimension. Boundary commutes with affine pushforward and subdivision, so the resulting top chain still has zero boundary.

Orient every top cell by the outward orientation of (P). Its integer multiplicity is nonnegative because every nondegenerate source simplex has that orientation. Across a shared codimension-one cell, boundary cancellation says that the two top-dimensional multiplicities agree. The adjacency graph of the top cells of a triangulated convex boundary is connected: radial projection from an interior point identifies the boundary with a sphere, and the top-dimensional cells of such a triangulation are connected through their codimension-one faces. Thus the multiplicity is constant on the boundary.

Some nondegenerate simplex contributes positive multiplicity on an open set, so the constant is positive. If a facet were omitted, an open subset of its relative interior would be disjoint from every listed simplex, and its multiplicity would be zero. This is impossible. (\square)

The chain need not be embedded, and the argument does not need the source complex to be a sphere. A formally closed oriented chain suffices. The positivity hypothesis is essential: a nontrivial source cycle may otherwise push forward with zero degree.

Degenerate simplices must remain in the *formal* boundary calculation. Deleting them before that calculation can create a nonzero boundary. Their vanishing top-dimensional contribution is justified only after pushing the complete closed chain forward. The root certificate follows this requirement.

### Independent arithmetic verification

The review verifier rebuilt all 24 augmented permutation vertices from the supplied 13 bitmask coordinates. Their exact rank is 14. It then checked every claimed supporting inequality against all vertices, checked rank 13 on each active set, and independently regenerated the symmetry orbit of the representative facet. The result is exactly:


| Family | Number of distinct facets |
|---|---:|
| Singleton nonnegativity | 16 |
| Two-minor nonnegativity after complementary identifications | 18 |
| Left-right permutation orbit of the nontrivial representative | 48 |
| Total | 82 |


For the stored boundary chain, the verifier recomputed **all 9,050 integer determinants** by fraction-free elimination, checking every exact division. It found 6,846 positive oriented nondegenerate simplices and 2,204 degenerate simplices. Every codimension-one formal face has two incidences with canceling signs. Every simplex belongs to a certified supporting facet. All 82 facets occur in the nondegenerate chain. These facts meet the boundary-chain lemma's hypotheses and prove completeness without relying on Qhull's completeness claim.

### What the polytope theorem means for actual unitaries

For (U\in U(4)), write

\[
R(U)_{I,J}=|\det U[I,J]|^2,\qquad |I|=|J|.
\]

The earlier exterior/Boolean representation places (R(U)) in the normalized real affine span of the permutation operators. The representation has dimension 14 before normalization and 13 after its trivial component is fixed. Equivalently, the common (GL_2) action and the permutation representation identify this span; the entries of (R(U)) are real, so complex coefficients in a linear representation may be replaced by their real parts. The exact rank calculation above independently confirms the affine dimension of the permutation profile space.

All singleton and two-minor nonnegativity inequalities hold automatically for (R(U)). Thus a common permutation law for all minors is equivalent to the 48 nontrivial inequalities. One representative is

\[
R_{3,3}+R_{2,4}+R_{12,13}-R_{13,23}\geq0.
\]

This is a theorem about the stronger *common-law* condition. Failure of a common-law facet does not itself give spectra violating scalar MOC: the permitted determinant support functionals form a special family.

## 2. Quaternion factorization and the remaining structural bridge

For (O=L(q)R(r)\in SO(4)), with (q,r\in S^3), define the chart coefficients

\[
a=-O_{43},\quad b=-\det O[23,24],\quad
c=-\det O[13,14],\quad d=O_{34}.
\]

The audited identities are

\[
\begin{aligned}
a+d&=2(q_0r_1-q_1r_0),&a-d&=2(q_2r_3+q_3r_2),\\
b+c&=2(q_0q_1-r_0r_1),&b-c&=2(q_2q_3+r_2r_3).
\end{aligned}
\]

The two-minor formulas use both unit-norm equations. For example, before normalization,

\[
b=(q_0q_1+q_2q_3)\|r\|^2+(-r_0r_1+r_2r_3)\|q\|^2.
\]

Factoring

\[
4(ab-cd)^2-(a^2+b^2-c^2-d^2)^2
\]

as the negative product of the four signed sums (a\pm b\pm c\pm d) gives exactly

\[
\Delta=-16\prod_{i=0}^3(q_i^2-r_i^2).
\]

Because the four differences sum to zero, a nonzero discriminant is positive for a one-versus-three sign split and negative for a two-versus-two split. This interpretation is exact. It does not allow the quaternion coordinates to be rotated arbitrarily: only the finite transformations coming from permitted monomial changes are relevant.

### A finite linear arrangement, rather than unrestricted quaternion rotations

For a column permutation (\Pi), let (W=\Pi\operatorname{diag}(\det\Pi,1,1,1)\in SO(4)). The added diagonal sign is absorbed in the phase variables. Write (W=L(a)R(b)). Then

\[
OW=L(qa)R(br),\qquad q'=R(a)q,\quad r'=L(b)r.
\]

Thus every factor (q'_i\pm r'_i) is a real linear form in the eight original coordinates. The region where all 24 chart discriminants are strictly negative is a union of chambers of a finite hyperplane arrangement, restricted to the two unit spheres. This observation turns a collection of degree-eight signs into finite chamber data. The categorical track now owns the exact spin enumeration and chamber analysis; no root-system identification is asserted here.

The desired disjunction remains

\[
\text{common minor law}\quad\text{or}\quad
\operatorname{rank}(O-M)\leq2\text{ for some monomial unitary }M.
\]

In quaternion coordinates one would need to show that a negative common-law facet forces an admissible chart with nonnegative discriminant. A torus zero must also give a regular Schur solution, or be obtained as a limit of regular completions. The set of actual monomial rank-two completions is closed, since the phase torus is compact; consequently a density-plus-closure argument would suffice for singular limits. The singular-chart density and closure argument is now proved in `categorical_global_completion_criterion.md`; the structural disjunction itself remains unproved. Even a proof of the disjunction would still require the scalar rank-two MOC inequality.

## 3. Defect-one deletion and the exact scalar disk criterion

The categorical Schur deletion is a fixed-input matrix element, not an ordinary partial trace. If

\[
U=\begin{pmatrix}\alpha&r\\c&D\end{pmatrix},
\]

then the (E_{00}) input deletion produces the graded squared-minor kernel (K(D)). The remaining contraction satisfies 

\[
I-D^*D\succeq0,\qquad \operatorname{rank}(I-D^*D)\leq1.
\]

Conversely every such contraction has a one-dimensional unitary completion. Its polar form is (D=D_0+zxy^*), where (D_0) is a partial isometry from (y^\perp) onto (x^\perp), and (|z|\leq1).

After deletion, the comparison vertices are both

\[
Z_\sigma=\prod_i(a_i+b_{\sigma(i)})
\]

and the decorated values

\[
Z_{\sigma,j}^{\rm del}=a_j\prod_{i\ne j}(a_i+b_{\sigma(i)}).
\]

There are ((m+1)!) labels before coincidences, corresponding exactly to ordinary permutations in the completed system. The common projective normalization and multilinear homogeneity in the categorical note therefore give an equivalence between this scalar defect-one hull problem in size (m) and MOC in size (m+1). It is an exact reformulation, not an induction that has already removed the difficult case.

### Every two-by-two contraction has a partial permutation law

Let (p_{ij}=|D_{ij}|^2), (t=|\det D|^2), and assume (\|D\|\leq1). Choose

\[
\max(0,t-p_{12},t-p_{21})\leq x\leq\min(t,p_{11},p_{22}).
\]

The interval is nonempty. Indeed, each row and column squared norm is at least the smaller eigenvalue of (D^*D), and that eigenvalue is at least their product (t), because the larger eigenvalue is at most one. These are precisely the four cross-inequalities needed for the displayed interval.

Give the two full permutations weights (x,t-x), the four singleton matchings weights

\[
p_{11}-x,\ p_{22}-x,\ p_{12}-t+x,\ p_{21}-t+x,
\]

and the empty matching weight

\[
1-\sum_{ij}p_{ij}+t=\det(I-D^*D)\geq0.
\]

These weights sum to one and reproduce every minor. For a defect-one contraction the empty weight vanishes. This proves the smallest deletion case by an explicit law.


### The scalar disk is an exact two-by-two matrix problem

Every minor of (D_0+zxy^*) is affine in (z). Therefore the real support is

\[
f(z)=c+2\Re(bz)+q|z|^2.
\]

For any proposed height (h), the disk bound (f(z)\leq h) is equivalent to the existence of (\lambda\geq0) such that

\[
\begin{pmatrix}h-c-\lambda&-b\\-\bar b&\lambda-q\end{pmatrix}\succeq0.
\]

This follows either by completing the square or by maximizing the scalar quadratic. If (q<0) and (|b|\leq-q), the interior maximum is (c+|b|^2/(-q)). Otherwise the maximum is on the circle and equals (c+q+2|b|). These two cases give the matrix certificate explicitly.
## 5. Rank-two phase tori: a global criterion with exact hypotheses

Let (u,v) be orthonormal complex vectors and

\[
G(\theta_1,\theta_2)=I+(e^{i\theta_1}-1)uu^*+(e^{i\theta_2}-1)vv^*.
\]

For any fixed matrices in the determinant support problem, the real objective (f) has Fourier degree at most one separately in each phase. This follows from the bordered determinant identity for a single phase; its polynomial form avoids assumptions about an invertible complementary block.

Assume only (f_1(0,0)=f_2(0,0)=0). With (x=\tan(\theta_1/2)), (y=\tan(\theta_2/2)), the exact identity is

\[
f-f_0=\frac{(x,y,xy)\,\mathcal M\,(x,y,xy)^T}{(1+x^2)(1+y^2)},
\]

where

\[
\mathcal M=
\begin{pmatrix}
2f_{11}&2f_{12}&2f_{112}\\
2f_{12}&2f_{22}&2f_{122}\\
2f_{112}&2f_{122}&f(\pi,\pi)-f_0
\end{pmatrix}.
\]

The factors of two and the third-derivative entries check directly against the six stationary Fourier coefficients. The projective directions ([x:y:xy]) are dense in (\mathbb{RP}^2): if (abc\ne0), take (x=c/b,y=c/a). Therefore

\[
f\leq f_0\text{ on the entire phase torus}
\quad\Longleftrightarrow\quad\mathcal M\preceq0.
\]

A positive direction of the matrix gives actual improving phases by the same rational formulas, after an arbitrarily small perturbation if a coordinate vanishes. This is an exact global equivalence, not an SOS relaxation.

For a complete real rank-two circle, stationarity similarly leaves

\[
g-g_0=\frac{t^2}{(1+t^2)^2}
\left(2g''+\frac43g'''t+(g(\pi)-g_0)t^2\right).
\]

Hence a two-by-two negative-semidefinite matrix characterizes whole-circle nonascent. Negative initial curvature by itself gives neither of these global conclusions.

The exact determinant Hessian in `continuous_so4_variational_geometry.md` follows by differentiating (\det(Ae^{tK}+e^{tK}B)). Transposition of complex symmetric (A,B) gives (f(U)=f(\bar U)), so vanishing of the six real skew first derivatives implies full unitary stationarity at a real base. Imaginary diagonal directions lie in the stationary Hessian kernel by the left diagonal phase invariance.

In (\mathfrak{so}(4)), write (k=(k_{12},k_{13},k_{14},k_{23},k_{24},k_{34})). The real rank-two cone is

\[
\operatorname{Pf}(K)=k_{12}k_{34}-k_{13}k_{24}+k_{14}k_{23}=0.
\]

Let (J) satisfy (k^TJk=2\operatorname{Pf}(K)), (J^2=I). A zero-trace orthogonal-basis decomposition proves the exact convex hull identity for density matrices with (\operatorname{tr}(JX)=0). A supporting-line argument then gives

\[
H(k,k)\leq0\text{ on that cone}
\quad\Longleftrightarrow\quad H-\lambda J\preceq0\text{ for some real }\lambda.
\]

### Generic imaginary diagonal completion

The continuous note's completion criterion also checks. For real skew (K) with all six upper edges nonzero, a real diagonal (D) with (\operatorname{rank}(iK+D)\leq2) exists exactly when

\[
\operatorname{Pf}(K)\prod_{i<j}k_{ij}\leq0.
\]

For edges ((x,y,z,w,v,t)), an invertible (12) principal block reduces the equations to

\[
d_1d_2=x\operatorname{Pf}(K)/t,
\qquad yz\,d_2+wv\,d_1=0.
\]

Thus (d_1^2=-xyz\operatorname{Pf}(K)/(twv)), which gives the sign condition. Necessity at a putative completion is justified by the existence of a nonsingular principal two-by-two minor of a rank-two Hermitian matrix. Rank one is impossible because each nonzero triangle product is purely imaginary, whereas a Hermitian rank-one triangle product is real. Relabeling does not change the product sign: each of its two factors changes by the permutation sign. In the strict case, the three candidate Schur denominators cannot all vanish. 

Every (SO(4)) matrix does have a product of two commuting rank-two complex phase updates, modulo a scalar phase. The associated rank-two projections have rank-one intersection and a three-dimensional union. This is not the preceding two-rank-one-axis torus. A scalar proof cannot iterate a theorem requiring a commuting base after the first factor without an additional composition argument.

## 7. The 54-variable support cone and its exact scope

For a fixed normalized CH spectrum (\beta), rows (r,v,s,t) of (U(4)), and a complex support direction, column phases make (v) real. The support becomes

\[
r^*M(v)r+s^*L(v)s
\]

on (H=v^\perp), where (M,L) are the real parts of reciprocal complex symmetric pencils. The other three rows may remain complex. Real symmetric PSD bounds apply to their complexification, so no unjustified realification is used.

A shared correction (Y\succeq0) gives a valid bound when

\[
Y+\alpha I\succeq M,\quad Y+\gamma I\succeq L,
\quad\operatorname{tr}Y+\alpha+\gamma\leq h.
\]

The exact 54-variable model uses a real completely positive quadratic map before compression by (P=I-vv^T), quadratic scalar multipliers, and bilinear sum-of-squares slacks modulo (r^Tv=0). Averaging over coordinate signs splits its covariance into a three-by-three diagonal block and six two-by-two pair blocks. The two slacks each contribute six pair Grams and one three-by-three restricted Gram.

For the trace budget, with (p_i=v_i^2), the exact residual is (p^TBp). In order four, copositivity is equivalent to a PSD matrix plus an entrywise nonnegative matrix. This is a genuine exact step at dimension four; it is not available in arbitrary dimension. A primary source explicitly restating the theorem is Dickinson, Dür, Gijben and Hildebrand, *Irreducible elements of the copositive cone*, Section 1, which attributes the result to Diananda: <https://optimization-online.org/wp-content/uploads/2012/03/3383.pdf>.

The model has 54 real variables and 32 PSD blocks when the ten scalar nonnegativity constraints are counted as one-by-one blocks. It is complete for the stated quadratic CP/bilinear SOS class. This does **not** assert that every nonnegative biquadratic form admits the selected SOS representation, or that every scalar MOC inequality belongs to this certificate class.

The fixed-chart quantifier is also necessary. All facets for one fixed (\beta) would prove that CH inclusion. Normalizing arbitrary original first spectra changes the second spectrum by a projective transformation. Thus this statement does not automatically keep an original (B) fixed while proving all original (A).

### An exact positive complex facet certificate

For

\[
\beta=(-4+4i,2i,-1-2i,1-3i),\quad
\lambda_0=287+91i,\quad\lambda_1=772+2546i,
\]

the actual permutation height is (h=11100). The provided integer parameters reconstruct all 32 PSD blocks exactly. Our independent verifier rebuilt those blocks from the defining formulas and checked all principal minors. The nonnegative budget is

\[
21p_1p_3+1501p_1p_4+1363p_2p_3+415p_2p_4+8p_3p_4+1526p_4^2.
\]

This proves a genuine complex support inequality for every complex \(U(4)\).

For spectral clipping: for (Y) with eigenvalues (\mu_1\geq\mu_2\geq\cdots\geq0), replace it by

\[
\widehat Y=(\mu_1-\mu_2)u_1u_1^*,\quad
\widehat\alpha=\alpha+\mu_2,\quad
\widehat\gamma=\gamma+\mu_2.
\]

Then (\widehat Y+\mu_2I-Y\succeq0), and the new cost is (\mu_1+\mu_2+\alpha+\gamma\), no larger than the old one. This works in every anchor dimension at the level of the semidefinite dual. The resulting rank-one vector depends on the anchor and is not required to equal (PKv) for one fixed matrix (K).

### Equality and local stability of this single support instance

The first diagonal slack Gram is positive definite. Its equality conditions and pair supports give two continuous (U(2)) branches, (3124\)–(3214) and (3214\)–(3241), together with the phased permutation (4321). The branches meet at (3214). The author correctly places both in the larger solved (U(3)) family (r=e_3) for the neighborhood argument, instead of incorrectly demanding strict normal curvature relative to each small branch at their intersection.

The first slack controls (1-|r_3|^2) uniformly near the branches. Near (4321), the two slacks together control distance to the phased permutation. Each squared minor has zero transverse first derivative on a block family, for every spectral parameter. The negative transverse Hessians therefore persist under perturbation. On the block family, the inequality follows from its common law in dimension at most three. A compact tubular cover and a positive gap on the complement yield an open neighborhood of this *single spectral support instance*. It does not certify all directions for a nearby spectrum.

## 8. New result: compact certificates bounded by permutation support spread

Write the universal affine block map as

\[
\mathcal A_\xi(z)=C(\xi)+\mathcal L(z),\qquad z\in\mathbb R^{54},
\]

where (\xi) comprises the spectral coefficients and support height, and (\mathcal L) is independent of (\xi). Let (\mathcal K) be the product cone of its 32 PSD blocks.

The dual track found a universal rational (Z_0\in\operatorname{int}\mathcal K), orthogonal to every direction of (\mathcal L). Its weights are

\[
\begin{array}{c|c}
\text{block}&\text{weight}\\\hline
R_0&4(I_3+J_3)\\
\text{each pair block}&\begin{pmatrix}5&-1\\-1&5\end{pmatrix}\\
\text{each restricted diagonal slack}&4I_3-J_3\\
T&6I_4+3J_4\\
\text{scalar budget diagonal/off-diagonal}&9\,/\,6
\end{array}
\]

Every matrix weight has smallest eigenvalue at least one. The independent verifier checked its annihilation of all 54 coordinate directions.

**Support-spread identity.** If

\[
\overline h=\frac1{24}\sum_\pi
\Re(\lambda_0w_{\pi,0}+\lambda_1w_{\pi,1}),
\]

then

\[
\langle Z_0,C(\xi)\rangle=72(h-\overline h).
\]

**Proof.** For (v) uniform on the real unit sphere in dimension four and (r) uniform on the unit sphere of (v^\perp), the moments are

\[
\mathbb E(r_i^2v_j^2)=5/72\ (i\ne j),\quad
\mathbb E(r_iv_jr_jv_i)=-1/72,\quad
\mathbb E(r_i^2v_i^2)=3/72.
\]

Also (\mathbb E(v_i^4)=9/72) and (\mathbb E(v_i^2v_j^2)=3/72) for (i\ne j). These follow by conditioning (\mathbb E(rr^T\mid v)=(I-vv^T)/3) and the elementary fourth moments of a uniform sphere vector. Applying these moments to the two slack Gram expansions and the trace budget gives precisely the displayed weights, multiplied by 72. Every correction and scalar-multiplier term cancels.

For the pencil (T_\delta(v)), direct trace expansion gives

\[
\mathbb E_v\operatorname{tr}_{v^\perp}T_\delta(v)
=\frac{3e_1(\delta)+2e_2(\delta)}4.
\]

Conditional averaging over (r\in v^\perp) divides that trace by three. Consequently the first pencil has mean (e_1(\beta)/4+e_2(\beta)/6); the reciprocal pencil has mean (e_3(\beta)/4+e_2(\beta)/6). These are exactly the two uniform permutation means in the CH comparison points. The constant left after cancellation is (72(h-\overline h)). (\square)

**Compactness theorem.** Every feasible 54-parameter certificate obeys

\[
\sum_{b=1}^{32}\operatorname{tr}\mathcal A_\xi(z)_b
\leq72(h-\overline h).
\]

Moreover, the entire feasible set of parameters (z) is compact.

**Proof.** The trace inequality follows by pairing each PSD block with a weight at least the identity. The affine block map is injective: (R_0) is a block; the twelve directed correction variances and six covariances are entries of the six correction blocks; the twelve pair slack variables are their respective off-diagonal entries; (T) is a block. The remaining scalar coefficients (c_j,d_j) are recovered from any applicable pair diagonal after subtracting its already known correction and spectral terms.

A PSD matrix with bounded trace has every entry bounded. Hence all displayed parameters are bounded. More explicitly, if (C_*=72(h-\overline h)), each direct covariance, Gram, or (T) entry has absolute value at most (C_*). For example,

\[
c_j=D^M_{ij}+u_i+q_{ij}-x_{ij}\quad(i\ne j)
\]

gives (|c_j|\leq C_*+|u_i+q_{ij}|), since both nonnegative diagonal entries (D^M_{ij},x_{ij}) lie in ([0,C_*]). The same applies to (d_j). The feasible set is closed by the PSD constraints, and is therefore compact. (\square)

For the exact facet above, the mean is (-11259/2), so (C_*=1204524). The actual sum of traces in its integer certificate is 263949. These values were independently recomputed from the 24 support values and the 32 blocks.

### Consequences for a future universal proof

First, certificates cannot disappear solely by escaping to infinity as bounded spectral/support parameters converge. If each nearby parameter has a certificate, the common trace bound and the explicit coefficient bounds produce a convergent subsequence, yielding a certificate at the limit. Thus the parameter domain of this certificate class is closed on every finite spectral chart. Its failure set is open.

Second, there is no weak infeasibility. If points of the affine image approach the product PSD cone, nearby PSD points have bounded pairing with (Z_0), hence bounded norm. A limit lies in both the cone and the closed affine image. If the system is infeasible, it therefore admits a strict separating dual vector. For rational data that separator can be made rational: add a small positive rational multiple of (Z_0), then approximate within the rational annihilator subspace while preserving strict positivity and negative constant pairing.

This does not imply every feasible rational instance has a rational primal certificate, and it does not prove universal feasibility. It supplies a concrete alternative for a rational facet: an exact certificate in this class, or a rational strict countercertificate to the class. The remaining MOC problem is to show that the second alternative never occurs for the reciprocal spectral coefficients, or to discover which additional valid structures a failed class would need.


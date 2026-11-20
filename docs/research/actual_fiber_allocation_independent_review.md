## 2. Legal allocation polytope and coupled completion — VALID

The residual-change matrix has the correct signs.

Let
\[
t_1=\alpha_{12}+\alpha_{34},\quad
t_2=\alpha_{13}+\alpha_{24},\quad
t_3=\alpha_{14}+\alpha_{23}.
\]
Special extraction replaces the double-gap contribution by
\[
d'=d-4(t_1,t_2,t_3).
\]
Applying
\[
r=\tfrac12(d_1+d_2-d_3,\ d_1+d_3-d_2,\ d_2+d_3-d_1)
\]
gives exactly the displayed columns of \(C\). In particular, edges \(12,34\) change the residual by \(2\alpha_e(-1,-1,+1)\), not its negative.

The construction uses
\[
u=\ell(2\alpha-w),
\]
and compensates its quartic effect by
\[
Q=D-2\sum_j u_jL_j.
\]
This is the correct adjugate identity compensation. The same \(u\), and one raw cubic block
\[
B=B_0+\sum_{j=1}^{8}k_jK_j,
\]
define the entire matrix. Consequently, the \(9\)- and \(10\)-dimensional parity blocks are not being completed with independently chosen parameters.

The legal conditions are precisely the stated extraction restrictions:
\[
0\le\alpha\le w,\qquad r+C\alpha\ge0.
\]
Their use as restrictions of a sufficient selector family is legitimate; no necessity claim for the original support inequality follows.

**References:** `organized/research/actual_fiber_allocation/exact_seed.py:9-16`, `organized/research/actual_fiber_allocation/exact_seed.py:26-36`; `organized/research/actual_fiber_allocation/RESULT.md:6-17`.

## 3. Actual-spectral interpolation — VALID

The interpolation argument genuinely stays on actual spectra.

With the other eigenvalues and \(\eta\) fixed, every product
\[
\operatorname{Re}\!\left(\eta\prod_j(a_j+b_{\sigma(j)})\right)
\]
is real-affine in the remaining complex eigenvalue. The same is true of every compound cost. Therefore the contact height, comparison gaps, capacities, residuals and raw canonical Gram blocks interpolate with the **same** barycentric weights.

Interpolating \(\alpha\) and the eight **raw** cubic gauges then yields
\[
X=\sum_v\lambda_vX_v\succeq0.
\]
The capacity and residual inequalities are preserved as well.

The common-contact hypothesis is essential: interpolation of maxima with changing contact permutations would not justify this formula. The report states that hypothesis correctly.

The product-polytope extension is also sound through separate affineness and product barycentric weights. It is not a claim that arbitrary convex combinations of attainable 13-coordinate profiles are themselves attainable.

**References:** `organized/research/ACTUAL_FIBER_ALLOCATION.md:29-40`; `organized/research/actual_fiber_allocation/RESULT.md:19-24`.

## 4. The hexagon is the entire stated contact fiber — VALID

Independent expansion gives the stated identity height:
\[
h=\frac{153}{50}+6x-27y.
\]

The six displayed integer inequalities correspond to original comparison indices \(8,9,10,14,16,22\). More precisely, if \(L_i\) denotes a displayed primitive integer facet expression, the original gaps are
\[
\left(\frac3{25}L_1,\frac1{50}L_2,\frac1{100}L_3,
      \frac3{50}L_4,\frac1{50}L_5,\frac1{50}L_6\right).
\]
All scales are positive.

I checked every stored redundancy identity, including nonnegativity of its constant and multipliers. Thus the six inequalities imply all original 24 comparisons. Conversely, they are positive rescalings of six original comparisons, so the original contact region implies these inequalities. This proves equality of the regions.

Independent feasible pair-intersection enumeration returns exactly the six listed vertices. Boundedness has a short additional certificate. For the displayed normals,
\[
\frac{180}{277}n_1+\frac{29}{277}n_2+n_4=0,
\]
with strictly positive coefficients, and these normals span \(\mathbb R^2\). A recession direction satisfying \(n_i\cdot v\ge0\) must therefore be orthogonal to all three, hence must vanish.

This independently confirms boundedness without relying on the verifier’s boundary-ray enumeration. The six edges have the claimed pairs of endpoints.

**References:** `organized/research/actual_fiber_allocation/verify_polygon.py:5-35`; `organized/research/actual_fiber_allocation/polygon_verification.json:5-448`; `organized/research/actual_fiber_allocation/RESULT.md:26-50`.

### Minor presentation issue: redundancy multiplier normalization

The JSON’s multipliers act on the **unscaled original gap facets**, whereas the immediately displayed facet array contains primitive integer halfplanes. Applying those multipliers directly to the integer array would generally give the wrong identity.

This is not a mathematical failure: the verifier reconstructs and uses the correct raw facets. For a self-describing certificate, record the six scales above, or multiply each stored multiplier by its facet scale.

**References:** `organized/research/actual_fiber_allocation/verify_polygon.py:8`, `organized/research/actual_fiber_allocation/verify_polygon.py:24-26`, `organized/research/actual_fiber_allocation/verify_polygon.py:60-63`; `organized/research/actual_fiber_allocation/polygon_verification.json:13-72`.

## 5. Rank-17 full-Gram certificates and coefficient coverage — VALID

All six payloads passed independent checks of:

- the fixed spectral entries and actual vertex location;
- all original comparison gaps;
- every allocation capacity and residual inequality;
- reconstruction of the full Gram using the supplied raw gauges;
- symmetry, \(XK=0\), and nonsingularity of the deleted \(2\times2\) kernel submatrix;
- exact positive LDL reconstruction of the retained \(17\times17\) principal matrix.

The last two conditions really prove positivity of the **whole** matrix.

For any vector \(v\), choose \(\beta\) so that \(v-K\beta\) vanishes in the deleted coordinates. This is possible because the corresponding kernel submatrix is invertible. Then
\[
v^TXv=(v-K\beta)^TX(v-K\beta)\ge0
\]
by positivity of the retained principal matrix. Its rank is at least 17; the two independent kernel columns make it at most 17. Hence the full rank is exactly 17.

I regenerated the polynomial products independently and obtained exactly 838 monomial positions. Every coefficient residual vanished for all six vertex Grams and the seed. The sparse accumulation in `complete()` is sound: positions omitted from its residual dictionary have no nonzero contribution.

The fiber-wide triangle and Segre/discriminant checks are useful additional consistency checks. They are not being substituted for actual spectral reconstruction.

**References:** `organized/research/actual_fiber_allocation/verify_polygon.py:36-58`; `organized/research/actual_fiber_allocation/exact_seed.py:34-42`.

Combining these certificates with actual-spectral interpolation proves the entire closed hexagon, including its edges and vertices.

## 6. Rational quadratic sufficient criterion — VALID

The 13 profile directions and 14 allocation/gauge directions describe the intended family. The verifier checks every one of the 70 compound directions, not merely selected basis rows. It also solves for the difference between the representative cubic block and the raw block in the span of exactly the eight allowed gauges.

This prevents an unnoticed enlargement to arbitrary cubic completions.

**References:** `organized/research/actual_fiber_allocation/verify_criterion.py:12-38`.

The seed’s two positive LDL blocks, their complete coordinate partition and zero cross-block establish \(X_*>0\). I independently confirmed the strict margins
\[
\min\alpha_e=\frac1{100},\qquad
\min(w_e-\alpha_e)=\frac1{25},\qquad
\min(r+C\alpha)=\frac{23}{200},
\]
and minimum nonidentity comparison gap \(87/50\).

For symmetric matrices,
\[
\langle P,Q\rangle_W=\operatorname{tr}(WPWQ)
\]
is the Frobenius inner product after congruence by \(W^{1/2}\). Since the 14 directions are independent, their metric Gram \(H\) is positive definite. The verified orthogonality equations therefore uniquely identify
\[
T=-H^{-1}N.
\]
Thus \(T\) minimizes the relative Frobenius residual over the 14 **unconstrained** parameter adjustments. It need not minimize over legal allocations; legality is separately tested.

The construction gives
\[
X=\rho X_*+\Delta,\qquad
\|X_*^{-1/2}\Delta X_*^{-1/2}\|_F^2
=\delta^TC_{\rm quad}\delta.
\]
For \(\rho>0\), the stated bound implies
\[
\rho I+X_*^{-1/2}\Delta X_*^{-1/2}\succeq0,
\]
because operator norm is bounded by Frobenius norm. Congruence proves positivity of the full coupled \(19\times19\) matrix. Equality is allowed and gives PSD, not necessarily PD.

**References:** `organized/research/actual_fiber_allocation/verify_criterion.py:4-11`, `organized/research/actual_fiber_allocation/verify_criterion.py:39-45`; `organized/research/actual_fiber_allocation/RESULT.md:65-87`.

The 24 allocation-response entries involving odd coordinates are indeed nonzero. That proves genuine dependence on the chosen odd profile coordinates, not universal success of the resulting section.


## 8. Dual equivalence and exclusion of weak infeasibility — VALID

The compactness argument is correct and sufficiently specific to this family.

Fix \(z\). For bounded-distance pairs \(X(\alpha,k),Z\succeq0\):

1. Compactness bounds \(\alpha\).
2. Gauge directions have zero diagonal, so \(\operatorname{diag}X\) is bounded.
3. Bounded distance bounds \(\operatorname{diag}Z\).
4. PSD gives \(|Z_{ij}|^2\le Z_{ii}Z_{jj}\), bounding all entries of \(Z\).
5. Hence \(X\) is bounded.
6. Independence of the eight gauge directions then bounds \(k\).

A minimizing sequence has a convergent subsequence. Thus disjointness implies an attained, strictly positive distance, not weak infeasibility.

At a nearest pair, the difference supplies a strict PSD separator annihilating every unrestricted gauge direction. Its support over the allocation family is exactly
\[
\langle Y,F(z)\rangle+
\max_{\alpha\in P(z)}
\sum_e\alpha_e\langle Y,A_e\rangle.
\]
Conversely, a negative value excludes every PSD member. The displayed dual equivalence follows without invoking generic SDP strong duality.

**References:** `organized/research/actual_fiber_allocation/RESULT.md:93-105`; `organized/research/ACTUAL_FIBER_ALLOCATION.md:127-140`.

### Recommended proof clarification: explicitly establish \(P(z)\neq\varnothing\)

The nearest-pair presentation implicitly uses nonemptiness. For actual supported data it follows from the existing inverse-four-cycle reserve identities.

At most one component of \(r\) is negative, since pairwise sums are the nonnegative double gaps. If \(r_1<0\), the reserve identity gives
\[
w_{14}+w_{23}\ge-r_1/2.
\]
Allocate total \(-r_1/2\) across those two capacities. The new residuals are \(0,d_1,d_2\), all nonnegative. The other cases are analogous.

Adding this argument would make the dual statement self-contained; it does not require a new hypothesis.

**References:** `organized/research/actual_fiber_allocation/RESULT.md:99-105`; `organized/research/verify_reflection_average_sos.py:56-60`.

Finally, the proposed multiplier signs are correct:
\[
b=\mu-\nu-C^T\xi
\]
implies
\[
b\cdot\alpha
\le\mu\cdot w+\xi\cdot r
\]
for legal \(\alpha\) and nonnegative multipliers. A strict negative upper bound would therefore exclude every allocation in the family.

**Reference:** `organized/research/actual_fiber_allocation/RESULT.md:107-112`.

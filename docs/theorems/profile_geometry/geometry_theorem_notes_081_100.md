## Coefficient and scalar-theorem conventions

The three-value scalar theorem cited as Round 083 below is retained with its complete hypotheses and proof in [Scalar rank-two compression with at most three spectral values on one side](geometry_three_value_scalar_theorem.md).

For the coefficient-hull (CH) statements, let β∈C⁴ and C=O diag(β)O^T for the specified real orthogonal O. Write C[I] for its principal submatrix on I, and define D_0=det C[124]+det C[14] and D_1=C_{11}+det C[12]. A permutation written π(1)π(2)π(3)π(4) has CH coordinates D_{0,π}=β_{π(1)}(1+β_{π(2)})β_{π(4)} and D_{1,π}=β_{π(1)}(1+β_{π(2)}). Real target coordinates are ordered (Re D_0, Im D_0, Re D_1, Im D_1). Here a weighted CH law means nonnegative permutation weights summing to one, with CH average (D_0,D_1) and anchor marginal Pr(π(2)=j)=O_{2j}². The coefficient definitions are retained in [the coefficient-hull formulation](verified_results.md#the-coefficient-hull-equivalent-to-moc-in-dimension-four); the anchor marginal and real-coordinate ordering are also explicit in the original exact verifier cited below.

## Round 086 — The new scalar theorem includes neither-normal, nontriangular pairs

**Mechanism.** Take the real coisometry with columns

\[
 x_1=e_1/\sqrt2,\quad x_2=e_2/\sqrt2,\quad
 x_3=(1,1)^T/2,\quad x_4=(-1,1)^T/2.
\]

For a=(0,1,0,i),

\[
 A=\begin{pmatrix}i/4&-i/4\\-i/4&1/2+i/4\end{pmatrix}.
\]

Use the same frame with b=(1,2,1,1−i), giving B=A*+I. Both spectra have
three distinct values, while A and B are nonnormal. Directly,

\[
 [A,B]=\begin{pmatrix}0&-i/4\\i/4&0\end{pmatrix},
 \qquad \det[A,B]=-1/16\ne0.
\]

Thus the pair has no common eigenvector. Nevertheless A+B=diag(1,2),
and Round 083 proves the matching-hull inclusion for its determinant 2.

**Status: exact example.** The three-value theorem adds a class not
contained in either the normal-summand or simultaneous triangular class.

## Round 087 — Every fixed-row anchor carries two genuine 2×3 coisometries

**Mechanism.** Let O be real orthogonal, fix its second row v, and choose
an anchor column j with |v_j|<1. Let

\[
 K_j=\operatorname{span}(v,e_j)^\perp,
 \quad d_j=1-v_j^2,
 \quad w_j=(e_j-v_jv)/\sqrt{d_j}.
\]

Project the other three rows of O onto K_j to obtain one two-row,
three-column coisometry. Project the three coordinate vectors e_k,
k≠j, onto K_j to obtain another. Each coisometry identity follows by
projecting a resolution of the identity; the omitted row v and omitted
coordinate e_j have zero projection.

The left omitted-label probabilities are O_{ij}²/d_j, i≠2. The right
omitted-label probabilities are v_k²/d_j, k≠j. These follow from
completing each projected two-row frame to its corresponding
three-dimensional orthonormal basis.

**Status: proved.** The new (3,3) common law applies exactly on every
nondegenerate anchor plane. No approximate compression or invented
coisometry is used.

## Round 088 — The anchor-plane mixed coefficients retain a precise star interference

**Mechanism.** Relabel the anchor block as

\[
 O=\begin{pmatrix}u&r\\c&V\end{pmatrix},\qquad d=1-u^2.
\]

The inner-product matrix of the two projected frames is
Z=V+u cr/d. Its row and column squared norms are 1−c_i²/d and
1−r_k²/d. Therefore their mixed determinant probabilities are

\[
 F^{(j)}_{ik}
 =(1-c_i^2/d)(1-r_k^2/d)-Z_{ik}^2.
\]

Writing the anchored two-minor q_{ik}=(uV_{ik}−c_ir_k)² gives the equivalent
formula

\[
 \boxed{F^{(j)}_{ik}
 =\frac{d-V_{ik}^2-c_i^2-r_k^2+q_{ik}}{d}.}
\]

It follows by expanding the square; no phases or signs are discarded in
the real case. The nonnegativity is guaranteed by the projected-frame
interpretation.

**Status: proved.** This makes the conditional problem computable directly
from the actual singleton and anchored-minor data.

## Round 089 — Completing the conditional matching exposes an omitted-pair transport

**Mechanism.** A size-two matching between three left and three right labels
can be completed to a unique three-permutation by matching the two omitted
labels. Let J^{(j)} be the joint distribution of those omitted labels.
The completed permutation's one-entry marginal is

\[
 W^{(j)}=F^{(j)}+J^{(j)}.
\]

Its row and column sums equal one. J has prescribed omitted-label
marginals, but it is coupled to F through the common matching law; an
arbitrary transportation plan with those marginals need not be attainable.

For three parent spectra α and β, the expectation of the completed
three-product depends only on W:

\[
 \prod_i\alpha_i+\prod_k\beta_k+
 \sum_{i,k}\bigl(\alpha_{i^c}\beta_k+
                   \alpha_i\beta_{k^c}\bigr)W_{ik}.
\]

Here α_{i^c} and β_{k^c} are the products of the other two entries. Thus the
known F leaves a genuine omitted-pair coupling in the scalar three-product.

**Status: exact reduction.** Applying the two-dimensional common law alone
does not determine the needed rank-three product.

## Round 090 — All polar-phase completions form an explicit conditional zonotope

**Mechanism.** In the anchor notation, Z is an isometry between the two
two-dimensional complements. Therefore

\[
 Q_j(\theta)=Z+e^{i\theta}cr/d
\]

is a 3×3 unitary completion. Its squared entries depend only on
t_j=cos θ∈[−1,1]:

\[
 |Q_j(\theta)_{ik}|^2
 =Z_{ik}^2+c_i^2r_k^2/d^2+2t_j Z_{ik}c_ir_k/d.
\]

For fixed complex β, averaging its conditional CH coordinates with weights
v_j² gives a point c+Σ_j t_j g_j in a four-generator zonotope in R⁴.
All centers and generators are explicit spectral polynomials times real
anchor coefficients. A candidate target can therefore be checked by a
four-variable bounded linear system.

**Status: exact description of this proposed family.** It is a particular
conditional construction, not the full weighted coefficient hull.


## Round 092 — An eight-permutation common-minor law

**Setup.** The specific real orthogonal matrix is

\[
 O=\tfrac12\begin{pmatrix}
 1&1&-1&-1\\
 1&1&1&1\\
 1&-1&1&-1\\
 1&-1&-1&1
 \end{pmatrix}.
\]

This is the matrix specified in original Round 091. No restriction on β is needed for the common-minor law below.

**Mechanism.** For this O, the following eight permutations, each with
weight 1/8, reproduce every singleton and two-minor probability:

\[
 1324,\ 1432,\ 2341,\ 2413,\
 3142,\ 3214,\ 4123,\ 4231.
\]

Every singleton occurs twice. Direct determinant arithmetic shows each
nonzero two-minor square equals 1/4 and occurs in exactly two of the
eight permutations; zero two-minors occur in none. Complementary minors
then give the complete profile.

Condition on the anchor assignment π(2)=j. Exactly two permutations remain,
with conditional weights 1/2. Delete one of their three other edges uniformly.
The resulting size-two matching has mixed matrix (2/3)W^{(j)}, which agrees
exactly with Round 088: its entries are either 0 or 1/3.

**Result.** The eight-permutation law has exact rational checks of all moments and all four conditional incidence matrices, and is valid for every β for this O.


## Round 094 — A positive weighted CH law and its open neighborhood

**Setup.** Take β=(0,1,i,2) and O=L/153, where

\[
 L=\begin{pmatrix}
 -29&96&106&46\\
 96&99&-66&6\\
 106&-66&61&64\\
 46&6&64&-131
 \end{pmatrix}.
\]

Its fixed second row is v=(96,99,−66,6)/153. With the CH definitions above, the actual target is

\[
 (\operatorname{Re}D_0,\operatorname{Im}D_0,
   \operatorname{Re}D_1,\operatorname{Im}D_1)
 =(1568/2601,\ 47968/23409,\ 14800/23409,\ 24488/23409).
\]

These matrix, spectrum and target data are exactly those specified in original Round 093; no conditional reconstruction constraints are imposed here.

**Mechanism.** This target has the following actual weighted permutation
law. The common denominator is 70227:

| Permutation | Numerator |
|---|---:|
| 1324 | 8480 |
| 2314 | 3252 |
| 3124 | 9732 |
| 3214 | 28742 |
| 3412 | 108 |
| 4132 | 17916 |
| 4213 | 661 |
| 4321 | 1336 |

The numerators sum to 70227. Their row-two marginal is exactly
(96²,99²,66²,6²)/153², and their CH average equals the explicit target above.
These are exact rational identities.

The positive law persists on an open neighborhood. The eight selected weighted-CH columns form a nonsingular 8×8 constraint matrix, and every displayed weight is positive; the same basis solution remains positive under sufficiently small perturbations.


## Polynomial-pencil setup for Rounds 098–100

The actual pencils and their reciprocal identities, cited below as Rounds 095–096, are retained in [the exact fixed-row setup](verified_results.md#the-exact-fixed-row-sdp) and [the coupled-spectra identities](verified_results.md#what-the-coupled-spectra-retain). Explicitly, on H=v⊥ for a real unit v, put D_β=diag(β), μ=v^TD_βv, w=D_βv, p=∏_jβ_j, T_β=(1+μ)D_β−ww^T, B=T_β|_H and N=pT_{1/β}|_H. The notation |H means compression to H. The reciprocal expression for N is interpreted after polynomial cancellation, including when some β_j=0. Put s=1+μ and t=p+Σ_jv_j²∏_{k≠j}β_k. Then B#=sN, N#=tB, BN=NB=stI_H, det B=s²t and det N=st², where # is the three-dimensional adjugate. The common (3,3) law used below is the retained [three-color theorem](geometry_three_color_theorem.md), not an assertion of a universal simultaneous anchor reconstruction.

## Round 098 — Every coordinate-anchor restriction has an exact (3,3) determinant model

**Mechanism.** Return to K_j. Set u=v_j, d=1−u², and let Y be its projected
coordinate coisometry with columns indexed by k≠j. Put r=(v_k)/√d,

\[
 A=YD_{\beta_{j^c}}Y^T,\quad
 \rho=r^TD_{\beta_{j^c}}r,\quad
 h=YD_{\beta_{j^c}}r,\quad p_j'=\prod_{k\ne j}\beta_k.
\]

The restriction of the first pencil is

\[
 B|_{K_j}=(1+u^2\beta_j)A+d(\rho A-hh^T).
\]

The 3×3 block adjugate identity gives
ρA−hh^T=p_j' adj(YD_{1/\beta_{j^c}}Y^T). For the real quarter-turn J
on K_j, adj(YD_γY^T)=JYD_γY^TJ^T. Therefore

\[
 \boxed{
 B|_{K_j}
 =Y D_{(1+u^2\beta_j)\beta_k}Y^T
 +(JY)D_{d\prod_{\ell\ne j,k}\beta_\ell}(JY)^T.
 }
\]

Both frames are 2×3 coisometries. The new common law supplies an exact
convex combination for this restricted determinant, with one law valid
for all β. Division by zero is avoided by the displayed product form.
Moreover det(B|_{K_j})=w_j^T adj(B)w_j=s w_j^T Nw_j.

**Scope.** This is a proved local determinant representation controlling the special directions w_j. A general row in v⊥ need not be one of these directions. No universal simultaneous reconstruction is asserted.

## Round 099 — Reciprocal support matrices have matched inertia, and the normal branch is explicit

**Mechanism.** For invertible complex symmetric B and any complex η,

\[
 \operatorname{Re}(\bar\eta B^{-1})
 =B^{-*}\operatorname{Re}(\eta B)B^{-1}.
\]

Here Re denotes the Hermitian part, which equals entrywise real part for
a complex symmetric matrix. This is a direct expansion of both sides.
Hermitian congruence therefore gives identical positive, negative, and
zero inertia counts. Through N=st B^{-1}, it is an exact phase-coupled
inertia constraint on the two real support pencils.

If B=X+iY is normal, the real symmetric matrices X,Y commute. A real
orthogonal basis diagonalizes both, and also N. For its three complex
eigenvalues b_r, the exact inner support is then

\[
 \max_{r\ne q}
 \left\{\operatorname{Re}(\lambda_1b_r)
 +\operatorname{Re}(\lambda_0st/b_q)\right\}.
\]

**Status: proved.** This solves the orthogonal-completion optimization on
the normal-pencil branch. Comparing the resulting scalar expression with
the original weighted permutation support still requires a spectral
inequality; no automatic comparison is asserted.

## Round 100 — The remaining weighted support inequality has an explicit radical form

**Mechanism.** On H=v⊥ let

\[
 M=\operatorname{Re}(\lambda_1B),\qquad
 L=\operatorname{Re}(\lambda_0N).
\]

The exact completion maximum is
max_{x⊥y, ||x||=||y||=1}(x^TMx+y^TLy). For fixed x, the second term
is the largest eigenvalue of L compressed to x⊥. In dimension three put

\[
 \tau=\operatorname{tr}L-x^TLx,
\]

\[
 \Delta=2\operatorname{tr}L^2-(\operatorname{tr}L)^2
 -4x^TL^2x+(x^TLx)^2+2\operatorname{tr}L\,x^TLx.
\]

The compression is real symmetric 2×2, so Δ≥0 and its larger eigenvalue
is (τ+√Δ)/2. Thus

\[
 f(v)=\max_{x\in H,\|x\|=1}
 \left[x^TMx+\frac{\tau+\sqrt\Delta}{2}\right].
\]

For the proposed weighted majorant
H_v=Σ_jv_j² max_{π(2)=j} Re(λ_0D_{0,π}+λ_1D_{1,π}), define

\[
 W=2H_v-2x^TMx-\tau.
\]

The weighted CH conjecture is exactly the pair of inequalities

\[
 \boxed{W\ge0,\qquad W^2\ge\Delta}
\]

for every actual β, v, support λ, and unit x⊥v, with the adjugate-pair
relations of Round 096 imposed. Using the unweighted permutation support
instead of H_v gives an exact sufficient-and-necessary MOC4 support
obligation after the independently proved U4-to-real-O4 convexification.

**Status: exact final reduction; the universal inequalities are unresolved.**
Separate one-pencil bounds, conditional quotient laws, and restricted
normal branches do not establish them. A violation would construct an
actual completion by taking y to be the top compressed eigenvector;
a proof would close the corresponding full support assertion.


# An all-dimensional contact reduction for Marcus–de Oliveira

## Outcome

This note gives a contact reduction with the relative unitary held fixed and a closed formula for the fitted signed minor law.

For each fixed `U`, any counterexample can be replaced by an actual complex spectral counterexample for the same `U` having at least `2n−2` maximizing permutation products in one support direction. The proof uses the complex matching-source cone, not independent subset couplings. An explicit classification of its constant-parallel lines removes the exceptional case in the complex-curve argument.

Theorems 1–4 establish the reduction. Positivity on the resulting high-contact sources, equation (19), remains open and is equivalent to unrestricted MOC. Section 5 records the limits of signed inversion, compact-minimum equations, and determinantal flag couplings at that step.

## 1. The linear functional supplied by a unitary

Write

\[
d_U(a,b)=\det(D_a+UD_bU^*),\qquad
z_\pi=\prod_i(a_i+b_{\pi(i)}),\qquad
\rho_U(I,J)=|\det U[I,J]|^2.
\]

All subsets in this note are unordered. Empty products and empty minors are one.

**Lemma 1.** For arbitrary complex spectra,

\[
d_U=\sum_{k=0}^n\sum_{|I|=|J|=k}
 a_{I^c}b_J\rho_U(I,J).
\tag{1}
\]

There is a real signed law `w(U)` on permutations such that

\[
\sum_\pi w_\pi=1,\qquad
\sum_{\pi(I)=J}w_\pi=\rho_U(I,J),\qquad
 d_U=\sum_\pi w_\pi z_\pi.
\tag{2}
\]

One choice is

\[
w_\pi=\Re\!\left[\frac{\operatorname{sgn}(\pi)
                 \prod_i U_{i,\pi(i)}}{\det U}\right].
\tag{3}
\]

**Proof.** Expanding the determinant in the diagonal entries of `D_a`, then applying Cauchy–Binet to every principal minor of `UD_bU*`, proves (1). On a permutation fibre `π(I)=J`, Laplace expansion gives the corresponding signed product of the two complementary minors divided by `det U`. Jacobi's complementary-minor identity for a unitary makes this product exactly `ρ_U(I,J)`, a real number. Taking real parts therefore preserves every fibre sum. Expanding each `z_π` in its chosen `b` factors proves the last equality in (2). The imaginary amplitudes cancel coefficientwise on each fibre, so taking real parts of the weights preserves the complex first moment. ∎

Let `V_n` be the real function space on `S_n` spanned by the indicators `1[π(I)=J]`. A real signed law as in (2) defines

\[
L_U(g)=\sum_\pi w_\pi g_\pi\qquad(g\in V_n).
\tag{4}
\]

This value does not depend on which complete-minor signed law was chosen. In particular,

\[
L_U(1[\pi(i)=j])=|U_{ij}|^2.
\tag{5}
\]

For an actual source `z`, a support index `r`, and an absorbed complex phase, the gap vector is

\[
g_\pi=\Re(z_r-z_\pi)\ge0.
\tag{6}
\]

Its directional MOC gap is exactly `L_U(g)`. This remains valid at collisions and singular sums.

## 2. Closed harmonic formula for the fitted signed weights

Put

\[
m=\lfloor n/2\rfloor,\qquad
d_j=\binom nj-\binom n{j-1},\qquad
S_k(\pi;U)=\sum_{|I|=k}\rho_U(I,\pi(I)),
\]

where `S_0=1`, `S_{−1}=0`, and `binom(n,−1)=0`.

**Theorem 2.** Another choice in (2), the minimum-Euclidean-norm complete-minor signed law, is

\[
\boxed{
 w_\pi(U)=\frac1{n!}\sum_{j=0}^{m}d_j\bigl(S_j(\pi;U)-S_{j-1}(\pi;U)\bigr).
}
\tag{7}
\]

Thus, in `w=(c_0+Σc_k S_k)/n!`, for `n≥2`,

\[
c_0=2-n,\qquad c_k=d_k-d_{k+1}\ (1\le k<m),\qquad c_m=d_m.
\tag{8}
\]

The four fitted rows are

| n | `(c_0;c_1,...)` |
|---|---|
| 3 | `(-1;2)` |
| 4 | `(-2;1,2)` |
| 5 | `(-3;-1,5)` |
| 6 | `(-4;-4,4,5)` |
| 7 | `(-5;-8,0,14)` |
| 8 | `(-6;-13,-8,14,14)` |

The question's table should be headed `c`, not `n! c`, if its displayed formula already has denominator `n!`. There is no extra factor two at the middle exterior degree.

**Proof mechanism.** Write `B_k=(ρ_U(I,J))` in the orthonormal subset basis, and let `D_k` be down-incidence between Boolean levels. Orthogonality of the columns of `U` and Cauchy–Binet give

\[
D_kB_k=B_{k-1}D_k,\qquad B_kD_k^T=D_k^TB_{k-1}.
\tag{9}
\]

For example, both sides of the underlying entry identity compute the squared norm of a contraction of an orthonormal exterior product:

\[
\sum_{I\supset H,\ |I|=k}\rho_U(I,J)
 =\sum_{K\subset J,\ |K|=k-1}\rho_U(H,K).
\]

The Boolean permutation modules split multiplicity-free into the real irreducibles of shapes `(n−j,j)`, of dimensions `d_j`. Choose the incidence embeddings as isometries. Equations (9) identify the same matrix block at every level where that irreducible occurs. Consequently `S_j−S_{j−1}` is precisely its matrix-coefficient function. Real Schur orthogonality inverts that block with coefficient `d_j/n!`. This proves (7) and every fibre equation for `k≤m`; complementary minors prove the remaining levels. The trivial block proves total mass one. The inverse lies in `V_n`, while the difference of any two complete-minor laws is orthogonal to `V_n`; hence the minimum-norm statement. A detailed proof is in `next_harmonic_algebra.md`, Section 1.

This identity resolves the fitted pattern, not the sign problem. At the exact orthogonal matrix

\[
O=\frac15\begin{pmatrix}
4&-2&-1&-2\\2&4&-2&1\\1&2&4&-2\\2&-1&2&4
\end{pmatrix},
\]

(7) has minimum weight `−89/3750`. More importantly, the archive's exact compound separator shows that **no** positive law reproduces all its minor marginals. The original scalar MOC assertion still allows spectrum-dependent corrections.

### Sequence interpretation

The dimensions are ballot numbers: with the indexing of OEIS [A009766](https://oeis.org/A009766), `d_j=T(n−j,j)`. Its formula is
`T(p,q)=binom(p+q,p)−binom(p+q,p+1)`, and its tableaux interpretation is the standard tableaux of shape `(p,q)`. Thus the reindexing is structural, not a fit. In particular `Σ_j d_j²=Cat_n`, the matching-space dimension. The upper coefficient is `c_{2m,m}=Cat_m`, `c_{2m+1,m}=Cat_{m+1}`, giving `1,2,2,5,5,14,14,...` starting at `n=2`. The even/odd subsequences, with their stated index shifts, match [A000108](https://oeis.org/A000108). The entry formulas were read and agree with the representation proof. A proposed match with increasing repeat lengths was rejected; it was a different sequence.

## 3. The source cone and its constant-parallel lines

For spinors `u_i,v_j∈C²`, set

\[
[u,v]=u_1v_2-u_2v_1,\qquad
 z_\pi=\prod_i[u_i,v_{\pi(i)}].
\]

Let `X_n⊂V_n⊗C` be the affine matching-source cone. It is irreducible, has dimension `d=2n−2` for `n≥2`, and contains the constant profile `e_π=1`.

These statements concern actual sources, not a larger real secant hypersurface. The degree-one matching invariants generate the equal-multidegree `SL₂` invariant ring. Bipartite matchings span them: pair a row-row bracket with a column-column bracket and use the Plücker identity until every edge crosses the bipartition; a regular bipartite graph decomposes into perfect matchings. Equivalently this is the standard invariant quotient of `2n` labelled points on `P¹`. The reductive quotient map is onto, so every point of the affine cone is represented by spinors (zero included). Its dimension is also immediate from the following dense chart.

On the open set where every `z_π≠0`, use a common projective change of coordinates and nonzero individual rescalings to arrange

\[
u_i=(1,x_i),\quad v_j=(y_j,1),\quad x_1=y_1=0.
\]

Then

\[
z_\pi=\alpha\prod_i(1-T_{i,\pi(i)}),\quad
T=xy^T,\quad \operatorname{rank}T\le1,
\tag{10}
\]

with first row/column zero, `α≠0`, and no remaining entry of `T` equal to one. This identifies the open cone with `C*` times the rank-at-most-one `(n−1)×(n−1)` matrix variety with these nonvanishing conditions. For a direct inverse, choose `π` using `(1,1),(i,j)` and let `σ` swap only these edges. Then

\[
T_{ij}=1-z_\pi/z_\sigma.
\tag{11}
\]

Recover `α` from any matching. Thus the chart holds on the closure as well as on the initially parametrized configurations. This is the established local quotient chart of Howard–Millson–Snowden–Vakil, *The equations for the moduli space of n points on the line*, Lemma 4.3; its proof on pp. 18–20 was read in the primary PDF. We use its elementary matching-coordinate version here.

**Theorem 3 (line classification).** For `n≥2`,

\[
x+\mathbb C e\subset X_n
\quad\Longleftrightarrow\quad
x_\pi=f(\pi(i_0))\ \text{for one row }i_0,
\ \text{or}\ x_\pi=f(\pi^{-1}(j_0))\ \text{for one column }j_0.
\tag{12}
\]

**Proof.** Since `e+εx∈X_n`, differentiate (10) at `e`. Its tangent cone, rather than merely its tangent space, gives

\[
x_\pi=c+\sum_i r_i s_{\pi(i)}.
\tag{13}
\]

The rank-one condition is essential. Restrict to any three rows/columns, fixing a matching outside. Translate the selected `r,s` values to `(0,r,q)` and `(0,a,b)` and absorb constants into `t`. Applying (11) to the six matching values of `te+x` gives a two-by-two determinant

\[
-\frac{abrq\,t(a-b)(r-q)}
 {(t+ar)(t+aq)(t+br)(t+bq)}.
\tag{14}
\]

It must vanish identically in `t`. Thus the full `r` vector or the full `s` vector has at most two values. Suppose it is `r`, and shift/rescale it to `1_A`. If `|A|=1` or `n−1`, (13) is already a one-row function. Otherwise both groups have at least two labels.

For generic `t`, the products are nonzero and invariant under permutations within either row group. In the inverse (11), rows in the anchor group have zero `T` rows and the other group has one common `T` row. Hence, for `p=|A|`, their common value depends only on the image subset `J` and has both forms

\[
z_J=\alpha\prod_{j\in J}q_j
    =t+c+\sum_{j\in J}s_j,\qquad |J|=p.
\]

For any four distinct labels and an outside `(p−2)`-set `R`, the multiplicative relations among `z_{Rab},z_{Rac},...` imply

\[
(s_a-s_d)(s_b-s_c)=0,
\qquad(s_a-s_c)(s_b-s_d)=0.
\tag{15}
\]

Every four entries of `s` therefore contain at least three equal values; globally at most one entry is exceptional. This gives a one-column function in (13). Exchanging rows and columns covers the other case. For `n=2` the conclusion is immediate; for `n=3` a nonconstant two-valued vector already has a singleton group.

Conversely, for a one-row function take all ordinary row spinors to be `e_1`, the exceptional row to be `e_2`, and columns `(-(t+f(j)),1)`. Their matching products are `t+f(π(i_0))`. Transposition gives the column case. ∎

There is an explicit positive repair on this exceptional class. If `z_π=f(π(i_0))`, then

\[
d_U=\sum_j |U_{i_0j}|^2 f(j),\qquad
p_\pi=\frac{|U_{i_0,\pi(i_0)}|^2}{(n-1)!}.
\tag{16}
\]

These probabilities reproduce the evaluated source, without claiming all minor marginals. In particular every nonnegative gap obtained from a line in (12) has `L_U(g)≥0`.

## 4. Transfer to at least `2n−2` supporting contacts

**Theorem 4.** Fix `U∈U(n)`, `n≥2`. If an actual spectral source violates one directional MOC inequality, there is another actual finite complex spectral source, for the same `U`, whose directional gap is negative and for which at least `2n−2` permutations maximize the support.

**Proof.** Absorb the phase into the source and choose one maximizing index `r`. Put `g_π=Re(z_r−z_π)`. Assume `L_U(g)<0`. Its sum is positive; otherwise `g=0`. Positive scalar rescaling normalizes `Σg_π=1`.

Let `C` be the exact zero set of `g`, of size `k`, including `r`. Suppose `k<d=2n−2`. Intersect `X_n` with the complex equations

\[
z_r-z_\pi=(z_r-z_\pi)(z^0)\quad(\pi\in C\setminus\{r\}),
\qquad
\sum_\pi(z_r-z_\pi)=\sum_\pi(z_r^0-z_\pi^0).
\tag{17}
\]

There are `k` equations. Every component through `z^0` has complex dimension at least `d−k≥1`. If all gap functions are constant on such a component, it lies in `z^0+Ce`: the common kernel of their differences is exactly `Ce`. Closedness and positive dimension make it the entire line. Theorem 3 and (16) then contradict the negative gap.

Otherwise choose an irreducible affine curve through `z^0` on which some gap is nonconstant. Normalize and complete it to a compact connected Riemann surface `Σ`; only finitely many punctures `S` were added. The gap differences are meromorphic on `Σ`; denote their real parts by `h_π`. On the curve, the old contacts remain zero and `Σh_π=1`.

Suppose no point of this curve has both a new zero gap and negative `L_U(h)`. On the component

\[
\Omega=\{h_\pi>0\ (\pi\notin C),\ L_U(h)<0\}
\]

containing `z^0`, define `v=−L_U(h)` and extend it by zero outside. At any finite boundary point, negative `L_U(h)` would produce a new contact, contrary to the supposition. Thus `v` vanishes continuously at that boundary. Harmonic pasting makes it subharmonic on `Σ\S`. Since `0≤h_π≤1` in `Ω`, it is bounded. Its punctures are removable as subharmonic singularities.

A subharmonic function on compact connected `Σ` is constant. Since it is positive at `z^0`, `Ω=Σ\S`. Every `h_π` is consequently bounded there. A genuine meromorphic pole has real part unbounded with both signs in any punctured neighborhood, so no gap difference has a pole. Each is then constant on the compact surface. This contradicts the choice of curve.

There is therefore a finite negative point with an additional contact. Iterate until there are at least `d` contacts.

Finally these are actual, not merely formal, matching sources by the invariant quotient description. Their spinors are nonzero because the gap is negative. A common `SU₂` transformation makes all second coordinates nonzero. Writing `u_i=(x_i,y_i)`, `v_j=(s_j,t_j)` then gives

\[
[u_i,v_j]=y_i t_j(a_i+b_j),\quad a_i=x_i/y_i,
\quad b_j=-s_j/t_j.
\]

All products and the determinant are multiplied by the same nonzero scalar `L=∏y_i∏t_j`. Absorbing `L` into the support direction yields finite complex spectra and the same `U`. This proves the claimed scope, including any degenerate intermediate sources. ∎

The complex-curve proof generalizes the archive's checked `n=4` curve-exit argument using the all-dimensional constant-line classification.

### A cone consequence

Let `A` be all nonnegative real gap vectors arising from `X_n`, and `A_d` those with at least `d=2n−2` zero entries. Then

\[
 A\subset\overline{\operatorname{cone}
 \bigl(A_d\cup\{1[\pi(i)=j]:i,j\in[n]\}\bigr)}.
\tag{18}
\]

Indeed any separating functional from the closed cone on the right is nonnegative on its entry indicators. The same curve proof, using Theorem 3, transfers a negative value on `A` to one on `A_d`, a contradiction. Thus a positivity theorem on the high-contact sources would propagate globally. This is stronger than a claim about generic smooth sources: it retains collisions and singular quotient points.

## 5. The missing assertion and attempts to prove it

The exact remaining assertion in this proof attempt is

\[
\boxed{L_U(g)\ge0\quad
 \text{for every actual nonnegative gap }g\text{ with at least }2n-2\text{ contacts}.}
\tag{19}
\]

With Theorem 4, (19) is equivalent to unrestricted MOC. It is a boundary restriction with a proved return argument, not a theorem obtained by defining desired positive weights.

Three attempts exposed specific limitations.

1. **Signed inversion.** Formula (7) organizes all exterior degrees in every dimension and closes the exceptional lines through (16). Its weights nevertheless have genuine negative mass, and the compound obstruction prevents a universal coefficientwise repair. A viable repair must use the evaluated source and may change the other minor marginals. Positivity of each exterior-level Birkhoff decomposition cannot be substituted for that repair.

2. **Compact minimum plus high contact.** The archive's compact spinor global minimum has a common active-law KKT system and `Σww*=nI₂`. However the affine complex-curve transfer above does not preserve the product of spinor norms. Renormalizing changes every gap by a common positive factor, preserving its sign but not its minimal value. Therefore one cannot assert both the high-contact property and all compact-global-minimum equations at the same witness. Common normalized `SL₂` directions in fact have positive second variation at a negative balanced minimum, not a hidden descent. The mixed unitary derivative in those symmetry directions vanishes.

3. **Positive flag coupling.** Honest projection-DPP flags fix all singleton Born marginals. The archive has an exact input for which no distribution retaining those marginals reproduces the determinant. Changing which covering coupling is used cannot solve it. `next_probabilistic_rounding.md` constructs an exact small positive change of measure at that input and solves a capped-density auxiliary optimization. But the equation making its initial expectation equal to `d_U` is still the global missing inequality; the martingale tower property does not establish it.

### A thin-hull continuation attempt

To try to pass through zero-gap endpoints of a normalized deformation, we investigated the joint first jet at real spectra. Let `M=D_a+UD_bU*` be Hermitian and set

\[
J_U=(\det M,\operatorname{diag}\operatorname{adj}M,
      \operatorname{diag}(U^*\operatorname{adj}M U)).
\]

A necessary condition for unrestricted MOC is

\[
J_U\in\operatorname{conv}\{(z_\pi,\partial_a z_\pi,
                                     \partial_b z_\pi)\}.
\tag{20}
\]

Indeed perturb `a→a+iεα`, `b→b+iεβ` and use the support multiplier `−i+εc`. The first-order coefficient is an arbitrary real linear functional of this joint jet. A strict separator in (20) would give an actual complex normal MOC counterexample for all sufficiently small positive `ε`. This implication was already derived in the early archive.

The companion script uses polynomial cofactors, including singular sums, and complete permutation enumeration. All 250 numerical LPs at `n=3,4,5,6` were feasible; the largest normalized equality residual was `1.64e−12`. Repeated real eigenvalues were included. These are finite checks of (20), not a proof. A small real-product second-compound probe also found no violation or proof mechanism.

An attempted ratio-of-harmonic-functions improvement to Theorem 4 stalls at `Σg=0`: the unnormalized gap vanishes there, while its normalized ratio can have a nonzero limit. Controlling this first derivative requires information such as (20), not merely removable-singularity theory. The existing compact normalization cannot silently supply it. The supported next attack is to prove a source-dependent positive first-jet law at these thin-hull endpoints, or to construct the required high-contact positivity directly in the rank-one chart (10). No theorem asserting either has been used above.

## 6. Useful route eliminations

The archive's exact spectra

\[
a=(2+5i,2-3i,-2+i,5+4i),\quad
b=(1+i,-2+2i,3+3i,1-5i),\quad\eta=1
\]

already refute the user draft's generic benign-landscape assertion: the identity is a strict local maximum on the relative flag, with support `129`, but another permutation has support `1099`. All six transposition losses are strictly positive, so this obstruction persists under small generic perturbations. It does not refute MOC or the weaker existence of a reducing global maximizer.

The new extremal note also analyzes which individual rank-one phases are flat at the Walsh anchor. Such facts concern an unnecessarily restrictive rounding class. Pair-sphere or coordinated higher-rank moves must be treated separately; an obstruction to one move family is not an obstruction to every route to the support maximum.

The Kovačec 2026 preprint's stronger polygon assertion was read and checked against the archive's exact counterexample. That example still satisfies original MOC. It supplies no counterexample to the target. Drury's primary compound papers remained inaccessible at the attempted publisher/mirror URLs; we do not claim to have read their full texts. Instead the relevant stronger-law obstruction was reconstructed from the retained exact matrix and separator.

## 7. Reading scope, computation, and continuation files

The following inventory records the workspace at the time of the investigation, before later cleanup. The initial recursive inventory counted 37,498 ordinary workspace files. The early path/size list is `/tmp/moc-workspace-inventory.tsv` (37,500 paths, including two research files created before that snapshot was saved). Most files are generated dependencies: `build/lean0710` alone has 31,959 files and about 4.76 GB. Empty hidden directories and private harness state were not treated as mathematical evidence. `moc-results.zip` has 714 members; `contextdex/research_workspace.tar.gz` has 1,940 members, grouped as archived copies rather than expanded into another workspace.

After reorganization, the older export and handoff snapshot live under [`archive/`](../../archive/README.md). That guide also locates the historical research stream, generation specification, and preserved build records; the downloaded Lean environment was removed as regenerable.

The PDF manifest accounts for 77 original paths as 59 distinct PDFs, 4,287 pages; the largest standalone volume is 3,651 pages. Matching `docs/full_text` extractions preserve those arguments, and three image-only diagrams have explicit separate descriptions. We read the principal source arguments relevant to the routes above, plus corresponding mathematical code/data definitions. Coverage was selective: repetitive contact tables, generated JSON/caches, and the whole 3,651-page volume were not read line by line. The companion notes record their substantive coverage and exclusions.

The mechanisms, rather than a full audit catalogue, determined subsequent reading: signed fibre laws and Boolean incidence; the actual-source quotient chart; the complex-curve proof; compact mixed variations; honest DPP coverings and their Born obstruction; normal-compression resolvent defects. Primary HMSV Section 4.3 was read because it supplied the exact chart used in Theorem 3. Broader bibliography expansion stopped when it no longer changed a bridge.

Focused files:

- `next_unrestricted_research.md`: this common proof attempt and exact unresolved step.
- `next_harmonic_algebra.md` and `code/research/next_harmonic_algebra.py`: full signed inversion and source-line proofs; finite fibre and symbolic checks.
- `code/research/next_source_contact.py`: cross-ratio inverse checks and joint thin-hull jet LPs.
- `next_extremal_geometry.md` and companion script: exact extremal/rounding deductions and limitations.
- `next_probabilistic_rounding.md` and companion script: legitimate flag disintegration, observable-dependent measure change, and capped-expectation auxiliary problem.
- `next_archive_mechanism.md` and companion script: all-dimensional rank-one resolvent defects, phase-dependent quadratic repair, and the failure of a fixed defect plane.

Theorems 1–4 use the written proofs, independently of numerical observations and finite transport checks. They cover every finite dimension, arbitrary complex spectra, and arbitrary complex unitary mixing. The implication from (19) back to MOC includes degenerate spectra and singular sums.

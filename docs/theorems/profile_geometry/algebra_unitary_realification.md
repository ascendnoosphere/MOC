# Four-dimensional unitary minor profiles are mixtures of real orthogonal profiles

## Statement and scope

For every U∈U(4), there are at most four matrices O_s∈O(4) and nonnegative weights λ_s with Σ_s λ_s=1 such that, for every pair of index sets I,J of the same cardinality,

\[
\boxed{|\det U[I,J]|^2
=\sum_s\lambda_s|\det O_s[I,J]|^2.}
\tag{1}
\]

A selected row can be fixed throughout the construction: after making that row of U real and nonnegative by column phases, every O_s has the same row. Row signs can be adjusted so that O_s∈SO(4), without changing any squared minor.

Consequently, for all complex spectra a,b, with the same weights and orthogonal matrices,

\[
\boxed{
\det(D_a+UD_bU^*)
=\sum_s\lambda_s\det(D_a+O_sD_bO_s^T).}
\tag{2}
\]

Thus MOC in dimension four for arbitrary complex unitary eigenvector changes is equivalent to its restriction to real orthogonal eigenvector changes. The spectra remain arbitrary complex. This is not a proof of real-orthogonal MOC, and it is not a common law on permutations.

## Antecedent and attribution

Oszmaniec, Guerini, Wittek and Acín, “Simulating positive-operator-valued measures with projective measurements,” Physical Review Letters 119, 190501 (2017), arXiv:1609.06139v2, Lemma 7, proves the corresponding trace-one three-effect decomposition over complex three-dimensional Hilbert space:

https://arxiv.org/html/1609.06139v2

The real-symmetric decomposition needed here is proved below, as are the minor-profile application and the at-most-four bound for effects obtained by taking real parts of rank-one complex projectors. No historical-priority claim is made.

## 1. A real trace-one three-effect lemma

Let E_1,E_2,E_3 be real symmetric positive semidefinite 3×3 matrices with

\[
\operatorname{tr}E_i=1,\qquad E_1+E_2+E_3=I_3.
\]

Then the triple belongs to the convex hull of triples

\[
(r_1r_1^T,r_2r_2^T,r_3r_3^T)
\]

for real orthonormal bases (r_1,r_2,r_3).

### Proof

The set of such triples is compact and convex. Suppose all three ranks are at least two. The space of symmetric matrices supported on the range of a rank-r effect has dimension r(r+1)/2. Thus the sum of these three support-space dimensions is at least nine.

A supported perturbation (H_1,H_2,H_3) must satisfy tr H_i=0 and ΣH_i=0. There are at most eight independent real linear constraints: six from the symmetric sum equation, plus two further trace constraints, because summing the three traces is already implied. A nonzero supported perturbation therefore exists.

For sufficiently small positive and negative t, each E_i+tH_i remains PSD; the perturbation preserves all constraints. Hence the triple is not extreme.

At an extreme point some effect has rank one. Its trace makes it an orthogonal projection P. Since the other two effects are PSD and sum to I−P, both are supported on P⊥. They sum to the two-dimensional identity there, so they commute and diagonalize simultaneously. If their eigenvalues are θ,1−θ and 1−θ,θ, their triple is the convex combination, with weights θ and 1−θ, of the two orthogonal bases obtained by exchanging the two complementary basis vectors.

Therefore every extreme point is a real orthogonal rank-one projection triple. Compact convexity proves the lemma.

## 2. At most four bases for the effects relevant here

Assume in addition that every E_i has rank at most two.

If one effect has rank one, the preceding proof gives at most two bases. Otherwise all ranks equal two. Choose a nonzero supported perturbation as above, and let [t_−,t_+] be its maximal PSD interval. This interval contains zero in its interior and has finite endpoints: trace-one PSD matrices form a bounded set.

At each endpoint at least one effect drops to rank one. Rank zero is impossible because its trace remains one. Thus each endpoint triple is a mixture of at most two orthogonal bases.

The original triple is the convex combination of its two endpoint triples:

\[
E_i=
\frac{t_+}{t_+-t_-}(E_i+t_-H_i)
+\frac{-t_-}{t_+-t_-}(E_i+t_+H_i).
\]

Combining the decompositions gives at most four real orthogonal bases.

## 3. Construct the real effects from a unitary matrix

Choose row 2 for convenience. Multiply U on the right by a diagonal unitary D whose jth entry is the conjugate phase of U_2j whenever that entry is nonzero. Put V=UD. Its second row is

\[
v=(|U_{21}|,\ldots,|U_{24}|)\in\mathbb R^4.
\]

Column phases do not change squared minors. They also leave U D_b U* unchanged, because D commutes with every diagonal D_b.

Treat each of the other rows of V, transposed, as a complex column x_i. Define

\[
E_i=\operatorname{Re}(x_i x_i^*),\qquad i\in\{1,3,4\}.
\]

These matrices are real symmetric and PSD on real vectors, because

\[
y^TE_i y=|x_i^*y|^2\ge0.
\]

Each has trace one and rank at most two: it is the sum of the outer products of Re x_i and Im x_i. Row orthogonality gives E_i v=0, and completeness gives

\[
E_1+E_3+E_4=I_4-vv^T.
\]

Thus, on the three-dimensional real space v⊥, these are exactly the effects covered by the at-most-four lemma.

Choose the resulting real orthonormal triples in v⊥ and insert v as row 2. This produces at most four real orthogonal matrices O_s.

## 4. Verify every minor size

### Singletons

For each nonfixed row,

\[
|V_{ij}|^2=(E_i)_{jj}
=\sum_s\lambda_s(O_s)_{ij}^2.
\]

The fixed row v is unchanged.

### Two-by-two minors containing the fixed row

For any other row x_i and columns j,k,

\[
|x_{ij}v_k-x_{ik}v_j|^2
=(v_k e_j-v_j e_k)^TE_i(v_k e_j-v_j e_k).
\]

This is linear in E_i. The decomposition therefore preserves every such squared minor.

### Two-by-two minors not containing the fixed row

For a 4×4 unitary matrix, complementary-minor identities imply

\[
|\det V[I,J]|^2
=|\det V[I^c,J^c]|^2.
\]

If I does not contain row 2, its two-element complement does. The same identity holds for every real O_s, so the remaining two-minors are preserved as well.

### Three-minors and endpoints

Three-minors are complementary to singletons. Empty minors and full determinant moduli equal one. This proves (1).

## 5. Determinants for all complex spectra

Cauchy–Binet and expansion in the diagonal entries of D_a give

\[
\det(D_a+UD_bU^*)
=\sum_{\substack{I,J\subset[4]\\|I|=|J|}}
a_{I^c}b_J\,|\det U[I,J]|^2.
\]

Substitute (1). The finite sums interchange, proving (2). This is an identity for every pair of complex spectra with one spectrum-independent mixture over real orthogonal matrices.

If every real orthogonal summand obeys MOC, its determinant belongs to the common permutation polygon. Convexity and (2) give the arbitrary-unitary case. The converse is immediate.

For a real O_s with determinant −1, multiply a row other than the fixed row by −1. This changes its determinant to +1 and preserves all squared minors, so SO(4) suffices.

## 6. Joint coefficient-hull convexification and explicit matrices

Fix β∈C⁴ and v∈R⁴ with ||v||=1. Put

\[
m=\sum_j\beta_jv_j^2,\qquad
w=D_\beta v,
\]

\[
\boxed{T_\beta(v)=(1+m)D_\beta-ww^T.}
\tag{3}
\]

The matrix is complex symmetric. Its diagonal and off-diagonal entries are

\[
(T_\beta)_{jj}=\beta_j+\sum_{k\ne j}\beta_j\beta_kv_k^2,
\qquad
(T_\beta)_{jk}=-\beta_j\beta_kv_jv_k\quad(j\ne k).
\]

For the coefficient-hull target, with row effects E_1,E_3 as above,

\[
\boxed{D_1=\operatorname{tr}(T_\beta E_1).}
\tag{4}
\]

If p=∏β_j and γ_j=1/β_j, then

\[
\boxed{D_0=p\,\operatorname{tr}(T_\gamma E_3).}
\tag{5}
\]

The right side in (5) is polynomial after cancellation; zeros of β follow directly from its entrywise polynomial form. The formula uses q_14,J=q_23,Jc and the complementary expression for the triple minor.

Since complex symmetric matrices pair only with the real symmetric part of x_i x_i*, the same effect decomposition preserves D_0 and D_1 simultaneously. Thus it gives a convex combination in all four real coefficient-hull coordinates, independent of β and the support functional.

Useful identities, when the indicated inverses exist, are

\[
T_\beta(v)v=D_\beta v,
\]

\[
T_\beta(v)^{-1}
=\frac{D_{1/\beta}+vv^T}{1+\sum_j\beta_jv_j^2},
\]

\[
\det T_\beta(v)
=\left(\prod_j\beta_j\right)
\left(1+\sum_j\beta_jv_j^2\right)^3.
\]

These follow directly from the rank-one update formula.

## 7. An exact inner SDP for the remaining real problem

For the support functional Re(λ₀D₀+λ₁D₁), restrict the following real symmetric matrices to v⊥:

\[
M_1(v)=\operatorname{Re}(\lambda_1T_\beta(v)),
\]

\[
M_3(v)=\operatorname{Re}(\lambda_0pT_{1/\beta}(v)),
\qquad M_4(v)=0.
\]

The maximum over every orthogonal completion of the fixed row v equals the SDP

\[
\max\sum_{i\in\{1,3,4\}}\operatorname{tr}(M_iE_i)
\]

subject to E_i≥0, tr E_i=1, and ΣE_i=I_3. Exactness follows from the real frame-decomposition lemma. This is not an outer relaxation.

Its dual is

\[
\min\left(\operatorname{tr}Y+\alpha_1+\alpha_3+\alpha_4\right)
\]

subject to

\[
Y+\alpha_iI_3-M_i(v)\succeq0.
\]

Strict primal feasibility holds at E_i=I_3/3, so the usual finite-dimensional SDP duality has no gap. A common scalar shift permits α₄=0; then Y≥0.

An actual-spectral formula for dual-feasible Y,α with objective at most the permutation support h, valid for every real unit v and every actual coefficient-hull facet, would prove MOC in dimension four. No such universal dual certificate has been constructed here.

## Limits

The proof uses dimension four twice: the real fixed-row complement has dimension three, and every two-minor not involving the fixed row is complementary to one that does. Neither step extends automatically to higher dimensions.

The theorem transfers linear inequalities in the full minor profile from real orthogonal matrices to complex unitaries. It does not replace the remaining real matrices by permutations, nor does it prove that one quaternion factor suffices in SO(4).


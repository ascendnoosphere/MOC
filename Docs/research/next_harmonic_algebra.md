# Harmonic inversion, constant-source lines, and the positivity gap

This note proves two all-dimensional algebraic theorems and an explicit positive repair on their exceptional source class. It also gives an exact obstruction to a weaker quantum bridge. Generic source-dependent positivity remains open; the companion script checks finite instances and symbolic identities.

## 1. Exact answer to the proposed coefficient table

Use **unordered** subsets and set

\[
B_k(U)_{I,J}=|\det U[I,J]|^2,\quad
S_k(\pi;U)=\sum_{|I|=k}B_k(U)_{I,\pi(I)},\quad S_0=1.
\]

Put \(m=\lfloor n/2\rfloor\), \(d_j=\binom nj-\binom n{j-1}\), where \(\binom n{-1}=0\), and \(S_{-1}=0\).

**Theorem 1 (canonical signed law).** For every complex unitary \(U\),

\[
\boxed{w_\pi(U)=\frac1{n!}\sum_{j=0}^m d_j\,[S_j(\pi;U)-S_{j-1}(\pi;U)]}
\tag{1}
\]

is real, sums to one, and satisfies, in every exterior degree,

\[
\boxed{\sum_{\pi:\pi(I)=J}w_\pi=B_{|I|}(U)_{I,J}.}
\tag{2}
\]

In the user's notation,

\[
c_0=2-n,\qquad c_k=d_k-d_{k+1}\ (1\le k<m),\qquad c_m=d_m
\tag{3}
\]

for \(n\ge2\). Thus the proposed four rows are **already correctly normalized when the denominator is \(n!\)**:

| n | \((c_0;c_1,\ldots,c_m)\) |
|---|---|
| 2 | \((0;1)\) |
| 3 | \((-1;2)\) |
| 4 | \((-2;1,2)\) |
| 5 | \((-3;-1,5)\) |
| 6 | \((-4;-4,4,5)\) |
| 7 | \((-5;-8,0,14)\) |
| 8 | \((-6;-13,-8,14,14)\) |

There is no additional middle-level factor two. Replacing \(S_k\) by an ordered-row-tuple sum multiplies it by \(k!\); the coefficient of that sum must then be divided by \(k!\). Ordering row and column tuples separately produces a different convention again. At \(U=I\), (1) is a central projection kernel, **not** a delta mass at the identity; neither \(w_{\mathrm{id}}=1\) nor positivity is a valid normalization test.

### 1.1 Incidence coherence, with its required normalization

Let \(M_k=\mathbb R^{\binom nk}\) have its usual orthonormal subset basis, and let \(D_k:M_k\to M_{k-1}\) be the unnormalized down-incidence matrix. Unitarity gives

\[
D_kB_k=B_{k-1}D_k,\qquad B_kD_k^T=D_k^TB_{k-1}.
\tag{4}
\]

For example, the entry identity behind the first equation is

\[
\sum_{I\supset H,\ |I|=k}|\det U[I,J]|^2
=\sum_{K\subset J,\ |K|=k-1}|\det U[H,K]|^2.
\tag{5}
\]

To see (5), the columns \(U[:,J]\) form an orthonormal \(k\)-frame. Contract their unit exterior product by the coordinate wedge indexed by \(H\). Its squared norm is the left side; the Gram determinant of its selected rows is the right side by Cauchy–Binet. The second equation follows by applying the first to \(U^*\) and transposing. Thus it is false to treat the \(B_k\)'s as independent doubly stochastic matrices.

The Boolean permutation module splits orthogonally as

\[
M_k=\bigoplus_{0\le j\le\min(k,n-k)}V_j,\qquad
V_j\cong S^{(n-j,j)},\qquad\dim V_j=d_j.
\tag{6}
\]

One elementary construction starts with \(\ker D_j\), then raises it to level \(k\) by up-incidence. The identity
\(D_{k+1}D_{k+1}^T-D_k^TD_k=(n-2k)I\)
on \(M_k\) gives the dimensions and the orthogonal chain decomposition. Normalize each raising embedding to an **isometry**. Equation (4) then identifies a single operator \(A_j(U)\) on \(V_j\) across all its levels. These operators need not be symmetric or positive semidefinite.

With a consistent real orthogonal matrix-coefficient convention for the permutation action,

\[
S_k(\pi;U)=\sum_{j=0}^k\langle A_j(U),R_j(\pi)\rangle_F
\qquad(k\le m).
\tag{7}
\]

Real Schur orthogonality says that multiplication by \(d_j/n!\) inverts this coefficient map in block \(j\). Subtracting adjacent equations (7) isolates block \(j\), proving (1) and reconstruction at levels \(k\le m\). The complementary-minor identity and \(\pi(I^c)=\pi(I)^c\) prove the other levels. The trivial block is \(A_0=1\), so the sum of the weights is one.

The function space of all subset-indicator coefficients has dimension

\[
\sum_{j=0}^m d_j^2=\mathrm{Cat}_n.
\tag{8}
\]

Formula (1) is the unique minimum-Euclidean-norm signed law with the specified complete minor marginals: it lies in this function space, whereas every difference of two laws is orthogonal to it. In particular canonical inversion is not an optimization for positivity.

### 1.2 Exactly what remains positive and what does not

Minor expansion gives, for arbitrary complex spectra,

\[
\sum_\pi w_\pi\prod_i(a_i+b_{\pi(i)})
=\det(D_a+UD_bU^*).
\tag{9}
\]

But the weights can be negative even in dimension three. There a different, nonnegative spectrum-independent law exists by Birkhoff decomposition of \(B_1\); the canonical harmonic law is not that decomposition.

In dimension four some profiles have **no** positive law with all the marginals (2). At

\[
O=\frac15\begin{pmatrix}4&-2&-1&-2\\2&4&-2&1\\1&2&4&-2\\2&-1&2&4\end{pmatrix}
\]

the five-coordinate separator of `algebra_local_marginal_obstruction.md` is \(639/625>1\). Every exact complete-minor signed law therefore has negative mass at least \(7/625\). For the canonical law, the companion script obtains minimum weight \(-89/3750\) and negative mass \(431/1875\). No correction in the universal, spectrum-independent kernel can make it positive. Block-diagonal embedding transfers the impossibility of full-minor positivity to every larger dimension. This is not an obstruction to spectrum-dependent MOC weights.

## 2. Rank-two matching sources: an explicit open chart

Let \(X_n\) denote the affine cone of matching-invariant vectors

\[
z_\pi=\prod_i[u_i,v_{\pi(i)}],\qquad u_i,v_j\in\mathbb C^2,
\]

or its algebraic closure in the linear matching span. Write \(e_\pi=1\). The cone has dimension \(2n-2\) for \(n\ge2\).

**Chart theorem.** The part of \(X_n\) where every \(z_\pi\ne0\) is isomorphic to

\[
\mathbb C^*\times\{T\in\operatorname{Mat}_{n-1}(\mathbb C):
\operatorname{rank}T\le1,\quad T_{ij}\ne1\},
\tag{10}
\]

via

\[
z_\pi=\alpha\prod_{i=1}^n(1-T_{i,\pi(i)}),
\qquad T_{1j}=T_{i1}=0.
\tag{11}
\]

This chart is established invariant geometry, not a novelty claim: see Howard–Millson–Snowden–Vakil, *The equations for the moduli space of n points on the line*, Section 4.3, Lemma 4.3, <https://math.umd.edu/~millson/papers/hmsvfinalversion.pdf>. The chart statement and proof on pp. 18–20 were checked in the downloaded text `/tmp/moc-hmsv.txt`, lines 938–1075. The following direct matching-coordinate inverse records the normalization needed here.

**Proof.** If every matching product is nonzero, every cross bracket is nonzero. Make \(u_1=e_1,v_1=e_2\) by one projective change of coordinates and individual nonzero rescalings. All other rows and columns then have forms
\(u_i=(1,x_i),v_j=(y_j,1)\), with \(x_1=y_1=0\). Individual rescalings affect every matching by the same nonzero scalar \(\alpha\). Hence \(T_{ij}=x_i y_j\) gives (11).

For a rational inverse, choose a permutation \(\pi\) using edges \((1,1),(i,j)\). Let \(\sigma\) differ only by replacing these edges with \((1,j),(i,1)\). Then

\[
\boxed{T_{ij}=1-z_\pi/z_\sigma.}
\tag{12}
\]

Other edges cancel. Recover \(\alpha\) from any one equation (11). All these formulas are regular on the specified open sets. They give mutual inverses on actual configurations, and the reconstruction identities extend to the closure after clearing the nonvanishing denominators. Thus taking the affine cone's closure introduces no extra points in this chart. Conversely factor any rank-at-most-one \(T=xy^T\); (11) constructs spinors. \(\square\)

At \(e\), the coordinates are \((\alpha,T)=(1,0)\). Differentiation gives

\[
\delta z_\pi=\delta\alpha-\sum_i\delta T_{i,\pi(i)}.
\tag{13}
\]

The linear map from \((\delta\alpha,\delta T)\) is injective: an entry array with all permutation sums constant is a row-plus-column array, and a row-plus-column array with first row and column zero is zero. Consequently:

* The Zariski tangent **space** at \(e\) is exactly the constant plus ordinary permutation-entry function space, dimension \(1+(n-1)^2\).
* Its tangent **cone** consists precisely of (13) with \(\operatorname{rank}\delta T\le1\). In ordinary-entry coordinates its nonconstant part is a rank-one standard-by-standard coefficient matrix.

The distinction between tangent space and cone is consequential. The former alone permits arbitrary assignment costs, whereas the latter already forces a separable assignment array.

## 3. Complete classification of source lines through the constant direction

**Theorem 2.** For \(n\ge2\), an affine line \(x+\mathbb C e\) is contained in \(X_n\) if and only if its coordinates have one of the forms

\[
\boxed{x_\pi=f(\pi(i_0))\quad\text{or}\quad
x_\pi=g(\pi^{-1}(j_0))}
\tag{14}
\]

for a fixed row \(i_0\) or fixed column \(j_0\). Constants are included.

**Proof, first step: rank-one assignment direction.** Since \(X_n\) is a cone, the line assumption implies \(e+\epsilon x\in X_n\). The tangent-cone description yields

\[
x_\pi=c+\sum_i r_i s_{\pi(i)}.
\tag{15}
\]

Adding constants to \(r\) or \(s\) only changes \(c\).

**Second step: one vector has at most two distinct entries.** Fix any three rows and any three columns, and fix a matching of the remaining labels. The resulting six coordinates of \(t e+x\), after an immaterial common factor, are actual three-by-three matching invariants. Translate the three selected \(r\)- and \(s\)-values so they are \((0,r,q)\), \((0,a,b)\); absorb constants into \(t\). Apply the inverse chart (12) to these six values. Its two-by-two determinant is

\[
-\frac{abrq\,t(a-b)(r-q)}
{(t+ar)(t+aq)(t+br)(t+bq)}.
\tag{16}
\]

It must vanish identically in \(t\). Therefore these three \(r\)-values or these three \(s\)-values have a repetition. If both full vectors had at least three distinct values, choose a distinct triple on each side and contradict (16). Thus at least one full vector has at most two values. For \(n=2\), (14) holds without this argument.

**Third step: two nontrivial groups force a singleton on the other side.** Suppose \(r\) has exactly two values. After a shift and rescaling, take it to be the indicator of a nonempty proper set \(A\). If \(|A|=1\) or \(n-1\), (15) already has the first form (14). Otherwise both \(A\) and its complement have size at least two.

For a generic \(t\), all coordinates \(z_\pi=t+x_\pi\) are nonzero and invariant under permutations of the rows within each group. Choose the anchor row 1 in \(A^c\). Formula (12) shows that every other row of \(A^c\) has zero \(T\)-row: swapping it with row 1 leaves both matching values equal. All rows in \(A\) have the same \(T\)-row: exchange two such labels in the numerator and denominator of (12), leaving each matching value unchanged. Therefore the normalized bracket matrix has one row type on \(A\), and the all-ones row on \(A^c\). Hence, for \(p=|A|\),

\[
z_J=\alpha\prod_{j\in J}q_j,
\qquad |J|=p,
\qquad z_J=t+c+\sum_{j\in J}s_j.
\tag{17}
\]

Take four distinct labels \(a,b,c,d\) and a set \(R\) of \(p-2\) other labels; this is possible since \(2\le p\le n-2\). The multiplicative identities

\[
z_{Rab}z_{Rcd}=z_{Rac}z_{Rbd}=z_{Rad}z_{Rbc}
\]

imply

\[
(s_a-s_d)(s_b-s_c)=0,
\qquad(s_a-s_c)(s_b-s_d)=0.
\tag{18}
\]

Thus every four selected \(s\)-values have at least three equal. This forces the full vector \(s\) to be constant except at at most one label: two groups each of size at least two violate (18), as does any choice with three or four different values. Equation (15) then has the column form in (14). The argument with rows and columns exchanged covers the alternative from step two. For \(n=3\), any nonconstant two-valued vector already has a singleton group.

**Converse.** For \(x_\pi=f(\pi(i_0))\), take all row spinors equal except row \(i_0\), and choose column spinors so the exceptional row brackets equal \(t+f(j)\), while the other row brackets equal one. Their products are exactly \(t+x_\pi\). For instance use ordinary rows \(e_1\), exceptional row \(e_2\), and columns \((-(t+f(j)),1)\). A transposition of the construction gives the column case. \(\square\)

## 4. An all-dimensional positive repair on the source-line class

Suppose an evaluated actual source satisfies \(z_\pi=f(\pi(i_0))\). The complete marginal identity (2) gives

\[
d(U)=\sum_j|U_{i_0j}|^2 f(j).
\tag{19}
\]

Thus for **every dimension and every support direction**,

\[
\Re(\eta d(U))\le\max_j\Re(\eta f(j))=\max_\pi\Re(\eta z_\pi).
\tag{20}
\]

An explicit nonnegative permutation law is

\[
\boxed{w'_\pi=\frac{|U_{i_0,\pi(i_0)}|^2}{(n-1)!}.}
\tag{21}
\]

It preserves the evaluated complex first moment and total mass, but generally **does not** preserve every exterior marginal. Therefore \(w'-w\) is in the kernel of this evaluated source, not necessarily in the universal matching-identity kernel. This is an actual rank-two, source-dependent positivity repair; it is not a signed-law-to-convexity inference. The column version is identical.

This classification and repair close the exceptional constant-parallel-line case in the [complex-curve contact argument](next_unrestricted_research.md). Generic high-contact sources require a separate positivity argument. In particular, the tangent-space dimension \(1+(n-1)^2\) cannot replace the source-cone dimension \(2n-2\) in such an argument.

## 5. What invariant-tensor positivity supplies, and a precise failure

The unnormalized bipartite singlet matching Gram matrix is

\[
K_{\pi,\sigma}=2^{\#\mathrm{cycles}(\pi^{-1}\sigma)}.
\]

Schur–Weyl decomposition of \((\mathbb C^2)^{\otimes n}\) shows that its nonzero eigenvalues are

\[
\boxed{\lambda_j=\frac{n!(n-2j+1)}{d_j},\quad
\text{multiplicity }d_j^2,\quad0\le j\le m.}
\tag{22}
\]

For \(n=4\), these are \(120^1,24^9,12^4\), exactly the repository's fourteen-channel loop metric. Its rank is \(\mathrm{Cat}_n\), not a positivity result for the coordinates of the inverse frame. The rank-two multiplier is a product-spinor matrix coefficient of this same representation. Its Fourier block in sector \(j\) has rank at most the GL2 multiplicity \(n-2j+1\). This is a real low-rank constraint, but no implication from it to a positive law has been proved here.

There is also an all-dimensional physical contraction. Let \(V\) embed \((\mathbb C^2)^{\otimes n}\) into \(\bigwedge^n(\mathbb C^n\otimes\mathbb C^2)\) by putting one fermion in each spatial mode. Up to the harmless inverse-permutation convention,

\[
T_U=\frac1{\det U}\,V^*\bigwedge^n(U\otimes I_2)V
=\sum_\pi\frac{\operatorname{sgn}\pi\prod_iU_{i,\pi(i)}}{\det U}P_\pi.
\tag{23}
\]

It is a contraction, commutes with the global two-state action, and acts as identity on the fully symmetric sector. Its product-spinor matrix coefficient is the desired Hadamard determinant. These statements follow from compression of a unitary operator, not a CP extrapolation from dimension four.

Contraction, invariance, and a fixed symmetric sector are insufficient for the directional bound. In three qubits set \(T=2P_{\mathrm{sym}}-I\). It is an invariant unitary and fixes the symmetric sector. For the product vector \(v=|001\rangle\),

\[
\langle v,Tv\rangle=2/3-1=-1/3.
\]

The permutation-orbit coefficients \(\langle v,P_\pi v\rangle\) are only zero or one. They are actual rank-two matching products, with multiplier \(C_{ij}=\langle s_i,s_j\rangle\) for the two colors in \(001\). The direction \(\eta=-1\) therefore violates the desired bound for this nonphysical invariant contraction. Hence a proof based on (23) must retain additional physical occupation/minor constraints; abstract operator contraction is an insufficient bridge. This is an obstruction to a proposed mechanism, not to MOC.

Likewise the balanced spinor identity \(\|S^TJT\|_*=n\) from `moc_balanced_bracket_nuclear_20261031.txt` cannot provide the missing directional comparison by itself. Schur-multiplier factorization already bounds the absolute determinant by one for unit spinors, but the matching polygon can occupy a much smaller directional region.

## 6. Source audit and reading coverage

The following principal files were read completely, rather than inferred from filenames:

* `docs/theorems/profile_geometry/verified_results.md` and `docs/theorems/finite_and_spin_geometry/structural_results.md`: realification in dimension four, colored-edge allocation for three left parents, Clifford converse, rank-two plane SDP, capacity/SOS distinction, derangement-face rigidity, and scalar compression equivalence. Their precise limitations are substantive: realification stops at a fixed-row four-effect obstruction in n5; the rank-two compression theorem does not imply the needed rank-three compression; reflection zero-gap vanishing does not prove the positive-gap energy estimate.
* `docs/theorems/finite_and_spin_geometry/COMMON_MINOR_POLYTOPE.md`, `docs/theorems/profile_geometry/algebra_local_marginal_obstruction.md`, `docs/theorems/profile_geometry/analysis_clifford_idempotent_reformulation.md`, and `docs/theorems/support_certificates/global_bridge_geometry.md`: full-minor positivity is genuinely false; complex Clifford Gram matrices are bilinear, not PSD; pointwise rank-two completion and its convex-hull replacement are distinct, with the latter unproved.
* Representative theorem-note batch `profile_geometry/algebra_theorem_notes_081_100.md` (including its appended rounds through 103), and representative support batch `support_certificates/restricted_support_proofs_01.md`: read actual oriented-row cuts, rank-one dual/SOS arguments, quaternion capacity allocation, and exact affine-weight obstruction. The support batch's simplex theorem closes its stated tetrahedral family, not generic spectral support. Other repetitive theorem-note batches were not individually read.
* `docs/research/moc_signed_scalar_variance_20261031.txt`, `moc_balanced_bracket_nuclear_20261031.txt`, `moc_spinor_plane_convex_20261031.txt`, `moc_fixed_b_clifford_kernel_20261031.txt`, `moc_qft_cp_completion_audit_20261031.txt`, `moc_qft_polynomial_tilt_20261031.txt`, `moc_global_nonlocal_fierz_construction_20261031.txt`, `moc_unrestricted_fierz_20261031.md`, and `moc_global_clifford_standard_projection_obstruction_20261031.txt` were read substantively (the first polynomial-tilt note's final few continuation lines were not reread). The full91/mixed77 residuals remain unresolved, not no-go theorems. Their already-refuted lower-dimensional POVM/Cartan restrictions cannot be silently reused. The signed scalar variance real-part bound fails for complex relative unitaries even for Hermitian spectral matrices; its real-orthogonal proof gives a modulus bound after realification, not the directional maximum.

Code actually inspected: `moc_qft_polynomial_tilt.py`, `moc_signed_scalar_variance_20261031.py`, `moc_global_link_pattern_interpolation.py`, and `code/theorems/finite_and_spin_geometry/root_common_hull_exact.py`. The first is numerical discovery with explicit positive-amplitude and SVD cutoffs; the second checks rational examples and the exact complex variance counterexample; the third exports all fourteen source features and eighty-one symmetric Gram gauges. The common-hull script's embedded completeness string is older than its separate boundary-chain proof and must not be treated as the current theorem status.

Concrete schema checks from those implementations: permutations are lexicographic zero-based tuples; exact matrices are generally serialized as rational strings; loop features are a 24-by14 table, the singlet basis is 70-by14, and symmetric Gram gauges are 14-by14. The polynomial-tilt replay stores Gaussian-integer spectra as `[real,imag]`, floating mixers, degree-specific angle/rank/margin fields, a seed, and sampled angle count; it is not an exact all-angle certificate. The audit covers the files listed here; unlisted theorem files and other Fierz/Clifford/QFT variants remain unaudited. Generated JSON and old solver replays were not comprehensively checked.

### Cofactor-jet archive follow-up

A focused follow-up read `docs/early/proof_notes/metaproof_notes.txt` and `docs/research/moc_global_actual_odd_jet_and_mobius_20261031.txt` completely. The former already proves that MOC would imply the **joint** first-jet hull condition
\((d,\nabla_a d,\nabla_b d)\in\operatorname{conv}\{(z_\pi,\nabla_a z_\pi,\nabla_b z_\pi)\}\)
at real spectra, by using the support phase \(-i+\epsilon c\); gradient-only containment is weaker. It reports feasible numerical LPs in dimensions four through six, not a proof. The latter gives the exact dimension-four formula
\(\Im\det(C_0+i\epsilon C_1)=\epsilon\operatorname{tr}(\operatorname{adj}C_0 C_1)-\epsilon^3\operatorname{tr}(\operatorname{adj}C_1 C_0)\)
for Hermitian \(C_0,C_1\), reducing the entire imaginary perturbation scale to a twenty-four-line LP. No universal first-jet positive law is established by either note.

## 7. Reproduction, sequence check, and remaining first gap

Run:

```bash
OPENBLAS_NUM_THREADS=1 python code/research/next_harmonic_algebra.py
```

The script prints JSON only. It checks every subset fiber through dimension seven on seeded complex unitaries, the complex determinant first moment, the exact n4 negative law and separating profile, a rational n5 source-chart inverse, the symbolic three-by-three line determinant, the four-label subset identity, and the exact eight-by-eight invariant-contraction obstruction. In the run accompanying this note, maximum fiber error was \(6.44\times10^{-15}\), and maximum relative complex first-moment error was \(2.17\times10^{-15}\). Finite checks supplement, not replace, the proofs.

The natural sequence is Catalan, not an unidentified coefficient pattern. An exact OEIS search and fetch verified [A000108](https://oeis.org/A000108), offset **0**, \(1,1,2,5,14,42,\ldots\). Here
\(\sum_jd_j^2=\mathrm{Cat}_n\), while
\(d_{\lfloor n/2\rfloor}=\mathrm{Cat}_{\lceil n/2\rceil}\).
A search of the repeated-Catalan sequence starting at n=0 did not give a reliable separate OEIS identification; none is asserted.

The next step is an evaluated-source-dependent correction of the harmonic signed law, or a support certificate using its physical fermionic compression, for sources not of (14). The source-line theorem handles the exceptional case in the contact deformation route. The generic directional inequality requires more than the two-row idempotent formula, positive loop metric, or invariant contraction.

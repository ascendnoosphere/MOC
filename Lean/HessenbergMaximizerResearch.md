# Hessenberg support maximizers: exact reduction and sparsification

Status: ordinary mathematical proofs and a residual conjecture. No general MOC
proof or Lean verification of the new statements is claimed.

Let \(A=\operatorname{diag}(a)\), \(B=\operatorname{diag}(b)\),
\(F_\eta(U)=\operatorname{Re}(\eta\det(A+UBU^*))\), and
\(G(U)=\|A+UBU^*\|_F^2\). A relative unitary is reindexed upper
Hessenberg if independent row and column permutations make \(U_{ij}=0\)
for \(i>j+1\). The eigenvalue labels must be reindexed with the matrix
when using invariance of the determinant.

## 1. Equivalence and a weaker structural target

For fixed spectra, existence of a reindexed upper-Hessenberg global support
maximizer for every \(\eta\) is equivalent to the determinant hull inclusion
for all relative unitaries with those spectra. Indeed, in the forward direction,
apply the already formalized theorem
SparseRow.lean: holds_of_reindexed_upper_hessenberg to a global maximizer
and use directional separation. In the reverse direction, choose a permutation
of maximal directional matching product. MOC bounds every unitary by that
value. Every permutation matrix can be reindexed to the identity.

In particular, the unrestricted Hessenberg-maximizer assertion is equivalent
to MOCIsTrue. It suffices to prove it on dense spectral/directional data,
then pass to a convergent subsequence: the set of reindexed Hessenberg
unitaries is closed (a finite union of closed zero-pattern sets). However,
that generic assertion remains open.

A structurally weaker inductive target is: for every order at least four,
every pair of spectra and every direction, some global support maximizer has
a row or column of degree at most two. At a least failing order, the existing
theorems holds_of_row_degree_le_two and holds_of_column_degree_le_two
give the hull inclusion at that maximizer, contrary to a strict separating
direction. Conversely, MOC gives a permutation maximizer. Hence this
all-order sparse-maximizer target is also equivalent to MOC.

The next two sections sharpen the existing sparse-row argument. They do not
assume MOC in any smaller order.

## 2. Sparse-row elimination for arbitrary entrywise kernels

For an arbitrary complex matrix \(K\), define the polynomial in its entries

\[
\Phi_K(U)=\frac{\det(K\circ U)}{\det U},
\]

where \(\circ\) denotes entrywise multiplication. For the additive kernel
\(K_{ij}=a_i+b_j\), this is \(\det(A+UBU^*)\), since
\((A+UBU^*)U=K\circ U\).

Suppose row \(i\) is supported on \(\{j,k\}\), with \(j\ne k\).
For each nonzero pivot \(U_{ip}\) in this support, delete row \(i\) and
column \(p\). Denote the resulting matrix by \(W_p\). If the other
support column survives, divide it by the complex number \(U_{ip}\).
Call the result \(V_p\). The resulting matrix is unitary by
SparseRow.lean: unitary_normalizedSparseRowMinor. The same fact follows
from column orthogonality: the Gram matrix of \(W_p\) is diagonal with
entries 1 except for the other support column, whose squared norm is
\(|U_{ip}|^2\).

If \(K_{\hat i,\hat p}\) is the kernel with that row and column deleted,
column scaling cancels in the determinant ratio:

\[
\frac{\det(K_{\hat i,\hat p}\circ W_p)}{\det W_p}
=\Phi_{K_{\hat i,\hat p}}(V_p).
\]

The pivot cofactor identity, using \(\operatorname{adj}U=(\det U)U^*\), is

\[
\frac{(-1)^{i+p}U_{ip}\det W_p}{\det U}=|U_{ip}|^2.
\]

Laplace expansion therefore gives the exact arbitrary-kernel recursion

\[
\boxed{\Phi_K(U)=
\sum_{p:U_{ip}\ne0}|U_{ip}|^2K_{ip}
\Phi_{K_{\hat i,\hat p}}(V_p).}\tag{1}
\]

The weights are nonnegative and sum to 1. The degree-one case is the same
with one pivot of modulus one; for order one use the empty determinant 1.
Transposition gives the column version.

### 2.1 Peeling a global maximizer

Let \(U\) be a global maximizer of \(F_\eta\), with a row of degree at most
two. Each branch of (1) for the additive kernel is the determinant of an
actual order-\(n\) relative unitary: use the isolated entry 1 at \((i,p)\),
zeros in the rest of its row and column, and \(V_p\) in the complementary
block. Thus the directional value of each branch is at most the global
maximum \(M\). Their weighted mean equals \(M\). Each branch of positive
weight consequently has value \(M\).

Moreover \(V_p\) is a global support maximizer for the complementary
spectra in direction \(\eta_p=\eta(a_i+b_p)\): if another unitary in this
smaller order improved its support, inserting it in the same isolated
block would improve the original support. This is also valid if
\(\eta_p=0\), when every smaller unitary is a maximizer.

The column version is identical. Thus one can isolate a spectral pair
at a sparse-row or sparse-column maximum, without loss of support and
without assuming any smaller-order conjecture. If such a sparse maximizing
representative exists at each reduced order, induction yields a permutation
maximizer. In orders at most three use the already proved MOC to select a
permutation. This proves the equivalence of the sparse-maximizer target
and the Hessenberg target constructively, via optimal branches.

### 2.2 Preservation of Frobenius ties

Write \(U^{(p)}\) for the isolated-block branch just described and
\(t_p=|U_{ip}|^2\). There is also an entrywise probability identity

\[
|U_{rs}|^2=\sum_p t_p |U^{(p)}_{rs}|^2.
\]

For row \(i\) it is immediate. For any other row and any column outside
the two support columns, each branch leaves the entry unchanged. For
one of the support columns, the branch that isolates it has zero in the
other rows, while the other branch rescales its entries by the inverse
of that branch's pivot. Multiplying their squared moduli by the branch
weight gives the original squared modulus. If the row has degree one,
the isolated branch is the original matrix up to phase.

Since \(G(U)\) is affine in the matrix of squared moduli
(see NormalMaximizerResearch.md, Section 2), it follows that

\[
G(U)=\sum_p t_p G(U^{(p)}).
\]

If \(U\) maximizes both objectives lexicographically, every positive branch
maximizes both, by the same averaging argument as for the determinant.
The smaller Frobenius objective differs from the larger one by the
constant \(|a_i+b_p|^2\), so every complementary branch is also a
lexicographic maximizer for its smaller problem. A sparse lexicographic
maximizer can therefore be peeled without loss in either objective.

## 3. Hessenberg unitaries have a full nonnegative permutation law

Equation (1) is stronger than the additive-kernel result in SparseRow.lean.
For every upper-Hessenberg unitary, the actual complex signed determinant
weights in Weights.lean are nonnegative real numbers:

\[
w_\sigma(U)=\frac{\operatorname{sgn}(\sigma)
\prod_j U_{\sigma(j),j}}{\det U}\ \in\mathbb R_{\ge0}.
\tag{2}
\]

Proof by induction on order. The empty matrix and one-by-one case have
one weight equal to 1. In order \(n\ge2\), the last row is supported
on the last two columns. Each normalized pivot minor is upper Hessenberg:
deleting the last row and one of the last two columns preserves all
required zero positions; scaling a column cannot introduce a nonzero
entry in a zero position. Apply the induction hypothesis to each minor.
By (1), for every kernel \(K\),

\[
\Phi_K(U)=\sum_\sigma \tilde w_\sigma\prod_j K_{\sigma(j),j},
\]

where \(\tilde w_\sigma\) is the pivot probability times the recursively
obtained permutation probability on the remaining labels, or zero if
its pivot was zero. These weights are nonnegative and sum to 1.
Comparing coefficients of the distinct permutation monomials in the
independent entries \(K_{ij}\) with the Leibniz formula gives
\(\tilde w_\sigma=w_\sigma(U)\), proving (2). Independent row/column
permutations only relabel these weights because numerator and
denominator acquire the same permutation signs.

In particular, the normalized signed law itself (not merely an
unspecified law depending on the spectra) simultaneously represents
every entrywise-kernel determinant, all squared-minor marginals
(TwoValues.lean: sum_signedWeight_image_eq_subsetMinorSq), and all
singleton marginals. Therefore it also represents the Frobenius
objective. For every reindexed Hessenberg unitary, the joint vector

\[
\left(\det(A+UBU^*),G(U)\right)
\]

is a convex combination of the corresponding permutation vectors.
This gives a stronger result than MOC for this unitary class.
If a global maximizing unitary is Hessenberg, a permutation in its law
attains the primary maximum. If it also maximizes Frobenius among ties,
a permutation in the law attains both maxima.

The same proof works for any recursively two-supported unitary for which
every positive pivot branch admits such a row or column until order zero.
If only one branch can be recursively peeled, the full-law conclusion
need not follow from this proof; at a global maximum, however, one
recursively peelable branch is enough to select a permutation.

## 4. Exact row and column Givens identities at a global maximum

Let \(U\) be any global support maximizer. Fix two different rows,
with row vectors \(u,v\), and act on them by

\[
R_{\alpha,\beta}=
\begin{pmatrix}\alpha&\beta\\-\bar\beta&\bar\alpha\end{pmatrix},
\quad |\alpha|^2+|\beta|^2=1.
\]

Let \(P\) exchange the two rows. For a pair of row vectors \(x,y\),
let \(D(x,y)\) be the determinant of the additive-kernel weighted
matrix with the chosen two rows replaced by \(x,y\) before entrywise
multiplication, divided by \(\det U\). All other rows stay fixed.
The function \(D\) is complex bilinear (it need not be alternating
in its two vector arguments, since different row weights are used).

Since \(\det R_{\alpha,\beta}=1\),

\[
\begin{aligned}
\det(A+(R_{\alpha,\beta}U)B(R_{\alpha,\beta}U)^*)
={}&|\alpha|^2D(u,v)-|\beta|^2D(v,u)\\
 &-\alpha\bar\beta D(u,u)+\beta\bar\alpha D(v,v).
\end{aligned}
\]

Taking directional real parts gives

\[
F_\eta(R_{\alpha,\beta}U)=
|\alpha|^2 F_\eta(U)+|\beta|^2 F_\eta(PU)
+\operatorname{Re}(\beta\bar\alpha L),
\]
\[
L=\eta D(v,v)-\overline{\eta D(u,u)}.
\]

At a global maximum, first variation in arbitrary complex \(\beta\)
at \((\alpha,\beta)=(1,0)\) gives \(L=0\). More explicitly, if \(L\ne0\),
take \(\beta=t\bar L/|L|\), \(\alpha=\sqrt{1-t^2}\), with small positive
\(t\). The positive term linear in \(t\) exceeds the loss quadratic in
\(t\), a contradiction. Hence the exact identity at a maximizing \(U\) is

\[
\boxed{F_\eta(R_{\alpha,\beta}U)=
F_\eta(U)-|\beta|^2\bigl(F_\eta(U)-F_\eta(PU)\bigr).}\tag{3}
\]

For any fixed pair, either its swap has strictly smaller support, in which
case every rotation with \(\beta\ne0\) loses support, or the swap ties, in
which case every such rotation preserves the maximum. Applying this
argument to the transposed weighted matrix proves the column version.

Choose a maximizing \(U\) with the greatest number of zero entries (the
integer maximum exists, since there are finitely many possible counts).
If two rows have identical supports and their swap ties, choose a rotation
that annihilates one entry in a column of their common support. It
introduces no nonzero entry outside their common support and preserves
the support maximum by (3). The new unitary has strictly more zeros,
a contradiction. Therefore every swap of rows with identical supports
strictly decreases the support. The corresponding assertion holds for
columns. In particular, if this sparsest maximizer is dense, every
nontrivial row swap and every nontrivial column swap strictly decreases
the support.

This is an exact necessary condition for a hypothetical failure, not
a proof that a flat swap exists. There is no unconditional argument that
a single Givens rotation at a maximum can preserve the support while
introducing a zero.

### 4.1 Conditional row-rotation obstruction

Even in a known MOC case, maximizing over the rotation of a fixed pair
of rows can have a dense strict optimizer modulo phases. This rules out
the proposed local elimination algorithm in which each pair can always
be sparsified by optimizing that rotation, independently of the other rows.

For order three let

\[
A=\operatorname{diag}(1,0,0),\quad
B=\operatorname{diag}(1/11,1/8,1/3),\quad \eta=1.
\]

Fix the third row \(w=(1,1,1)/\sqrt3\) and take

\[
u=(-5,4,1)/\sqrt{42},\qquad v=(1,2,-3)/\sqrt{14}
\]

as the first and second rows. These three real vectors are orthonormal
and dense. The matrix determinant lemma gives, for any first row \(x\),

\[
F_1(U)=\det B\left(1+x\operatorname{diag}(11,8,3)x^*\right).
\]

The compression of \(\operatorname{diag}(11,8,3)\) to the span of
\(u,v\) is diagonal in that basis:
\(uDv^*=0\), \(uDu^*=29/3\), \(vDv^*=5\).
Thus within the two-row rotation family the maximum is attained only
when the first row is a scalar phase times \(u\). The second row must
then be a scalar phase times \(v\). No maximizing rotation in this
family introduces any zero. This is a conditional maximum, not a
counterexample to the existence of a global Hessenberg maximizer:
the global maximum is realized by a permutation.

## 5. Residual proof obligation and formalization targets

The substantive unknown is not that a sparse maximum can be peeled;
(1) settles that. It is the existence of a maximizing representative
with at least one degree-two row or column. At a least failing order,
every maximizer for a strictly separating direction has degree at
least three at every row and column, by the existing SparseRow theorem.
In a maximizer of greatest zero count, (3) further forbids flat swaps
between rows or columns of identical support.

The possible proof routes are to exclude all such maximizers by
simultaneous multi-row/column variations, or to find a support-preserving
change not expressible as a single flat two-row or two-column move.

Suggested Lean targets:
* Generalize the existing weighted-entry determinant recursion to arbitrary
  kernels; prove (1) as a public equality, without hull hypotheses.
* Prove nonnegativity of signedWeight for Hessenberg unitaries via recursion
  on permutation terms, or coefficient comparison in a polynomial ring.
* Prove the sparse-support optimal-branch lemma and the Frobenius identity.
* Prove the exact Givens equality (3) and identical-support strictness.

The unrestricted maximizer assertion remains unresolved.

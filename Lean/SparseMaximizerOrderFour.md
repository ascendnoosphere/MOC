# Sparse maximizers: order-four zero-pattern reduction

Status: ordinary mathematical proofs, not yet Lean-checked. This note does
not establish the existence of a sparse global maximum in general.

Let \(A=\operatorname{diag}(a_i)\), \(B=\operatorname{diag}(b_i)\) and
\(F_\eta(U)=\operatorname{Re}(\eta\det(A+UBU^*))\).
Use row-to-column permutations \(p=(p(1),p(2),p(3),p(4))\) in this note,
and \(P_p=\prod_i(a_i+b_{p(i)})\),
\(w_p=\operatorname{sgn}(p)\prod_i U_{i,p(i)}/\det U\).
This is the inverse of the permutation convention in Weights.lean.
The weights sum to one and give the exact signed determinant expansion.

## 1. Four zeros suffice in order four

**Theorem.** Every complex unitary of order four with at least four
zero entries satisfies MOC for every pair of spectra.

If two zeros occur in a common row or column, the degree is at most
two. The already proved SparseRow.lean reduction and order-three theorem
give the inclusion. Otherwise four zeros occupy distinct rows and columns,
and independent permutations put them on the diagonal. If there are any
more zeros, the preceding sparse-row case applies. Thus we need only
consider a zero diagonal and twelve nonzero off-diagonal entries.

In this case the nine derangements are exactly the nonzero signed terms.
If two rows \(r,s\) have exactly two common support columns \(j,k\), row
orthogonality gives

\[
U_{rj}\overline{U_{sj}}+U_{rk}\overline{U_{sk}}=0.
\]

For a permitted assignment \(r\mapsto j,s\mapsto k\), exchanging the
assignments multiplies the signed weight by

\[
-\frac{U_{rk}U_{sj}}{U_{rj}U_{sk}}
=\frac{|U_{sj}|^2}{|U_{sk}|^2}>0.
\]

The analogous exchange rule holds if the two selected columns have exactly
two common support rows, by column orthogonality. In the zero-diagonal case
every pair of rows has exactly two common support columns.

Every four-cycle connects two double transpositions by exchanging the
assignments at either opposite pair of vertices of the cycle. The three
double transpositions are joined in this manner: any two distinct double
transpositions form an alternating four-cycle in the union of their edges,
and a four-cycle connects them. Thus the graph on all nine derangements
with these exchanges is connected. All nine weights are positive multiples
of one nonzero complex number. Their sum is one, so every weight is
positive real. This proves the determinant inclusion for the zero-diagonal
case, in fact with the entire signed law nonnegative. QED.

Consequently, to prove order-four MOC it suffices to find, for every
spectral pair and direction, a global maximizer with either a degree-two
row/column or four zeros in arbitrary positions. This permits the zero
diagonal pattern, which has no degree-two row/column. The two sufficient
conditions (four zeros and a degree-two row) are not logically comparable
for an individual matrix: a degree-two row could have only two zeros
in the entire matrix.

The theorem also holds if the relative eigenbasis is replaced by a real
orthogonal one: FourMinorTransport.lean, four_minor_mixture gives a common
mixture of all squared minors, hence of determinant values. At a global
maximum every positive component is maximizing. Its zero entries include
all zero entries of the original unitary, because singleton squared
minors are nonnegative and averaged. Thus in order four one may always
select a real orthogonal maximizing representative without losing any
existing zero positions.

## 2. Exact three-zero normal form and signed weight obstruction

Suppose a unitary of order four has exactly three zero entries and no
degree-two row or column. They must lie in distinct rows and columns.
Reindex them to positions \((1,1),(2,2),(3,3)\).

**Lemma (real normal form).** Multiplication by diagonal unitary matrices
on the left and right puts the first three rows in the form

\[
R_1=c(0,x,y,1),\quad
R_2=f(z,0,-1/y,1),\quad
R_3=h(-1/z,-1/x,0,1),\qquad x,y,z>0,
\]

where \(c=(1+x^2+y^2)^{-1/2}\),
\(f=(1+z^2+y^{-2})^{-1/2}\), and
\(h=(1+x^{-2}+z^{-2})^{-1/2}\).
The fourth row can be chosen real. Proof: make the fourth entry of each
of the first three rows positive by row phases. Make entries \((1,2)\),
\((1,3)\), \((2,1)\) positive by column phases. Each pair of the first
three rows has exactly two common nonzero positions. Their orthogonality
then determines the remaining entries as negative real numbers, with
the stated ratios. Normalize the rows. The fourth row spans the complex
one-dimensional orthogonal complement of three real independent rows,
so one more row phase makes it real. Diagonal phases do not change the
signed weights, the determinant objective, or the squared minors.

Put \(X=x^2,Y=y^2,Z=z^2,\rho=X/(YZ)\) and

\[
D=(1+X+Y)(1+Z+Y^{-1})(1+X^{-1}+Z^{-1}).
\]

The signed weights of the two permitted three-cycles that fix row four are

\[
w_{2314}=\frac{\rho-1}{D},\qquad
w_{3124}=\frac{\rho^{-1}-1}{D}.
\tag{1}
\]

Indeed, the two products of entries in the upper-left three-by-three
minor are \(cfh\,x/(yz)\) and \(-cfh\,yz/x\).
Their sum is its determinant. By the unitary cofactor identity this
determinant is \((\det U)U_{44}\) for the real representative. Both
three-cycles have positive sign, and substituting the cofactor gives (1).
The fourth entry in row four is zero precisely when \(\rho=1\).
The other three fourth-row entries cannot be zero: before normalization
their cofactors have magnitudes
\((x^2+y^2+1)/(xy)\),
\((y^2z^2+y^2+1)/(yz)\), and
\((x^2z^2+x^2+z^2)/(xz)\).
The same parameterization therefore produces exactly three zeros for
any positive \(X,Y,Z\) with \(\rho\ne1\).

The other nine permitted permutations are derangements. Their weights
are positive, either by the explicit table in Section 4 or the exchange
argument of Section 1: among opposite vertices of a four-cycle, either
the two rows or the two assigned columns both belong to the first three
indices, so orthogonality gives the positive exchange ratio. They are
connected and their weight sum is \(1-|U_{44}|^2>0\).

Thus a unitary with exactly three zeros in distinct rows/columns has
exactly one negative signed weight. The sign is reversed between the two
three-cycles when \(\rho\) passes through 1. At \(\rho=1\) both weights
vanish, and the four-zero theorem applies.

### 2.1 No nonnegative common squared-minor law for this entire pattern

Let \(P_{ij}=|U_{ij}|^2\), and
\(M_{I,J}=|\det U[I,J]|^2\) for two-element row and column sets.
Suppose a probability measure on row-to-column permutations represents
all singleton and pair minors. Since \(P_{11}=P_{22}=P_{33}=0\),
its support must be among the eleven allowed permutations.

For these eleven permutations the following indicator identity holds:

\[
1_{p=2314}
=-1_{p(1)=2}-1_{p(1)=4}
 +1_{p(2)=1}+1_{p(2)=3}
 -1_{p(\{1,2\})=\{1,3\}}
 +1_{p(\{1,3\})=\{1,2\}}.
\tag{2}
\]

It follows by evaluating the right side on the eleven permitted
permutations listed in Section 4: it is one at 2314, zero on the others.
Taking expectations shows that its putative probability at 2314 is

\[
-P_{12}-P_{14}+P_{21}+P_{23}
-M_{\{1,2\},\{1,3\}}+M_{\{1,3\},\{1,2\}}.
\]

The same expression is the actual signed weight, since the signed
determinant weights have precisely these singleton and pair marginals
(TwoValues.lean, sum_signedWeight_image_eq_subsetMinorSq, with inverse
permutation convention). Exchanging labels 2 and 3 on both sides
gives the corresponding identity for 3124. One of these two forced
probabilities is negative by (1). Contradiction. Thus no common
nonnegative full squared-minor law exists for any exactly-three-zero
unitary of this pattern.

This is a limitation of the common-law proof route, not a counterexample
to MOC, which allows the representing probability law to depend on the
given pair of spectra.

### 2.2 A small exact witness

Normalize the rows of the integer matrix

\[
T=\begin{pmatrix}
0&1&1&1\\
2&0&1&-1\\
1&-2&0&2\\
2&2&-3&1
\end{pmatrix}.
\]

Here \(TT^T=\operatorname{diag}(3,6,9,18)\), and \(\det T=-54\).
The normalized matrix is orthogonal with exactly three zeros. Row
normalization cancels in the determinant ratio defining the weights.
Thus \(w_{2314}=-1/54\) and \(w_{3124}=2/27\).

Directly, the right hand side of (2) evaluated on its minor table is

\[
-\frac13-\frac13+\frac23+\frac16-\frac29+\frac1{27}
=-\frac1{54}.
\]

## 3. Sharp bound on the negative signed mass

Let \(\nu=-\min_p w_p>0\) for the exactly-three-zero pattern. By (1),

\[
\nu=\frac{1-\min(\rho,\rho^{-1})}{D}.
\]

Hölder's inequality, grouping the three terms in each factor of \(D\),
gives

\[
D=(1+X+Y)(1+Y^{-1}+Z)(1+Z^{-1}+X^{-1})
\ge(1+\rho^{1/3}+\rho^{-1/3})^3.
\]

Put \(s=\min(\rho,\rho^{-1})^{1/3}\in(0,1)\). Therefore

\[
\nu\le \frac{s^3(1-s)}{(1+s+s^2)^2}.
\]

The derivative of the right side is

\[
-\frac{3s^2(s^2+s-1)}{(1+s+s^2)^3}.
\]

Its maximum is at \(s=(\sqrt5-1)/2\) and equals
\((5\sqrt5-11)/8\). This is attained: take \(X=s\),
\(Y=Z=s^{-1}\), for which Hölder is an equality and \(\rho=s^3\ne1\).
The real normal form yields a unitary with exactly three zeros.
Thus

\[
\boxed{\nu\le(5\sqrt5-11)/8\approx0.022542486}
\]

is sharp. A directional gap from the largest matching value is at
most \(\nu\) times the spread of the matching values in that direction:
if \(s_p=\operatorname{Re}(\eta P_p)\) and \(m=\max_p s_p\), then
\(\sum_p w_p(s_p-m)\le \nu(m-s_{p_-})\).
In addition, replacing the negative weight and the positive weight
of the other three-cycle by their sum on the positive cycle shows
that a violation requires \(s_{p_-}<s_{p_+}\).

## 4. Exact three-variable convex support test

The normal form above gives the complete signed-weight table below.
All weights not listed are zero. Each listed numerator is to be
divided by \(D\). The table follows from the signed Leibniz terms and
the explicit fourth-row cofactors in Section 2: the determinant of
the unnormalized matrix formed by the three displayed rows without
\(c,f,h\) and their cofactor vector is \(D\).

| Permutation (row to column) | \(D w_p\) |
| --- | --- |
| 2143 | \(XZ+X+Z\) |
| 2314 | \(X/(YZ)-1\) |
| 2341 | \(X/Y+1+1/Y\) |
| 2413 | \(X+X/Z+1\) |
| 3124 | \(YZ/X-1\) |
| 3142 | \(YZ+Y+1\) |
| 3412 | \(Y+Y/Z+1/Z\) |
| 3421 | \(1+Y/X+1/X\) |
| 4123 | \(Z+1+Z/X\) |
| 4312 | \(1+1/Z+1/(YZ)\) |
| 4321 | \(1/Y+1/X+1/(XY)\) |

For fixed arbitrary complex spectra and direction let \(m=\max_p s_p\)
over all 24 permutations and \(g_p=m-s_p\ge0\).
The directional hull gap of any unitary in this chart is

\[
D(m-F_\eta(U))=\sum_p g_p D w_p
=C+\sum_{\alpha\ne0} c_\alpha X^{\alpha_1}Y^{\alpha_2}Z^{\alpha_3},
\]

where each \(c_\alpha\ge0\) and

\[
C=g_{2341}+g_{2413}+g_{3142}+g_{3421}
  +g_{4123}+g_{4312}-g_{2314}-g_{3124}.
\tag{3}
\]

Thus \(C\ge0\) is one exact sufficient test for MOC throughout this
three-zero chart. In the remaining case set \(u=\log X\), \(v=\log Y\),
\(w=\log Z\). The function

\[
H(u,v,w)=\sum_{\alpha\ne0}c_\alpha
              \exp(\alpha_1u+\alpha_2v+\alpha_3w)
\]

is convex on \(\mathbb R^3\), because every coefficient is nonnegative.
The directional determinant hull inclusion for every unitary in this
chart holds **if and only if**
\(\inf_{\mathbb R^3} H\ge -C\).
Including \(\rho=1\) in the infimum is legitimate: that surface
already satisfies the hull inclusion by Section 1, and the chart
is continuous. For generic directions with a unique maximizing
permutation, all listed gaps except possibly one are positive.
In particular, the monomials \(X,1/X,Y,1/Y,Z,1/Z\) all have positive
coefficients: each receives contributions from at least two distinct
permutations in the table. Hence \(H\) is coercive and strictly convex,
and the test is equivalent to evaluation at its unique critical point.
For general directions the infimum formulation still holds.

This replaces a nonconvex optimization over unitaries of this pattern
by an exact convex test in three scalar variables. It does not establish
that (3) and this test succeed for every spectral profile, and it does
not cover all zero patterns.

## 5. Flat Givens swaps can exploit an existing zero

Use the Givens identity in HessenbergMaximizerResearch.md. At a global
support maximizer, if exchanging rows \(r,s\) preserves the support,
every unitary rotation of those rows preserves it. Suppose in order
four that there is no degree-two row or column. Every existing zero
is then alone in its row and column. If there is a zero \((i,j)\)
with \(i\notin\{r,s\}\), both \(U_{rj}\) and \(U_{sj}\) are nonzero.
Choose a Givens rotation of rows \(r,s\) that annihilates one of these
entries. The entry \(U_{ij}=0\) is unchanged, so column \(j\) now
has at least two zeros. The new unitary is still a global maximizer.
The same statement holds with rows and columns exchanged.

Therefore at a hypothetical strictly violating order-four maximum:

* there are at most three zeros, in distinct rows and columns;
* any row swap not containing the row of some existing zero must
  strictly lose support, and analogously for columns;
* with three zeros, every nontrivial row and column swap must
  strictly lose support, since no pair can contain all three zeros.

These are necessary conditions, not evidence that a flat swap must
exist. The earlier Givens argument cannot be completed merely by
assuming that a maximizing representative can be chosen with a
nontrivial flat swap.

## 6. Why general squared-minor geometry cannot prove sparsification

The exact three-zero witness also provides a minor-linear objective
for which no degree-two row/column or four-zero matrix can be globally
minimizing. Define

\[
L(U)=-P_{12}-P_{14}+P_{21}+P_{23}
-M_{\{1,2\},\{1,3\}}+M_{\{1,3\},\{1,2\}}
+3(P_{11}+P_{22}+P_{33}).
\]

On a permutation that avoids the first three diagonal positions,
(2) implies \(L\ge0\). On any other permutation, the penalty is at
least 3 and the three negative terms each have magnitude at most one,
so again \(L\ge0\).
At the normalized integer witness \(T\), the penalty vanishes and
\(L=-1/54\).

Every unitary of order four with a degree-two row or column has a
common nonnegative squared-minor law. To see this, use the
arbitrary-kernel sparse-row recursion from HessenbergMaximizerResearch.md.
For each pivot, in order three choose a Birkhoff probability law matching
singleton marginals; complementary minors give all pair marginals, and
empty/full minors agree automatically. Thus for each branch the
determinant identity for additive kernels holds for all spectra with
one law. Combining branches with pivot probabilities yields an
all-spectra probability law for the original unitary. Comparing
coefficients of the independent spectral variables
\(\prod_{i\notin I}a_i\prod_{j\in J}b_j\) gives exactly the full
subset-image marginal law (the coefficient on the determinant
side is the squared minor \(|\det U[I,J]|^2\)). The column case
uses transposition.

A zero-diagonal unitary has a full law by Section 1 and the signed
minor identity. Thus every unitary with either a degree-two row/column
or at least four zeros has \(L\ge0\), whereas the integer witness has
\(L<0\). Compactness shows that any global minimizer of \(L\) has
degree at least three in every row and column and at most three zeros.

This is a counterexample to the analogous sparsification principle for
arbitrary linear functionals of squared minors. It is **not** a
counterexample to the spectral determinant-support principle. The
special rank-two additive structure \(K_{ij}=a_i+b_j\), or equivalent
restrictions on the spectral matching scores, must enter a successful
proof.

## 7. Residual target

To complete the order-four Hessenberg-maximizer conjecture, one must
still prove that some global spectral support maximizer is covered by
the degree-two or four-zero condition, or rule out every violation in
the remaining real orthogonal zero patterns (zero, one, two, or three
zeros in different rows/columns). The three-zero chart admits the
explicit convex test above. Nothing here proves the requisite existence
of a sparse global maximizer in order four or in all orders.

Suggested Lean formalization: first prove the four-zero signed-law
theorem (by the finite derangement exchange graph), then the three-zero
normal form, weight table, and indicator certificate. The existing
order-four real-mixture theorem, SparseRow and signed-minor theorems
supply the required library infrastructure. No Lean declaration has
been added without verification.

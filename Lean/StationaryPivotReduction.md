# Stationary pivot reduction: every zero-containing order-four maximum

Status: mathematical proof, not yet Lean-checked. It strengthens the
three-zero result in StationaryThreeZero.md. The unrestricted order-four
conjecture remains open.

## 1. A stationary affine correction at a real orthogonal pivot

Let \(U\) be a real orthogonal matrix of order four, and let
\(F_\eta(U)=\operatorname{Re}(\eta\det(A+UBU^T))\) with arbitrary complex
diagonal spectra \(A=\operatorname{diag}(a)\), \(B=\operatorname{diag}(b)\).
We use row-to-column permutations \(p\).

Fix a nonzero pivot \(u_j=U_{ij}\), write \(u=U_{i,:}\) for its row and
\(v_r=U_{r,:}\) for every other row \(r\ne i\). Define the real
three-by-three matrix on the complementary row and column labels by
\[
H^{ij}_{rs}
=U_{rs}\left(U_{rs}-\frac{U_{rj}U_{is}}{U_{ij}}\right),
\qquad r\ne i,\ s\ne j.
\tag{1}
\]
Call a pivot admissible when every entry of \(H^{ij}\) is nonnegative.
This is equivalently the entrywise product of the deleted submatrix
with the Schur complement of the pivot. The condition is invariant
under row and column sign changes, permutations, and transposition.

**Stationary pivot theorem.** If \(F_\eta\) is stationary at \(U\) on
the real orthogonal group and \(U\) has an admissible pivot, then
\[
F_\eta(U)\le\max_p\operatorname{Re}(\eta\prod_r(a_r+b_{p(r)})).
\tag{2}
\]

Proof. Let \(u'=e_j/u_j\), \(t=(u'-u)/2\). Since \(u\cdot u'=1\),
\(u\cdot t=0\). The vector \(t\) has expansion
\(t=\sum_{r\ne i} h_r v_r\), \(h_r=t\cdot v_r=U_{rj}/(2u_j)\).
Use the real skew-symmetric tangent that mixes row \(i\) with the
other rows:
\[
\dot u=t,\qquad \dot v_r=-h_r u .
\]
Let \(U(\epsilon)=\exp(\epsilon S)U\) be the corresponding orthogonal
path. For any squared minor \(M_{I,J}(U)=\det U[I,J]^2\), define
its affine first-order correction
\[
\widehat M_{I,J}=M_{I,J}(U)+
\left.\frac{d}{d\epsilon}M_{I,J}(U(\epsilon))\right|_{\epsilon=0}.
\tag{3}
\]
This is a tangent-affine profile, not necessarily the squared minors
of an orthogonal matrix.

For singleton minors the correction is particularly simple:
\[
\widehat M_{\{i\},\{s\}}=u_s u'_s=1_{s=j},
\qquad
\widehat M_{\{r\},\{s\}}=
v_{r,s}(v_{r,s}-U_{rj}u_s/u_j).
\]
The second expression is zero at \(s=j\) and is exactly (1) otherwise.
Every row and column of \(H^{ij}\) sums to one. For example,
\(\sum_{s\ne j}U_{rs}U_{is}=-U_{rj}U_{ij}\) by row
orthogonality. Thus the row sum is
\(1-U_{rj}^2+U_{rj}^2=1\). Column orthogonality similarly
gives the column sums. The admissibility assumption makes \(H^{ij}\)
doubly stochastic.

For a two-minor containing the anchor row \(i\), set
\[
D_{r,st}=u_s v_{r,t}-u_t v_{r,s}.
\]
Its derivative is
\(\dot D_{r,st}=t_s v_{r,t}-t_t v_{r,s}\), because the
\(\dot v_r\) terms cancel. Consequently
\[
\widehat M_{\{i,r\},\{s,t\}}=
(u_s v_{r,t}-u_t v_{r,s})
(u'_s v_{r,t}-u'_t v_{r,s}).
\]
It vanishes if neither column is \(j\); if the column set is
\(\{j,s\}\), its value is \(H^{ij}_{rs}\).
The formula is independent of the ordering of the two columns.

Choose a Birkhoff probability law on permutations between the remaining
three row labels and three column labels with singleton marginals
\(H^{ij}\). Extend each permutation by \(p(i)=j\).
Its singleton and anchored two-subset marginals are exactly the
corrected quantities above. In order four these determine every
squared-minor marginal: unanchored two-subsets are complementary to
anchored two-subsets; three-subsets are complementary to singletons;
empty and full subsets have minor square 1. The complementary-minor
identities hold all along the orthogonal path, so also after the
affine derivative correction (3). Unequal-sized subset minors are
zero by convention.

Finally the determinant expansion in TwoValues.lean,
determinantValue_eq_sum_subsetMinors, is linear in these minor
coordinates for fixed spectra. Its value evaluated on \(\widehat M\)
is \(F_\eta(U)+\dot F_\eta(U)=F_\eta(U)\) by stationarity.
The Birkhoff law just constructed represents \(\widehat M\), hence
represents this stationary directional value by nonnegative weights
on permutations fixing the selected pivot. This proves (2). QED.

The proof does not assert that the original minor table admits a common
nonnegative law. The derivative correction is essential. It works for
any real linear functional of the squared minors, not just spectral
determinant support.

### An exact necessary identity even without admissibility

Without requiring \(H^{ij}\ge0\), the same correction represents the
stationary value by a signed law supported on \(p(i)=j\): any real
matrix with all row/column sums one is an affine combination of
permutation matrices (use a positive uniform doubly stochastic matrix
to move it into the doubly stochastic polytope and subtract the
uniform law). In order three, singleton marginals determine all
subset marginals by complementarity.

In particular, write
\[
c_{ij}=\prod_{r\ne i}a_r+\prod_{s\ne j}b_s,\quad
\alpha_{ir}=\prod_{k\notin\{i,r\}}a_k,\quad
\beta_{js}=\prod_{\ell\notin\{j,s\}}b_\ell .
\]
The matching expansion in order three then gives the exact real identity
at every nonzero pivot of every real stationary point:
\[
F_\eta(U)=\operatorname{Re}\left[
 \eta(a_i+b_j)\left(c_{ij}+
 \sum_{r\ne i,s\ne j}H^{ij}_{rs}
 (\alpha_{ir}b_s+a_r\beta_{js})\right)\right].
\tag{4}
\]
In particular a stationary dense violating maximum cannot have any
cross-sum \(a_i+b_j=0\) with nonzero support. Formula (4) can be used
without forming the full 24-permutation signed law.

## 2. Every real order-four orthogonal matrix with a zero has an admissible pivot

If a row has one or two nonzero entries, an admissible pivot can be
found directly. With one entry it is obvious; with two, orthogonality
forces the two nonzero ratios in each complementary row to have
opposite signs or both be zero. More explicitly, for an anchor row
\(u\) and another row \(v_r\), on the support of \(u\) define
\(R_{rs}=v_{r,s}/u_s\). Equation (1) becomes
\[
H^{ij}_{rs}=u_s^2 R_{rs}(R_{rs}-R_{rj})
\quad(s\in\operatorname{supp}u,\ s\ne j),
\tag{5}
\]
while outside the support it is \(v_{r,s}^2\ge0\).
The orthogonality equation is \(\sum_s u_s^2R_{rs}=0\).
For a two-entry support each nonzero ratio has the sign opposite
to the other, so either pivot is admissible. The column version
follows by transposing.

Suppose now that every row and column has degree at least three,
and some entry is zero. Permute rows/columns and change column signs
so the anchor row is \(u=(0,u_1,u_2,u_3)\) with each \(u_k>0\).
Use indices 0,1,2,3 here (anchor row and zero column both 0).
Set \(p_k=u_k^2>0\).
For each of the three lower rows \(r\), its three ratios \(R_{rk}\)
satisfy \(\sum_{k=1}^3p_kR_{rk}=0\).

### 2.1 Two or more zeros

At most one zero occurs in each row or column. Any other zero
therefore lies in one of the three support columns of the anchor
row. Its lower row has one ratio zero and two nonzero ratios of
opposite sign. This row forbids no pivot by (5). Every other lower
row forbids at most one pivot: with all three ratios nonzero, one
sign occurs twice, and only the ratio of larger absolute magnitude
among that pair can give a negative entry of (5). If the two
magnitudes are equal neither is forbidden. Three candidate pivots
and at most two forbidden positions give an admissible pivot.

### 2.2 Exactly one zero

All nine ratios are nonzero. Independently change the sign of each
lower row so that its three ratios have exactly one negative and
two positive entries. This leaves admissibility invariant. Write
\(m(r)\) for the column of the negative ratio (the minority column).
If any anchor pivot is admissible, the proof is finished.

Otherwise each lower row must forbid exactly one pivot, and the
three forbidden pivot columns must be distinct. Let \(f(r)\) be
this forbidden column: it is the one of the two positive ratios
with strictly larger value. In particular \(R_{r,f(r)}\) is the
strictly largest of all three ratios and \(f(r)\ne m(r)\).
Thus \(f\) is a bijection.

**Claim 1.** The map \(m\) is also a bijection.
Suppose distinct rows \(r,s\) have the same minority column \(k\).
Their forbidden columns are the other two columns, so the third
lower row \(t\) has \(f(t)=k\); \(R_{tk}\) is its strictly
largest ratio. Write \(q_r=U_{r0}\) for the first-column entries
of the lower rows, all nonzero. The projected inner product of
rows \(r,s\) on the last three columns is
\(\sum_\ell p_\ell R_{r\ell}R_{s\ell}>0\), since their ratio
signs agree. Row orthogonality then gives \(q_rq_s<0\).
On the other hand the projected inner product of \(r,t\) is
\[
\sum_{\ell=1}^3p_\ell R_{r\ell}R_{t\ell}
=\sum_{\ell\ne k}p_\ell R_{r\ell}(R_{t\ell}-R_{tk})<0,
\]
using the weighted zero sum of row \(r\).
The same argument for \(s,t\) gives a negative projected
inner product. Hence \(q_rq_t>0\) and \(q_sq_t>0\), contradicting
\(q_rq_s<0\). Claim 1 follows.

**Claim 2.** The three first-column entries \(q_r\) have the same sign.
By orthogonality of the first column and the other columns,
\[
\sum_r q_r R_{rk}=0\quad(k=1,2,3).
\]
If the \(q_r\) have mixed signs, change all three signs in this
equation if needed to arrange exactly one negative, say \(q_r\).
In column \(m(r)\), the ratio in row \(r\) is negative and the
ratios in the other two rows are positive by Claim 1. Every term
in the displayed sum is then positive, a contradiction.

**Claim 3.** Each lower minority position \((r,m(r))\) is admissible.
Use this position as the pivot rather than the original anchor
row. For the original anchor row, its ratio relative to row \(r\)
is negative at \(m(r)\), positive at the other two support columns,
and zero at column 0. These cannot make (1) negative.

For another lower row \(s\ne r\), its ratio relative to row \(r\)
is positive at column 0 by Claim 2 and positive at the one
support column different from \(m(r),m(s)\). At the latter two
minority columns it is negative. It suffices to prove that its
absolute value at pivot \(m(r)\) is at most its absolute value
at \(m(s)\). The two zero-sum row equations give
\[
p_{m(r)}|R_{r,m(r)}|>
 p_{m(s)}R_{r,m(s)},\qquad
p_{m(s)}|R_{s,m(s)}|>
 p_{m(r)}R_{s,m(r)}.
\]
Multiplying and canceling the positive \(p\)'s gives
\[
|R_{r,m(r)}R_{s,m(s)}|>
 R_{r,m(s)}R_{s,m(r)},
\]
which is precisely the required comparison after division by
the positive absolute values of the denominators.
All entries in (1) are nonnegative. This proves Claim 3 and
completes the proof in the exactly-one-zero case. QED.

## 3. Consequence for the full complex unitary orbit

**Theorem.** In order four, for arbitrary complex spectra and any
direction \(\eta\), if some global support maximizer has a zero entry,
then a permutation matrix attains the same maximum.

Proof: apply FourMinorTransport.lean, four_minor_mixture to the
unitary maximizer. This expresses all its squared minors as one
finite convex mixture of real orthogonal minor tables. The
determinant support is linear in the table, so every positive
component is itself a global maximizer on the complex unitary
orbit and therefore stationary on the real orthogonal group.
A zero singleton minor forces the same zero entry in every
positive component. Choose one component. Section 2 supplies
an admissible pivot; Section 1 bounds its support by the largest
permutation score. Permutation matrices are feasible, so equality
holds and a permutation realizes the global maximum. QED.

This reduces the unrestricted order-four conjecture to the
following exact assertion: for any complex spectra and direction,
a global maximizer can be selected with a zero entry or an
admissible real pivot. Equivalently it suffices to exclude strict
violations at dense real orthogonal stationary points for which
every pivot has some negative entry in (1). No existence of such
a sparse or admissible maximizing representative is assumed.

The dense case is not settled by the preceding theorem. The
existence of a common nonnegative law for arbitrary linear
functionals of squared minors is false (Obstruction.lean).
In particular no argument using stationarity alone for arbitrary
minor-linear scores can eliminate all remaining dense points.
One must use the special spectral score in (4) or another
equivalent spectral restriction.

Suggested Lean integration: use the squared-minor complementary
and singleton/pair lemmas from FiniteMinorLaw.lean, Birkhoff from
Weights.lean, the affine correction of an anchored pair-minor,
and the order-four minor mixture in FourMinorTransport.lean.
The proof of existence of an admissible pivot when a zero occurs
is finite sign reasoning and elementary row/column orthogonality.
No unverified Lean declaration is added.

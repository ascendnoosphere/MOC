# Stationary Latin gap inequalities in order four

Status: new ordinary mathematical proofs and exact finite enumeration.
The all-spectra spectral feasibility problem in Section 6 is **not**
proved infeasible. This note does not claim a complete proof of MOC.
No new Lean declaration is added.

This work uses the stationary pivot and dense sign reductions in
StationaryPivotReduction.md and DenseStationaryOrderFour.md, and the
Lean theorem four_minor_mixture in MOC/FourMinorTransport.lean.

## 1. Direct stationary marginal identity, valid in every real order

Use row-to-column permutations. Put \(K_{ij}=a_i+b_j\),
\(A=\operatorname{diag}(a)\), \(B=\operatorname{diag}(b)\), and let
\(U\) be a real orthogonal matrix. Define
\[
C=A+UBU^T,\quad W=K\circ U=CU,\quad
p_\sigma=\prod_iK_{i,\sigma(i)},\quad
s_\sigma=\Re(\eta p_\sigma),\quad
w_\sigma=\frac{\operatorname{sgn}(\sigma)\prod_i U_{i,\sigma(i)}}{\det U}.
\]
Let \(F=\Re(\eta\det C)=\sum_\sigma w_\sigma s_\sigma\).

If \(U\) is stationary on its real orthogonal component, then for every
entry (including zero entries)
\[
\boxed{\sum_{\sigma:\sigma(i)=j} w_\sigma s_\sigma=U_{ij}^2F.}\tag{1}
\]

Proof: differentiate \(\Re(\eta\det(K\circ X)/\det U)\) as a polynomial
in the real matrix entries of \(X\), at \(X=U\). Its real gradient is
\[
G=\Re\bigl(\eta K\circ\operatorname{cof}(W)/\det U\bigr).
\]
Here the cofactor matrix is the transpose of the adjugate. Since \(C\)
is complex symmetric, its adjugate is symmetric, and
\[
\operatorname{cof}(W)=(\det U)\operatorname{adj}(C)U.
\]
This follows from the inverse formula at invertible \(C\), and extends
to singular \(C\) by the polynomial adjugate identity (or continuity).
Using \(UB=(C-A)U\), we obtain
\[
\begin{aligned}
K\circ(\operatorname{adj}(C)U)
 &=A\operatorname{adj}(C)U+\operatorname{adj}(C)UB\\
 &=(\det C\,I+[A,\operatorname{adj}(C)])U.
\end{aligned}
\]
Thus
\[
GU^T=FI+\Re(\eta[A,\operatorname{adj}(C)]).
\]
The second term is real skew-symmetric. Stationarity against every real
skew-symmetric left tangent \(XU\) says \(GU^T\) is symmetric. Therefore
\(G=FU\). Expanding the derivative of the determinant in entry \((i,j)\)
and multiplying by \(U_{ij}\) gives (1), without division by the entry.
QED.

This is an alternative proof of the order-four stationary pivot identity
which needs neither nonsingularity nor the minor complement argument.
It is valid in arbitrary finite real orthogonal order for additive
complex spectra. The stationary identity for complex unitaries requires
a different argument and is not asserted here.

Let \(m=\max_\sigma s_\sigma\), \(g_\sigma=m-s_\sigma\ge0\),
and \(\delta=F-m\). The singleton identity
\(\sum_{\sigma(i)=j}w_\sigma=U_{ij}^2\) now gives
\[
\boxed{\sum_{\sigma(i)=j}w_\sigma g_\sigma
      =-\delta\,U_{ij}^2.}\tag{2}
\]
In particular, at a strictly violating dense stationary point every
one of the sixteen marginal sums is strictly negative.

## 2. Canonical dense sign chamber and its negative Latin set

By the preceding notes, a hypothetical order-four violation has a
dense real orthogonal global maximizer in the one no-admissible-pivot
chamber, after sign changes and reindexing both spectra and eigenbases.

In the notation of DenseStationaryOrderFour.md, multiply rows by
\(L=\operatorname{diag}(1,-1,-1,-1)\) and exchange columns 2 and 3
(indices start at zero). The resulting matrix has determinant +1 and
sign matrix
\[
S=\begin{pmatrix}
+&+&+&+\\-&+&-&+\\-&+&+&-\\-&-&+&+
\end{pmatrix}.
\]
The four negative signed permutations, evaluated by the sign of their
Leibniz monomials, are exactly
\[
N=\{0231,1320,2013,3102\}.
\]
All other twenty signed weights are strictly positive.
These four permutations are pairwise disjoint in matrix positions and
cover all sixteen positions exactly once. They are a coset of the
Klein four subgroup
\[
V_4=\{0123,1032,2301,3210\}.
\]
For each position \((i,j)\) write \(n(i,j)\) for its unique negative
permutation. Equation (2) becomes
\[
|w_{n(i,j)}|g_{n(i,j)}
=\delta U_{ij}^2+
\sum_{\substack{\sigma(i)=j\\\sigma\notin N}}w_\sigma g_\sigma.
\tag{3}
\]
At a strictly violating maximum all four negative-permutation gaps
are therefore strictly positive.

## 3. Latin geometric-mean inequalities and a quantitative bound

Call a set \(L\) of four permutations a Latin set if each matrix
position belongs to exactly one of the four permutations.
For such a set define
\[
G_L=\left(\prod_{\sigma\in L}g_\sigma\right)^{1/4}.
\]
Let \(\mathcal P\) be any partition of \(S_4\setminus N\) into five
Latin sets. There are 13 such partitions; the exact enumeration is
given in Section 7. In particular the five other Klein-four cosets
give one such partition.

**Theorem.** If a dense stationary point in this sign class has
\(\delta>0\), then
\[
\boxed{
G_N\ \ge\ \sum_{L\in\mathcal P}G_L+
\frac{\delta}{c^{1/8}},
\qquad c=\prod_{i,j}|U_{ij}|>0 .
}\tag{4}
\]
Consequently
\[
G_N>\sum_{L\in\mathcal P}G_L,\qquad
0<\delta\le \tfrac14
   \left(G_N-\sum_{L\in\mathcal P}G_L\right).
\tag{5}
\]

Proof: for each \(L\in\mathcal P\) and position \((i,j)\), let
\(x^L_{ij}=w_{\sigma_L(i,j)}g_{\sigma_L(i,j)}\), where
\(\sigma_L(i,j)\) is the unique permutation of \(L\) using that
position. Let \(x^N_{ij}=|w_{n(i,j)}|g_{n(i,j)}\).
All these entries are nonnegative, and (3) states
\(x^N_{ij}=\delta U_{ij}^2+\sum_L x^L_{ij}\).
The geometric mean on 16 nonnegative entries is superadditive, by
generalized Holder:
\[
\left(\prod_{ij}x^N_{ij}\right)^{1/16}
\ge \delta\left(\prod_{ij}U_{ij}^2\right)^{1/16}
+\sum_L\left(\prod_{ij}x^L_{ij}\right)^{1/16}.
\]
Each permutation occurs exactly four times in a Latin set's position
array. Also, for any Latin set,
\(\prod_{\sigma\in L}|w_\sigma|=c\), since its permutations partition
the sixteen entries and \(|\det U|=1\). Thus the left and the terms
in the sum are respectively \(c^{1/4}G_N\) and \(c^{1/4}G_L\).
The first term is \(\delta c^{1/8}\). Divide by \(c^{1/4}>0\).
Finally \(\prod_{j}|U_{ij}|\le(1/4)^2=1/16\) for each row, by AM--GM
on its four squared entries summing to one. Therefore
\(c^{1/8}\le1/4\). This proves (4) and (5). QED.

Taking the maximum over the 13 partitions strengthens (5). One may
further use fractional Latin-set packings: for each positive Latin
set \(L\subset S_4\setminus N\) choose \(\lambda_L\ge0\) with
\(\sum_{L\ni\sigma}\lambda_L\le1\) for every positive permutation.
The same argument gives (4) with
\(\sum_L\lambda_L G_L\) in place of the partition sum, because
the corresponding sum of nonnegative position contributions is
bounded by the positive part of (3). Maximizing this quantity is a
finite linear program in 17 variables.

In the original row/column labels, the negative set of a residual
maximizer is one of the six \(V_4\) cosets because \(V_4\) is normal
in \(S_4\). Thus a spectral-only, computable sufficient condition for
the directional inclusion is:
for every such coset \(N'\), there is a partition of its complement
into Latin sets such that \(G_{N'}\le\sum_L G_L\).
No actual maximizing relative unitary need be computed to use this
test. For arbitrary spectra the same argument gives the nonnegative
upper bound
\[
\max_U F_\eta(U)-m
\le \tfrac14\max_{N'\in S_4/V_4}
\left(G_{N'}-\max_{\mathcal P}\sum_{L\in\mathcal P}G_L\right)_+.
\tag{6}
\]
This conclusion uses the previously proved realification and
no-admissible-pivot reductions. If the support gap is zero it is
immediate; otherwise those reductions place a maximizing real
representative in the required sign chamber.

## 4. Twenty-four additional strict spectral gap inequalities

The minor-sign chamber contains more information than the sign matrix
alone. The four pivots forbidden by three positive-product rectangles
become the four diagonal pivots after the column exchange above;
every off-diagonal pivot is forbidden by exactly one rectangle.
For the off-diagonal pivot \((i,j)\), the unique negative entry in
its complementary singleton matrix \(H^{ij}\) is a diagonal
entry \((k,k)\). The other eight entries are positive.

Fix such a pivot and write \(n\) for its negative three-cycle,
\(t\) for the unique transposition in its six-permutation fiber,
\(c_1,c_2\) for the two four-cycles, and \(e_1,e_2\) for the other
two even permutations (one double transposition and one positive
three-cycle). This is a finite classification verified in Section 7.

Put \(r=|w_n|>0\). The transposition and the negative three-cycle
agree at the off-diagonal pivot and the forbidden diagonal position.
The two four-cycles each agree with the negative three-cycle at
one of its other two off-diagonal positions. The signed conditional
marginal for any two fixed assignments equals the sum of their
two signed permutation weights divided by \(U_{ij}^2\).
Since the complementary singleton signs are as stated, it follows
that
\[
0<w_t<r,\qquad w_{c_1}>r,\qquad w_{c_2}>r .
\]
At a strict violation (3) gives
\[
r g_n>w_{e_1}g_{e_1}+w_{e_2}g_{e_2}
+w_tg_t+w_{c_1}g_{c_1}+w_{c_2}g_{c_2}.
\]
Consequently
\[
\boxed{g_n>g_{c_1}+g_{c_2}.}\tag{7}
\]

In addition, the rank-two additive kernel has zero three-by-three
minor on the complementary labels. Its determinant expansion yields
the alternating fiber identity for the six matching products. Hence
their projected gaps satisfy
\[
g_n+g_{e_1}+g_{e_2}=g_t+g_{c_1}+g_{c_2}.
\]
Substituting in the strict weighted inequality gives
\[
(r-w_t)g_t>
(r+w_{e_1})g_{e_1}+(r+w_{e_2})g_{e_2}
+(w_{c_1}-r)g_{c_1}+(w_{c_2}-r)g_{c_2}.
\]
All terms on the right are nonnegative. Dividing by \(r-w_t>0\)
therefore gives the second strict spectral restriction
\[
\boxed{g_t>g_{e_1}+g_{e_2}.}\tag{8}
\]

Apply (7)--(8) at all twelve off-diagonal pivots. This gives 24
explicit inequalities on the spectral gap vector, without reference
to any unknown unitary entry. In particular no negative three-cycle
or transposition is a maximizing matching. There are only fourteen
possible contact permutations:
\[
0123,\ 0312,\ 1032,\ 1203,\ 1230,\ 1302,\ 2031,\
2130,\ 2301,\ 2310,\ 3012,\ 3021,\ 3201,\ 3210.
\]
The four negative cycles and all six transpositions have strictly
positive gaps.

The product comparison in (4) uses only the additive form of the
determinant's stationary equations and the mixer sign chamber.
The inequalities (8) explicitly use the rank-two kernel restriction.

## 5. Stronger convex necessary condition before eliminating magnitudes

If \(g\) is a candidate spectral gap profile satisfying these conditions,
one can further test whether *any* positive entry-magnitude matrix,
not necessarily orthogonal, can satisfy strict marginal domination.
For a positive matrix \(M\) define \(x_{ij}=\log M_{ij}\) and
\(\ell_\sigma(x)=\sum_i x_{i,\sigma(i)}\).
Since \(g_n>0\) for \(n\in N\), (3) implies
\[
\sum_{\substack{\sigma(i)=j\\\sigma\notin N}}
\frac{g_\sigma}{g_{n(i,j)}}
 \exp\bigl(\ell_\sigma(x)-\ell_{n(i,j)}(x)\bigr)<1
\quad\text{for every }i,j.
\tag{9}
\]
These are sixteen convex inequalities in \(x\). Row and column
additive changes to \(x\) do not affect them; set the first row and
column to zero, leaving nine real unknowns.
Thus infeasibility of this small convex system excludes a spectral
profile regardless of the actual orthogonal mixer. The Latin
geometric-mean inequalities are explicit necessary consequences
of (9). Feasibility of (9) is not sufficient for an actual MOC
counterexample; orthogonality, stationarity, and the spectral
support comparison impose further conditions.

## 6. A finite spectral-only sufficient target for complete order four

It suffices to use support directions normal to hull edges.
Indeed, after an arbitrarily small perturbation of a strict
violation, assume all cross-sums are nonzero, matching products
are distinct, and the matching hull is two-dimensional.
Each excluded equality is a proper real polynomial equation.
For noncollinearity, for example \(a=(0,1,2,3)\),
\(b=(1,i,2,4i)\) give three noncollinear matching values
\(-4+28i,-32+24i,6+33i\).
Strict violation is open, so the perturbation is permissible.
Any point outside a polygon violates at least one edge half-plane.
Choose a corresponding direction and then a global maximizing
unitary. Apply realification and the prior sign reductions.

For two distinct contacts \(p,q\), take the nonzero direction
\[
\eta=\pm i\overline{P_p-P_q}.
\]
Choose the sign for which all matching projections are at most
the contact projection. Here \(P_\sigma\) denotes the complex
matching product. The previous section shows that both contacts
must belong to the fourteen-label list. There are 91 unordered
pairs, each with two possible signs. This removes the independent
support-direction variable.

For generic spectra, use the normalized rank-two chart
\(K_{ij}=1+x_i y_j\), \(x_0=y_0=0,x_1=1\) from
DenseStationaryOrderFour.md. It has five complex free variables.
Row/column rescaling multiplies every determinant and matching
product by the same nonzero complex factor, and edge directions
transform with it. Therefore the above conditions apply in this chart.

For each allowed pair and sign, compute the nonnegative polynomial
gaps
\[
g_\sigma=\Re\left(\eta(P_p-P_\sigma)\right).
\]
Then require all of (7)--(8) and
\[
G_N>\sum_{L\in\mathcal P}G_L
\quad\text{for every one of the 13 partitions}.
\tag{10}
\]
This is a finite spectral-only feasibility test, with ten real
spectral variables. The fourth roots can be introduced as
nonnegative auxiliary variables \(G_L\) with
\(G_L^4=\prod_{\sigma\in L}g_\sigma\).
No Cayley/quaternion or unitary variables occur.
One may add (9) as a stronger filter on any feasible spectral
profile. If every one of these spectral systems is infeasible,
the full order-four conjecture follows.

**Important limitation.** This is a sufficient target, not a
claimed equivalence. A solution of the spectral-only conditions
need not be a determinant violation; the actual orthogonal mixer
conditions were relaxed. No proof of infeasibility is supplied.
The geometric-mean inequality by itself need not exclude all
complex spectral profiles; it must not be promoted to a universal
spectral inequality without a proof.

## 7. Lean verification gap

The negative-set census, Latin partitions, and the 24 conditional inequalities have not been certified in Lean.

## 8. Exact limitation of the geometric-mean condition alone

The strict inequalities (10), without (7)--(8), can in fact hold
for an additive complex spectral profile. Take integer complex
spectra (direction \(\eta=1\)):
\[
a=(-89-75i,-5+7i,-17+99i,-76+24i),\quad
b=(13-3i,5-90i,96+51i,108+135i).
\]
The largest projected matching product is \(32076180\), attained
at permutation 2103. For the negative set \(N\) of Section 2,
\[
G_N\ge126266249,\qquad
\max_{\mathcal P}\sum_{L\in\mathcal P}G_L\le114321308.
\]
These bounds use integer fourth-root lower and upper bounds on the products of four gaps. The numeric certificate has not been checked in Lean.

The maximizing label 2103 is a transposition; it violates (8).
So this example does not satisfy the complete necessary system
and is not a counterexample to MOC. It does establish that an
attempt to prove the geometric-mean inequality in the opposite
direction for all spectral data, without the other constraints,
would be false.

The finite census and the strict spectral target remain Lean verification gaps.

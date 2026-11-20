## Round 041 — The three-by-four matching event polytope has exactly 39 facets

**Status: proved by the exact completeness certificate in Round 042;
floating-point hull computation was used only for discovery.**

A size-two matching between three left vertices and four right vertices
has 36 possibilities. Record its left-pair indicator q^X, right-pair
indicator q^Y, and its three-by-four edge-incidence matrix F. There are
21 coordinates. On their probability affine space impose

\[
\sum q^X=\sum q^Y=1,\qquad
\sum_jF_{ij}=\sum_{k\ne i}q^X_{ik},\qquad
\sum_iF_{ij}=\sum_{l\ne j}q^Y_{jl}.
\]

These identities have eight independent equations, leaving dimension
thirteen, as also proved abstractly in Round 023.

The exact facet description is:

\[
\boxed{
q^X,q^Y,F\ge0,\qquad
1-q^Y_{J^c}-\sum_{j\in J}F_{ij}\ge0
\quad(i=1,2,3,\ |J|=2).
}
\]

There are 21 coordinate inequalities and 18 subset inequalities. Each
is a facet: the matching vertices on its equality hyperplane have exact
affine rank twelve. Their zero-vertex counts are respectively 24 for
the three q^X facets, 30 for the other eighteen coordinate facets, and
18 for each subset facet.

For intuition, the subset inequality says that an outcome matching
whose selected right pair is J^c cannot use any edge in color i and
columns J. On any other outcome, at most one such color-i edge occurs.
The nontrivial assertion is completeness: no more interlaced
inequalities are needed in this particular dimension.

The original numerical hull discovery produced 45,956 triangulated
facets, which collapse to the 39 supporting hyperplanes above. The
subsequent proof does not depend on that floating-point enumeration.

## Round 042 — An exact tangent-cone certificate closes the facet enumeration

**Status: complete exact certificate, independently reproduced.**

Use the following thirteen affine coordinates:

\[
(q^Y_{12},q^Y_{13},q^Y_{14},q^Y_{23},q^Y_{24},
 F_{11},\ldots,F_{14},F_{21},\ldots,F_{24}).
\]

The final right-pair coordinate is one minus the first five. Put
d_j=sum_{k !=j} q^Y_{jk}; then

\[
F_{3j}=d_j-F_{1j}-F_{2j}.
\]

If r_1,r_2 are the first two F-row sums, the left-pair masses are

\[
q^X_{12}=r_1+r_2-1,\quad
q^X_{13}=1-r_2,\quad
q^X_{23}=1-r_1.
\]

Let H be the polytope defined by the 39 inequalities. Nonnegativity and
normalization bound every coordinate, so H is bounded. The 36 matching
points have exact affine rank thirteen. At the matching
{(1,1),(2,2)}, precisely 26 inequalities are active.

The standard exact double-description algorithm was applied to this
thirteen-dimensional tangent cone. Start with thirteen independent
active inequalities, whose inverse is computed with rational arithmetic.
When a new halfspace cuts the cone, retain its nonnegative rays and add
the intersections of the cutting hyperplane with each crossing
two-dimensional face. A face is identified exactly from the incidence
sets of the existing rays. Primitive integer ray coordinates prevent
numerical tolerances.

With the simple canonical ordering, the successive ray counts were

\[
25,52,53,48,45,44,43,41,38,36,34,32,31.
\]

Every one of the final 31 extreme rays points toward a known matching
vertex. For each ray, exact rational ratios verify that its first exit
from H occurs at that known vertex, with parameter exactly one along
the corresponding vertex difference.

The group S_3 x S_4 preserves the 39 inequalities and acts transitively
on the 36 matching vertices. Hence no known vertex has an edge to an
unknown vertex. The vertex graph of a bounded polytope is connected:
for example a generic linear objective supplies an improving edge path
from any nonmaximal vertex to its unique maximizer. Therefore H has no
other vertices. This proves Round 041's completeness.


## Round 043 — The (3,4) coisometry common law is proved

**Status: complete theorem, including a Bell-locality consequence.**

Let X in C^{2 x 3}, Y in C^{2 x 4}, with XX*=YY*=I. Define

\[
q^X_{ik}=|\det[x_i,x_k]|^2,\qquad
q^Y_{jl}=|\det[y_j,y_l]|^2,\qquad
F_{ij}=|\det[x_i,y_j]|^2.
\]

Cauchy–Binet gives the two pure-pair sums equal to one. Its polarized
two-dimensional identity gives the degree relations in Round 041:
sum_j F_ij=||x_i||² and sum_j q^X_ij=||x_i||², and similarly for Y.
All coordinate probabilities are nonnegative.

For a two-element right subset J set K=sum_{j in J} y_jy_j*. Then
0 <= K <= I, and Cauchy–Binet gives

\[
q^Y_{J^c}=\det(I-K).
\]

Write x_i=sqrt(lambda)e_1 in a suitable orthonormal basis, where
0 <= lambda=||x_i||² <=1. Then F_i(J)=lambda K_{22}. Since

\[
\det K\le K_{11},
\]

we obtain

\[
F_i(J)+q^Y_{J^c}
=\lambda K_{22}+1-\operatorname{tr}K+\det K\le1.
\]

The determinant inequality follows directly from 0 <= K <= I or from
the explicit nonnegative expansion in Round 044. All 39 facet
inequalities therefore hold, so the event table has a common matching
law by Round 041.

For arbitrary complex a_1,a_2,a_3 and b_1,...,b_4, Cauchy–Binet gives

\[
\det(XD_aX^*+YD_bY^*)
=\sum_{i<k}q^X_{ik}a_i a_k
 +\sum_{j<l}q^Y_{jl}b_jb_l+\sum_{ij}F_{ij}a_i b_j.
\]

Assign matching {(i,j),(k,l)} the product
(a_i+b_l)(a_k+b_j). Its expansion has precisely these pure-pair and
edge coefficients. Therefore

\[
\boxed{
\det(XD_aX^*+YD_bY^*)
\in\operatorname{conv}
\{(a_i+b_j)(a_k+b_l):i\ne k,\ j\ne l\},
}
\]

with probabilities independent of all spectral values. The same holds
with three and four interchanged.

By Round 021's exact equivalence, the singlet behavior obtained when
both parties use the same two rank-one qubit POVMs with three and four
outcomes is Bell local. This includes arbitrary, party-dependent
postprocessing of outcomes; the complete hidden-variable model,
unlike a same-binning argument, is preserved by all such processing.

## Round 044 — Every support inequality has a three-term qubit positivity certificate

**Status: proved complete certificate template for the (3,4) law.**

The only non-coordinate facet deficit has an especially simple
factorization. In the basis used above write

\[
K=\begin{pmatrix}a&z\\\bar z&b\end{pmatrix},\qquad
\lambda=\|x_i\|^2.
\]

Then

\[
\boxed{
1-F_i(J)-q^Y_{J^c}
=a(1-b)+(1-\lambda)b+|z|^2.
}
\]

Every summand is nonnegative because 0 <= K <= I and 0 <= lambda <=1.
This retains the complex off-diagonal contribution |z|²; no real-frame
restriction is used.

Finite-dimensional polyhedral duality now has a useful consequence.
Every affine functional nonnegative on all 36 matching event vectors
is a nonnegative combination of the 39 facet deficits, modulo the
affine degree identities. Consequently every valid support inequality
for every complex choice of a,b has an exact certificate built from:

1. pure and mixed squared minors;
2. the three nonnegative terms displayed above;
3. the degree and normalization identities.

The nonnegative coefficients of this decomposition can depend on the
chosen support functional. This is a complete dual theorem for this
restricted configuration, whereas the attempted unrestricted MOC
certificate still lacks such a completeness result.

## Round 045 — A positive weight on every matching and an explicit margin parameter

**Status: proved strict version of the new common-law theorem.**

Assume every cross minor F_ij is positive, every two-column minor of Y
is nonzero, and every column of X has squared norm less than one.
The latter condition makes every q^X positive by the three-column
complementary-minor identity. All q^Y and F coordinate facets are also
strict.

For a two-column K from Y, its determinant is positive, so K is
positive definite and b>0 in Round 044. Since lambda<1, the term
(1-lambda)b is positive. Thus all 18 subset facets are strict.

Let r be the event table, let b_0 be the average of all 36 matching
vertices, and let L_k denote the 39 affine facet deficits. Put

\[
\epsilon=
\min\left\{\frac12,\,
\frac12\min_k\frac{L_k(r)}{L_k(b_0)}\right\}>0.
\]

Then

\[
r'={r-\epsilon b_0\over1-\epsilon}
\]

satisfies all facets and hence belongs to the matching polytope.
Decomposing r' into matching vertices gives a decomposition of r
whose weight on every matching is at least epsilon/36.

If the 36 complex product vertices affinely span the plane, the
compressed determinant is in the interior of their hull. This strict
statement supplies the quantitative reserve needed to move the
rank-degeneration theorem to finite normal matrices.

## Round 046 — An exact polynomial at the new five-dimensional boundary

**Status: proved coefficient expansion; no asymptotic remainder.**

In dimension five take

\[
A(t)=\alpha vv^*+tA_1,\qquad
B(t)=\beta_1w_1w_1^*+\beta_2w_2w_2^*+tB_1,
\]

with nonzero alpha,beta_1,beta_2, w_1,w_2 orthonormal, and v,w_1,w_2
independent. The normal small parts annihilate their respective large
spectral subspaces. Put D=A_1+B_1.

Index the three leading vectors by l=1,2,3 with coefficients
gamma_l=(alpha,beta_1,beta_2). For a subset S, let V_S be its frame,
delta_S=det(V_S*V_S), and H_S=(range V_S)^\perp. Use delta_empty=1.
The rank-one update expansion gives

\[
\boxed{
\frac{\det(A(t)+B(t))}{\alpha\beta_1\beta_2\,t^2}
=\sum_{S\subseteq\{1,2,3\}}
t^{3-|S|}
\frac{\delta_S\det(P_{H_S}D|_{H_S})}
     {\prod_{l\notin S}\gamma_l}.
}
\]

To verify it, expand the determinant multilinearly in the three
rank-one leading summands. The term using exactly S has the
Gram determinant delta_S, the product of its selected coefficients,
and the determinant of D on the orthogonal complement. It uses
5-|S| copies of tD.

The constant term after normalization is

\[
\delta_{\{1,2,3\}}
\det(P_H(A_1+B_1)|_H),\qquad \dim H=2.
\]

The projected A-small frame has four columns; the projected B-small
frame has three. Round 043 therefore proves the required leading
convex-hull inclusion. This is the new rank-(1,2) boundary case,
with the roles interchangeable.

## Round 047 — New finite-parameter MOC regions in dimension five

**Status: proved local MOC theorem under explicit strictness assumptions.**

Write the exact normalized determinant from Round 046 as

\[
Z(t)=z_0+t c_1+t^2c_2+t^3c_3.
\]

The separately paired permutation vertices have limits equal to the
36 two-factor products. Permutations pairing a large A eigenvalue with
a large B eigenvalue have limit zero. All normalized vertices are
polynomials of degree at most three.

Under Round 045's strict hypotheses and noncollinearity of the product
vertices, z_0=delta q lies in the interior of

\[
P_0=\operatorname{conv}(0,\text{all two-factor products}).
\]

Here delta=det(V*V)>0; if delta<1, its remaining mass is assigned to
the zero vertex. Let rho=dist(z_0,partial P_0)>0. For k=1,2,3 let L_k
be the maximum absolute value of the t^k coefficient of any normalized
permutation vertex.

Support functions change by at most sum |t|^k L_k, while the actual
point changes by at most sum |t|^k |c_k|. Consequently

\[
\boxed{
\sum_{k=1}^3 |t|^k\bigl(|c_k|+L_k\bigr)<\rho
\quad\Longrightarrow\quad\text{MOC holds at }t.
}
\]

This is an actual finite normal-matrix region, not just a limiting
statement. The zero-margin strata remain outside this proof, and the
interval is not claimed to continue to every t.

## Round 048 — Arbitrarily many parallel refinements inherit the (3,4) law

**Status: proved extension in the number of labeled parents.**

Split a column x_i into parallel columns sqrt(theta_r)x_i with
theta_r>=0 and sum theta_r=1. The compressed spectral matrix replaces
a_i by the affine average sum theta_r a_{i,r}. A size-two matching
uses a projective ray at most once, because minors between parallel
columns vanish.

Apply the coarse (3,4) law to these affine averages. In each product,
independently refine a selected coarse label according to theta.
Affineness in each selected variable gives exactly the original
compressed determinant and nonnegative product weights.

Therefore arbitrary parent counts are allowed when one frame has at
most three projective rays and the other at most four. This is larger
than merely padding a frame with zero columns. It also preserves all
the corresponding pure and mixed minor marginals.

The restriction is on distinct projective rays. This theorem does not assert a reduction for arbitrary convex decompositions into low-outcome POVMs.


## Round 050 — A scalar compression problem reduces to twelve parent rays by preserving its matrices

**Status: proved finite-parent reduction for scalar CMC, not for a universal law.**

For fixed complex spectral values a_i write

\[
XD_aX^*=\sum_i\lambda_i a_iP_i,\qquad
\sum_i\lambda_iP_i=I.
\]

Consider the compact polytope of nonnegative weights w_i satisfying

\[
\sum_iw_iP_i=I,\quad
\sum_iw_i\operatorname{Re}(a_i)P_i
=\operatorname{Re}(XD_aX^*),\quad
\sum_iw_i\operatorname{Im}(a_i)P_i
=\operatorname{Im}(XD_aX^*).
\]

Each Hermitian two-by-two matrix has four real coordinates, so there
are at most twelve independent linear equations. An extreme feasible
weight vector has at most twelve nonzero components. Otherwise its
active columns have a linear dependence, allowing a feasible
two-sided perturbation and contradicting extremality.

The reduced frame is still a coisometry and preserves the compressed
matrix exactly. Repeat for the other frame. Its matching-product
vertex set is a subset of the original one.

Thus proving scalar CMC(2;12,12) would prove scalar CMC(2;m,n) for every
finite m,n. This argument preserves the actual two matrices for the
chosen spectra. It neither preserves every squared minor nor produces
weights independent of a,b. Round 051 improves the bound when only a
separating support value needs to be preserved.

## Round 051 — A minimum-support maximizer improves the scalar bound to eight

**Status: proved, following the root researcher's improvement and checked here.**

Suppose a scalar coisometry example strictly violates its matching
hull in support direction eta. Keep one frame fixed and vary the
other's nonnegative ray weights w under sum w_iP_i=I. Maximize

\[
f(w)=\operatorname{Re}\eta\det
\left(B+\sum_i a_iw_iP_i\right).
\]

The feasible weight polytope is compact. Choose a global maximizer
with minimum support s. On its active face the equality constraints
have rank at most four, so the feasible tangent dimension is at least
s-4.

The real quadratic form Re(eta det Z) on M_2(C) has signature (4,4)
when eta !=0. A real-linear pullback therefore has negative index at
most four. At the chosen maximizer, the Hessian restricted to the
active tangent is negative semidefinite. If its tangent dimension
exceeds four, it has a nonzero null direction.

Stationarity kills the first derivative, and the null direction kills
the second. Since f is quadratic, it is exactly constant along the
entire feasible line. Move to a boundary where one weight disappears,
contradicting minimum support. Hence s<=8.

Repeat for the other frame. The support objective never decreases,
while deleting parent labels only shrinks the comparison hull.
Therefore any strict scalar counterexample has one with at most
eight rays on each side:

\[
\boxed{
\text{scalar CMC}(2;8,8)
\Longrightarrow\text{scalar CMC}(2;m,n)\text{ for all }m,n.
}
\]

This is a counterexample-reduction theorem. It does not preserve the
original compressed matrices, and it does not extend to the
spectrum-independent common law.

## Round 052 — Real ray configurations reduce further to six parents per side

**Status: proved sharpening of the scalar reduction.**

If all rays of a frame can be made real by a common unitary change of
basis, their projectors lie in the three-dimensional real space
Sym_2(R). The coisometry weight constraints therefore have rank at
most three.

The varying compressed matrix lies in an affine translate of
Sym_2(C). On this complex three-dimensional space, the determinant
quadratic form is nondegenerate; Re(eta det) has real signature (3,3).
The minimum-support argument of Round 051 now gives

\[
s\le3+3=6
\]

for that side. Thus the scalar problem for two real ray configurations
reduces to (6,6). If just one side is real, that side can be reduced to
six and the other to eight.

The fixed matrix from the other frame can be arbitrary complex:
it contributes only linear and constant terms to the quadratic
weight objective, so it does not change the Hessian-index bound.

## Round 053 — Collinear spectral values give direction-dependent bounds of seven, five, or four

**Status: proved further scalar support reduction.**

Suppose a_i=s+t r_i with r_i real. On the coisometry constraint
sum w_iP_i=I, the s-part is fixed. Along a feasible weight variation d,
the quadratic part of the determinant support is

\[
\operatorname{Re}(\eta t^2)\,
\det\left(\sum_i r_i d_iP_i\right).
\]

The determinant on Herm_2(C) has Lorentz signature (1,3): in scalar
and Pauli coordinates it is x_0²-x_1²-x_2²-x_3². Put
g=Re(eta t²). Its negative index is at most three when g>0, at most
one when g<0, and zero when g=0.

Adding the at-most-four independent coisometry constraints to the
minimum-support argument yields bounds

\[
\boxed{
s\le7\ (g>0),\qquad
s\le5\ (g<0),\qquad
s\le4\ (g=0).
}
\]

When g=0 the objective is affine on the weight fiber, so the
four-support conclusion is ordinary linear optimization. These are
support-direction reductions, not a theorem that every compressed
matrix with collinear parent spectra is normal after combining the
two frames.

## Round 054 — The exact rank-three scalar target behind MOC4

**Status: proved reformulation, consistent with the earlier CH equivalence.**

Let C=U diag(beta)U*, retain rows I={1,2,4}, and set
Y=U[I,:]. Then YY*=I_3. The coefficient-hull projection is exactly

\[
D_0+tD_1
=\det\bigl(Y\operatorname{diag}(\beta)Y^*
          +\operatorname{diag}(0,1,t)\bigr).
\]

Expanding in the last two diagonal entries gives

\[
\det C[I]+\det C[\{1,4\}]
+t\bigl(\det C[\{1,2\}]+C_{11}\bigr),
\]

which is the displayed D_0+tD_1 from the prior report.

Thus the missing scalar assertion is CMC(3;3,4): one parent frame is
the square identity and the other is a three-by-four coisometry.
Its comparison vertices are products over injections of three
selected beta labels. General triples of the first spectral values
reduce affinely to (0,1,t), with repeated cases handled by continuity.

The previous coefficient-hull argument shows this scalar assertion
is equivalent to MOC4. The new rank-two theorem establishes a
boundary and lower-rank input for this target, but raising the
compression rank from two to three requires a new scalar gluing
argument.


## Round 056 — A row supported on at most two columns has a full common law in dimension four

**Status: proved sparse-row family, using cross-block gluing.**

Let U in U(4) have a row supported on at most two columns. Choose a
two-column unitary G sending that row to a coordinate vector. Then
UG* has a one-dimensional isolated block and a three-by-three unitary
block V, after row and column permutations and harmless phases.

Every V in U(3) has a full common-minor law. Indeed a Birkhoff
decomposition of |V|² matches the one-by-one minors, and its
two-by-two minors are the complementary one-by-one minors, so the
same permutation probabilities match them too.

Thus UG* has a block-product law. Multiplying back by G mixes one
column from the one-dimensional block with one column from the
three-dimensional block. The column version of the proved
cross-block gluing theorem splits that law into two positive
relabelings.

Therefore U has a spectrum-independent common law. More generally,
the same argument works in dimension n whenever the remaining
(n-1)-dimensional block has such a law.

This includes an omitted row with support one or two, but it makes
no assertion for a row with three or four nonzero entries.

## Round 057 — Weighted one-omission CH holds for every two-valued beta spectrum

**Status: proved scalar coefficient-hull theorem preserving the prescribed omission marginal.**

Suppose beta has at most two distinct values. Within each equal-value
eigenspace, rotate the columns of U so that the omitted row has at
most one nonzero entry in that spectral class. This leaves
C=U diag(beta)U* unchanged. The modified unitary has omitted-row
support at most two, so Round 056 supplies a full common law.

Let G be an equal-beta class. The conditional coefficient hulls P_j
are identical for all j in G: permuting identical spectral labels
does not change any coefficient vertex. The modified omitted-row
probability is concentrated on one representative j_G with total

\[
w_G=\sum_{j\in G}|u_{3j}|^2.
\]

For every permutation in the resulting law that omits class G,
randomly relabel its equal-beta columns so that the representative
j_G is sent to j with probability |u_{3j}|²/w_G. Complete this to a
bijection on the other labels in G. The coefficient product remains
unchanged, while the original omitted-row probabilities are
recovered exactly. Classes of total weight zero need no division.

Hence

\[
\boxed{
(D_0,D_1)\in\sum_j |u_{3j}|^2P_j
\quad\text{for every two-valued beta and every }U\in U(4).
}
\]

The weights depend on beta and U; no false positive operator
decomposition is used. This extends the list of completed weighted
one-omission CH families beyond the previously established square
spectrum, though it does not settle general beta.

## Round 058 — An explicit open weighted-CH region with genuinely complex spectra

**Status: proved strict example and a neighborhood theorem.**

Take beta=(1,2,i,3+i). Let the omitted row of U be the fourth column's
coordinate vector, and let the retained three-by-three block have
flat squared moduli, for example a three-dimensional Fourier matrix.
Its common law may be the uniform distribution on all six
permutations. The omitted-row marginal is concentrated on label 4.

The six vertices of P_4 are, in (v_0,v_1) coordinates,

\[
(3i,3),\ (2+2i,1+i),\ (4i,4),\
(2+2i,2+2i),\ (4i,2i),\ (3i,3i).
\]

The first five are affinely independent over the reals: the
four-by-four difference determinant in
(Re v_0,Im v_0,Re v_1,Im v_1) coordinates equals twelve.
The uniform barycenter is

\[
z_*=\left(\frac23+3i,\ \frac53+\frac43i\right).
\]

It is therefore in the interior of P_4. Let
rho=dist(z_*,partial P_4)>0.

For perturbed beta',U', every conditional hull vertex and every
omission probability vary continuously. Quantitatively, put
delta_V=max_pi ||v'_pi-v_pi||, M=max_pi||v_pi||, and
delta_p=sum_j|p'_j-p_j|. The weighted support functions move by at
most delta_V+M delta_p. Thus

\[
\|z'-z_*\|+\delta_V+M\delta_p<\rho
\]

implies the weighted CH inclusion for the perturbed data.

This proves an open family allowing full-support nearby unitaries
and four distinct generic complex beta values. Its construction
starts from a reducible point with a strict coefficient margin, not
from a claim that perturbations preserve a universal minor law.

## Round 059 — The unrestricted CH support test reduces to four tied coefficient vertices

**Status: proved finite-facet meta-reduction in the full-dimensional case.**

Fix beta and suppose P=conv{v_pi} has real affine dimension four.
Checking CH requires only the facet support inequalities of this
four-dimensional polytope. Every facet contains at least four
affinely independent vertices. Thus arbitrary planar support
directions in the determinant plane need not be treated separately
once the complete coefficient vector is retained.

For four candidate tied permutations pi_0,...,pi_3, put
d_k=v_{pi_k}-v_{pi_0} in R^4. If the three differences are
independent, their exterior product gives a normal

\[
N=*(d_1\wedge d_2\wedge d_3).
\]

Choose its sign and check

\[
N\cdot(v_\pi-v_{\pi_0})\le0
\quad\text{for all 24 permutations}.
\]

When those inequalities hold, the corresponding proof obligation is
the single actual-unitary inequality

\[
N\cdot\bigl((D_0,D_1)-v_{\pi_0}\bigr)\le0.
\]

The coordinates of each v are real polynomials in Re beta,Im beta,
of degree at most three. Therefore N can be chosen polynomial of
degree at most nine, and the resulting support deficit has degree
at most twelve in the spectral coordinates before the unitary
moment variables are inserted.

There are at most C(24,4)=10,626 candidate four-vertex sets, with
invalid support orientations rejected by the remaining vertices.
Degenerate affine dimensions require their own lower-dimensional
version or continuity; they cannot simply be assumed generic.

For the weighted omission hull, the analogous facets belong to a
Minkowski sum of conditional hulls. Their tied faces may be spread
across different omission classes. One cannot replace that weighted
facet condition by four vertices tied at one global unweighted
support value.

## Round 060 — The matching polytope's vertex graph is classified for all (3,n)

**Status: proved graph structure for the true matching polytope; the
general subset-facet completeness step remains open here.**

At the base matching

\[
M_0=\{(1,1),(2,2)\},
\]

there are 6 C(n,2)-1 other vertices. Exactly 2(n-2) are nonneighbors:

\[
\{(1,j),(3,2)\},\qquad
\{(2,j),(3,1)\},\qquad j=3,\ldots,n.
\]

For the first type there is an exact rectangle relation between event
vectors:

\[
v_{\{(1,1),(2,2)\}}+
v_{\{(1,j),(3,2)\}}
=
v_{\{(1,1),(3,2)\}}+
v_{\{(1,j),(2,2)\}}.
\]

The two diagonal segments meet in their relative interiors, so the
first pair cannot form an edge. The second type is symmetric.

For any other candidate matching, set every nonnegative q^X,q^Y,F
coordinate outside the union of its support and M_0's support to zero.
The resulting face can use only the two original left pairs, the
two original right pairs, and the at-most-four original edges.
A case split on whether the two right pairs intersect in zero, one,
or two vertices leaves only the two given matchings, except for the
rectangle configurations just listed. Hence every other pair is an
edge.

The vertex degree is therefore

\[
\boxed{6{n\choose2}-1-2(n-2)=3n^2-5n+3.}
\]

This predicts 31,53,81 neighbors for n=4,5,6. The independent
reviewer subsequently certified the full subset-facet description
for (3,5) and (3,6), obtaining exactly 53 and 81 tangent rays by
exact arithmetic. Those extensions are recorded in the reviewer's
log and are not claimed as independent computations by this agent.

A possible general proof is now sharply localized: show that the
polyhedron defined by positivity and all single-color subset cuts
has no extra tangent rays at M_0 beyond the known edges above.
Every known edge involves at most four right columns. A theorem
localizing every extreme tangent ray to four columns would combine
with Round 042 to prove all (3,n) common laws. Such a localization
theorem was not obtained in this batch.


## Round 011 — An explicit finite-parameter MOC region near the compression boundary

**Status: proved local interior theorem, jointly developed with the independent
reviewer; a full unrestricted continuation is not obtained.**

Continue Round 009:
\[
A(t)=\alpha vv^*+tA_1,\quad
B(t)=\beta ww^*+tB_1,\quad
D=A_1+B_1,\quad
\delta=1-|v^*w|^2>0,
\]
where alpha beta !=0, v,w are independent unit vectors in C^4, and the two
normal small parts kill v,w respectively. Let H=(span(v,w))-perp and
\[
q=\det(P_HD|_H).
\]
The exact normalized determinant is a quadratic polynomial:
\[
\boxed{
Z(t)=\frac{\det(A(t)+B(t))}{\alpha\beta t^2}
=\delta q+t r+t^2s,
}
\]
where
\[
r=\frac{v^*\operatorname{adj}(D)v}{\beta}
 +\frac{w^*\operatorname{adj}(D)w}{\alpha},
\qquad
s=\frac{\det D}{\alpha\beta}.
\]
Indeed the constant and linear coefficients of det(C_0+tD) vanish because
C_0=alpha vv*+beta ww* has rank two. Its t^2 coefficient was computed in
Round 009; its t^3 coefficient is tr(adj(D)C_0), and the t^4 coefficient
is det D. No infinite remainder remains in this dimension.

Let the small spectra be a_1,a_2,a_3 and b_1,b_2,b_3. Every separately
paired normalized permutation vertex is exactly
\[
V\left[
1+t\left(\frac{b_j}{\alpha}+\frac{a_i}{\beta}\right)
+t^2\frac{a_i b_j}{\alpha\beta}
\right],
\]
where V is the two-factor product from the remaining indices. A vertex
pairing the two large eigenvalues together is exactly
\[
t\frac{\alpha+\beta}{\alpha\beta}
\prod_{k=1}^3(a_k+b_{\pi(k)}).
\]
Let P_0 be the convex hull of zero and the 18 two-factor products.

The reviewer observed a useful strict version of Round 008. If all
F_ij=|det[x_i,y_j]|^2 are positive and all columns of X,Y have squared
norm strictly less than one, then F is in the relative interior of the
size-two K_3,3 matching polytope. Subtract a sufficiently small multiple
of its uniform barycenter, then decompose the remainder. This produces
a matching law assigning positive weight to every one of the 18
matchings. If the product vertices affinely span C, q is therefore in
the interior of their hull. Since delta>0, delta q is in the interior of
P_0 even when delta<1.

Put
\[
\rho=\operatorname{dist}(\delta q,\partial P_0)>0.
\]
Let L_1,L_2 be the maximum absolute values of the linear and quadratic
coefficients, respectively, among all 24 normalized vertices just
listed. Then every unit support direction loses at most
|t|L_1+|t|^2L_2 under the vertex perturbation. The actual point moves by
at most |t||r|+|t|^2|s|. Consequently
\[
\boxed{
|t|(|r|+L_1)+|t|^2(|s|+L_2)<\rho
\quad\Longrightarrow\quad
Z(t)\in P_t.
}
\]
This is an explicit finite-t MOC interval, not only an asymptotic
statement. If B=|s|+L_2>0 and A=|r|+L_1, a sufficient radius is
\[
|t|<\frac{2\rho}{A+\sqrt{A^2+4B\rho}}.
\]
When B=0 use rho/A, with the evident constant case if A also vanishes.

The exact remaining difficulty is the zero-margin strata: failure of
strict cross-minor positivity, a saturated column norm, or collinear
product vertices can leave rho=0. The local theorem makes no claim
there, and its interval need not extend to t=1.


## Round 013 — The arbitrary-parent compression problem has a precise transport dual

**Status: exact equivalence for the stronger common-coefficient law;
universal feasibility for arbitrary parent counts remains open.**

Let X:C^m->C^2 and Y:C^n->C^2 be coisometries. Define
\[
q^X_{ik}=|\det[x_i,x_k]|^2,\quad
q^Y_{jl}=|\det[y_j,y_l]|^2,\quad
F_{ij}=|\det[x_i,y_j]|^2.
\]
A spectrum-independent coefficient law is equivalent to a probability
distribution on size-two bipartite matchings with:

* left selected-pair marginal q^X;
* right selected-pair marginal q^Y;
* edge marginal F.

The correspondence uses the opposite matching for the product vertex,
as in Round 008, so that the edge marginal matches the mixed monomials.

There are 2 binom(m,2) binom(n,2) nonnegative variables. Finite-dimensional
duality says the law exists exactly when every real array (u_I,v_J,c_ij)
satisfying
\[
u_{\{i,k\}}+v_{\{j,l\}}+c_{ij}+c_{kl}\ge0,
\]
\[
u_{\{i,k\}}+v_{\{j,l\}}+c_{il}+c_{kj}\ge0
\]
for distinct indices also satisfies
\[
\boxed{
\sum_Iu_Iq^X_I+\sum_Jv_Jq^Y_J+\sum_{ij}c_{ij}F_{ij}\ge0.
}
\]
Thus a smallest obstruction can be certified by a finite matching cost,
then substituted into rank-two Gram identities. This is a genuine
stronger target: an obstruction to it need not be a separating actual
spectral cost.

For three parents on both sides, the pure pair marginals are forced by
single-index degrees, which is why Round 008 closes. Once a side has
four parents its pair probabilities contain independent information.
The general dual above records that information rather than replacing
it with singleton marginals.

## Round 014 — One two-parent side allows arbitrarily many parents on the other

**Status: proved positive theorem by an exact orientation flow.**

Suppose X is two-by-two unitary and Y is a two-by-n coisometry, with any
n>=2. Then for arbitrary complex a_1,a_2 and b_1,...,b_n,
\[
\boxed{
\det(XD_aX^*+YD_bY^*)
\in\operatorname{conv}_{j\ne l}
\{(a_1+b_j)(a_2+b_l)\}.
}
\]
The law again can be chosen independently of the spectral values.

Write q_jl=|det[y_j,y_l]|^2. Select the unordered b-pair with this law,
and seek an orientation assigning one selected endpoint to cross slot 1
with prescribed mass d_j=F_1j. Since x_1,x_2 are orthonormal,
\[
d_j=|x_2^*y_j|^2,\qquad \sum_jd_j=1.
\]
The fractional orientation problem for a weighted graph is feasible
exactly when, for every vertex subset S,
\[
\sum_{j\in S}d_j\ge\sum_{\{j,l\}\subset S}q_{jl},
\]
together with equality of total masses. This follows by the ordinary
max-flow/min-cut criterion applied to pair nodes sending their weight
to one of their two endpoints.

Let M_S=sum_{j in S} y_jy_j*. Then 0<=M_S<=I and Cauchy–Binet gives
\[
\sum_{\{j,l\}\subset S}q_{jl}=\det M_S.
\]
If its eigenvalues are lambda_1,lambda_2 in [0,1], then
det M_S<=min(lambda_1,lambda_2)<=x_2*M_Sx_2. Hence every required cut
inequality holds.

The complementary slot has the correct marginal because
\[
\sum_{l\ne j}q_{jl}=\|y_j\|^2=F_{1j}+F_{2j}.
\]
The selected b-pair has its required determinant coefficient, the
a-pair is fixed, and both mixed coefficients match. This proves the
theorem through the same Cauchy–Binet expansion as Round 008.

This settles a broader compression class than merely two-by-three on
the unrestricted side. The next unresolved parent configuration for
this common-coefficient route is (3,4).

## Round 015 — Parallel-column refinement preserves every compression law

**Status: proved closure operation extending the positive classes.**

Suppose a column x of a coisometry is replaced by parallel columns
\[
x_r=\sqrt{\theta_r}\,x,\qquad
\theta_r\ge0,\quad\sum_r\theta_r=1.
\]
The coisometry identity is preserved. In the compressed matrix these
columns contribute
\[
\sum_ra_r x_rx_r^*
=\left(\sum_r\theta_ra_r\right)xx^*.
\]
Thus the coarse spectrum uses the effective eigenvalue
bar a=sum theta_r a_r.

A valid product vertex selects a given coarse direction at most once.
Its dependence on bar a is therefore affine. Replace that occurrence
by a randomly selected a_r with probabilities theta_r. This expands
the coarse law into a nonnegative normalized fine law with exact
determinant value. If two fine columns from the same class were
selected together their pure determinant coefficient would be zero,
consistent with the construction.

Refine the two frames independently and repeat. Therefore:

* if each frame has at most three distinct projective column directions,
  Round 008 proves its law for arbitrarily many parallel copies;
* if one frame has at most two projective directions, Round 014 permits
  arbitrarily many directions and parents on the other side.

This operation is not a convex decomposition into arbitrary POVMs.
General mixing of coisometries would alter the quadratic pure-pair
coefficients, which is exactly the information the proof must preserve.

## Round 016 — Strict commuting support maxima are stable under spectral perturbation

**Status: proved conditional interior principle; a global family satisfying
all hypotheses has not been established in this round.**

Work on the compact flag manifold U(n)/T for simple ordered spectra;
right diagonal phases do not change the orbit point. Left diagonal phases
also leave the determinant unchanged, and fix each permutation flag.
Fix spectra a^0,b^0 and a support direction eta^0. Suppose:

1. every global support maximum is one of finitely many permutation points;
2. at each maximizing permutation the support Hessian is strictly negative
   on the flag tangent space.

Then the same support inequality is true for all sufficiently small
perturbations of the spectra and support direction, with the maximum
still attained at a permutation.

Proof: select disjoint neighborhoods of the finitely many maxima. Outside
them compactness gives a positive support gap. Inside each neighborhood,
strict negative Hessian and continuity give strict concavity in a small
coordinate chart. A permutation remains stationary for every spectral
perturbation: the first determinant variation along off-diagonal
commutators vanishes at diagonal A+B. Hence the unique critical maximum
in that chart remains exactly the permutation point rather than moving
to a noncommuting point. The exterior support gap also persists.

At a permutation pi, each two-row fiber Hessian is controlled exactly by
\[
\operatorname{Re}\eta(z_\pi-z_{\pi\circ(ij)}).
\]
Strict positivity of all these transposition gaps gives the necessary
rootwise strictness; at the commuting point the torus symmetry removes
cross-root quadratic terms, so it also gives transverse negative
definiteness.

This principle supplies a possible open-set strategy once the global
maximizer classification is known. It does not automatically cover
directions normal to an exposed transposition segment, where a Hessian
root gap vanishes. Those directions require a genuine Morse–Bott or
higher-order analysis. The quantitative theorem in Round 011 avoids
this obstruction by using an actual interior margin for a fixed orbit.

## Round 017 — Simultaneous ellipse optimality is globally decisive in rank one

**Status: proved exact terminal classification for a base spectral class.**

If B=b_0I+delta vv*, ||v||=1, then
\[
\det(A+B)
=\det(A+b_0I)
+\delta\sum_i|v_i|^2
\prod_{k\ne i}(a_k+b_0).
\]
No invertibility assumption is needed. For a support direction eta this
is a constant plus sum_i gamma_i |v_i|^2, with explicit real gamma_i.

If v is optimal on every two-coordinate unitary fiber, then every
nonzero coordinate v_i must satisfy gamma_i=max_j gamma_j. Otherwise
rotate its mass into a larger coefficient and strictly increase the
support. Conversely any vector supported on the maximal-coefficient
set is globally optimal.

Thus the pairwise-ellipse ascent of Round 004 has no spurious terminal
support levels in this class. All maximum values are permutation
values, including the cases of a tied support face. This pinpoints the
step that must be generalized: with two or more active spectral
directions, the pairwise fiber coefficients depend on the rest of the
unitary and no longer form one fixed scalar score vector.

## Round 018 — The rank-two Hadamard operator has explicit stochastic weight blocks

**Status: proved representation identity; product-witness domination remains
the substantive unresolved inequality.**

For H_ij=a_i+b_j,
\[
\det(H\circ U)=\det(AU+UB)
=\det U\,\det(A+UBU^*).
\]
More generally any rank-two matrix H can be written H_ij=x_i^T y_j for
two-component vectors. Let
\[
c_\pi=\frac{\operatorname{sgn}(\pi)\prod_iU_{i,\pi(i)}}{\det U},
\qquad
K_U=\sum_\pi c_\pi P_\pi
\]
on (C^2) tensor-power n, with consistent permutation convention.
The determinant ratio is a product-bra/product-ket matrix element of
K_U, while each permutation product is the same matrix element of P_pi.

There is a particularly concrete description of K_U. Label a binary
basis vector by its set S of ones. Matrix elements vanish between
different weights. On weight k, collecting the determinant expansion
over permutations mapping T to S gives
\[
(K_U)_{S,T}
=
\frac{\pm\det U[S,T]\det U[S^c,T^c]}{\det U}
=|\det U[S,T]|^2,
\]
by the complementary-minor identity for a unitary matrix.
Thus
\[
\boxed{K_U=\bigoplus_{k=0}^n |\wedge^kU|^{\circ2}.}
\]
Every displayed block is real nonnegative and doubly stochastic.
Moreover K_U belongs to the permutation algebra and commutes with the
collective GL(2) action.

For n=4 the relevant permutation-algebra quotient has dimension
1^2+3^2+2^2=14, corresponding to partitions (4),(3,1),(2,2).
The entries of the five weight blocks obey this common representation
constraint, not independent Birkhoff decompositions.

The false full common-minor law would assert K_U is in the convex hull
of the P_pi as an operator. MOC only tests a highly structured subset
of linear functionals: the real parts of product-bra/product-ket
matrix elements. A generic operator separator cannot be substituted
for one of these without proving a product-witness realization.
The stochastic description explains why individual grades are easy
and why their simultaneous product test is the remaining issue.

## Round 019 — Exact Givens twirling matches permutation averaging

**Status: proved averaging identity; reverse martingale construction remains
unproved.**

For an arbitrary starting U, average det(A+gUBU*g*) over Haar g in a
fixed two-coordinate unitary subgroup. Round 003 writes that fiber as
c+delta x*Tx. Haar averaging gives xx*=I/2 in expectation. Therefore
\[
\boxed{
\mathbb E_g\,\det(A+gUBU^*g^*)
=\frac12\left[
\det(A+UBU^*)+
\det(A+P_{ij}UBU^*P_{ij}^*)
\right].
}
\]
In words, for this particular determinant observable, a continuous
two-row twirl has exactly the same mean as choosing identity or the
row transposition with equal probability.

Iterating independent twirls yields the same expected determinant as
the corresponding random transposition walk applied to the starting
matrix. Averaging over the full unitary group eventually gives the
uniform average of the permutation products. This last equality can
also be checked directly by uniform compound moments.

The identity is not a positive representation of the starting value.
It averages away information; reversing a Markov averaging operation
does not preserve positivity. A possible proof would require a
different process whose determinant is a martingale and whose terminal
distribution is supported on permutations. This round establishes
the exact local averaging relation such a process must respect, while
leaving the positive reverse construction open.

## Round 020 — Determinant-preserving reflections on each Bloch sphere

**Status: proved local transformation; a global rounding descent is open.**

In the generic two-row fiber of Round 003 write
\[
f(n)=c_0+\ell\cdot n,\qquad n\in S^2,\quad \ell\in C^3.
\]
Let a=Re ell, b=Im ell and suppose a,b are linearly independent. Put
\[
k=\frac{a\times b}{\|a\times b\|}.
\]
The ordinary reflection
\[
\boxed{n'=n-2(n\cdot k)k}
\]
preserves the sphere and exactly preserves the complex determinant:
ell dot n'=ell dot n. Every unit Bloch vector has a corresponding
two-row unitary, so this is an actual local move on the unitary orbit.

The reflection exchanges the two preimages of an interior ellipse
point. It fixes exactly the preimage circle mapping to the ellipse
boundary, where n dot k=0. If the fiber degenerates to a segment,
the kernel has dimension two and there is instead a continuous
circle of determinant-preserving moves at interior values.

This creates a concrete rounding mechanism worth pursuing: compose
determinant-preserving moves while trying to maximize a sparsity
functional or reach a fiber degeneracy that reduces dimension.
The algebraic formula guarantees preservation of the target value;
it does not guarantee a monotone sparsity functional or eventual
arrival at a tractable sparse unitary.

In particular a generic fiber gives only a two-point choice, not a
continuous path to its endpoints. A claim that every Givens fiber can
be rounded continuously while preserving the determinant would be
false for precisely this dimensional reason. Any successful global
rounding must coordinate multiple fibers.


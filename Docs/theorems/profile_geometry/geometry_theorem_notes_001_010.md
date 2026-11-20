## Round 003 — Every two-row orbit fiber is a filled ellipse, in all dimensions

**Status: proved exact fiber theorem and exact support inequality.**

Let A=diag(a), let C be any complex matrix, fix indices i,j, and conjugate C
by a unitary supported on those two coordinates. Normality is not required
for this local identity.

Put delta=a_i-a_j. Let A_0 be A with its i-th entry replaced by a_j, let
M_0=A_0+C, and let E:C^2->C^n embed the i,j coordinates. Define
\[
c=\det M_0,\qquad T=E^*\operatorname{adj}(M_0)E.
\]
Conjugating the determinant by the two-row unitary moves A instead of C.
Its varying two-by-two block is a_j I+delta xx*, where x is an arbitrary
unit vector in C^2. The rank-one determinant identity therefore gives
\[
\boxed{f(x)=c+\delta\,x^*Tx,\qquad \|x\|=1.}
\]
This formula also holds when M_0 is singular; it uses the adjugate, not an
inverse or an unproved limiting argument.

Write xx*=(I+n·sigma)/2 with n on the unit two-sphere. Then f is an affine
real-linear map from S^2 to C. Its image is a filled ellipse, a segment, or
a point: a rank-two linear projection of S^2 fills the ellipse because its
kernel has a remaining dimension. At a permutation matrix T is diagonal,
so this ellipse degenerates to the familiar Givens segment. At a general
orbit point the ellipse need not degenerate.

For a support direction eta, put
\[
H=\tfrac12(\eta\delta T+\overline{\eta\delta}\,T^*).
\]
Then
\[
\max_{\|x\|=1}\operatorname{Re}(\eta f(x))
=\operatorname{Re}(\eta c)+\lambda_{\max}(H).
\]
Consequently the entire fiber lies in the half-plane Re(eta z)<=h exactly
when the explicit two-by-two matrix
\[
\boxed{(h-\operatorname{Re}(\eta c))I-H\succeq0.}
\]
This gives a small matrix inequality retaining the curved interior that
the stronger polygon omitted. It does not by itself bound that matrix
using only permutation products.

## Round 004 — Exact support ascent reduces counterexamples to simultaneous fiber inequalities

**Status: proved monotone reduction; terminal classification remains open.**

For fixed spectra and eta, define F(U)=Re(eta det(A+UD_bU*)). At each step,
consider all n(n-1)/2 two-row fibers and choose one giving the largest
possible increase. Replace the current fiber vector by a top eigenvector
of its Hermitian matrix H from Round 003.

If x=e_1 is the current point, the exact best increase on this fiber is
\[
\Delta_{ij}=
\frac{H_{22}-H_{11}}2+
\sqrt{\left(\frac{H_{11}-H_{22}}2\right)^2+|H_{12}|^2}.
\]
This is continuous in U and nonnegative. The resulting support values
increase and are bounded on the compact unitary group, so the selected
improvements tend to zero. Every accumulation point U_* therefore has
Delta_ij(U_*)=0 for every pair. This is exactly
\[
H_{12}=0,\qquad H_{11}\ge H_{22}
\]
in every current two-row fiber.

Thus any strict MOC counterexample would lead, without lowering its
support value, to a point satisfying all these explicit two-by-two
positive-semidefinite conditions. These conditions hold on both the
left-row and right-column fibers if the ascent alternates over both
families. Degenerate top eigenspaces cause no problem for this statement,
which asserts accumulation-point conditions rather than convergence to
a unique matrix.

At a fiber optimum, a vector at angle theta from the maximizing
eigenvector loses exactly
\[
(\lambda_{\max}(H)-\lambda_{\min}(H))\sin^2\theta.
\]
Hence every individual root direction has a precisely quantified local
support gap. The unsolved step is compatibility between distinct roots:
pairwise optimality does not prove that the full Hessian is negative
semidefinite, nor that the value is below a permutation support.

This is a geometric proof-search reduction, not a claim that a Jacobi
iteration globally optimizes a nonconvex objective.

## Round 005 — Fixed-spectrum common-law selection has no topological obstruction

**Status: proved continuous and equivariant selection theorem, conditional
only on convex-hull membership.**

Let v_1,...,v_N be a fixed finite list in a real affine space and let
P=conv(v_1,...,v_N). There is a continuous piecewise-affine map
\[
s:P\longrightarrow\Delta_{N-1},
\qquad
\sum_k s_k(x)v_k=x.
\]
To construct it, triangulate P using its vertices. On each simplex, use
ordinary barycentric coordinates and put zero weight on unused vertices.
On common faces these definitions agree, so the coordinates glue
continuously. Repeated copies of a vertex can share its weight equally;
nonvertices in the list can receive zero weight.

If a finite group G acts compatibly on P and the vertex indices, average
the section:
\[
s_G(x)=|G|^{-1}\sum_{g\in G}g^{-1}s(gx).
\]
This is still a nonnegative normalized barycentric section and is
G-equivariant. Composing with the continuous determinant-coefficient map
U->(D_0,D_1) gives continuous equivariant weights whenever CH holds for
that fixed spectrum.

In the relative interior there is also a canonical real-analytic choice:
maximize entropy -sum lambda_k log lambda_k subject to the barycenter.
After working in the affine span,
\[
\lambda_k(x)=
\frac{\exp(\theta(x)\cdot v_k)}
{\sum_l\exp(\theta(x)\cdot v_l)}.
\]
The derivative of the mean map is the positive-definite covariance on the
affine span. Strict convexity and coercivity in interior directions give
existence and uniqueness of theta, modulo an irrelevant affine constant.

Therefore loops in the unitary orbit, eigenvector phase holonomy, or an
inability to choose eigenvectors continuously cannot alone obstruct a
fixed-spectrum coefficient law. The feasible fibers of probability laws
are convex, and a section exists once the metric membership inequality
holds. Difficulties in varying spectra can still arise at degenerating
polytope geometry; no spectrum-independent weights are asserted.

## Round 006 — A global orientation inequality survives the Clifford relaxation

**Status: proved universal Spin-coordinate inequality; insufficient alone.**

For R in SO(6), split R into nine real two-by-two blocks and define
\[
m_{ij}=\|R_{ij}\|_F^2,\qquad h_{ij}=\det R_{ij}.
\]
Let epsilon be the four-by-three matrix of sign triples with product +1.
Under Spin(6)=SU(4), consistent oriented Cartan bases give
\[
h=\tfrac14\epsilon^T p\,\epsilon,\qquad p_{ab}=|u_{ab}|^2.
\]
Since p is doubly stochastic, Birkhoff's theorem implies that h lies in
the convex hull of the 24 D_3 Weyl matrices: signed permutation matrices
with an even number of sign reversals. This claim concerns h alone, not
a simultaneous common law for m and h.

For any assignment pi, choose signs s_i with product -1 and nonnegative
weights w_i. Maximization over these 24 Weyl matrices gives
\[
\sum_i w_i s_i h_{i,\pi(i)}
\le \sum_iw_i-2\min_iw_i.
\]
Indeed an aligned Weyl assignment must disagree with at least one sign,
and changing the cheapest sign attains the right side. A nonidentical
permutation has at most one fixed position in three dimensions and
cannot exceed that value.

In particular, if the product of the three nonzero signs of
h_{i,pi(i)} is negative, then
\[
\boxed{\sum_iw_i|h_{i,\pi(i)}|
\le\sum_iw_i-2\min_iw_i.}
\]
For equal weights, the wrong-orientation sum is at most one. Treating
|h_ij|<=m_ij/2 independently would only give the much weaker bound three.

This geometrizes the parity constraint. The companion analyst subsequently
received an exact actual-spectral separator for the relaxation combining
this Weyl condition with m>=2|h| and doubly-stochastic m/2. Therefore this
orientation inequality does not complete the spectral argument.

## Round 007 — Sparse block support produces a robust nonlinear exclusion

**Status: proved universal inequality and explicit exclusion radius;
radius sharpened jointly with the analysis researcher.**

For distinct block rows r,s and a chosen column j, block orthogonality
gives
\[
R_{rj}R_{sj}^T=-\sum_{k\ne j}R_{rk}R_{sk}^T.
\]
For a two-by-two matrix A,
sigma_min(A)=|det A|/sigma_max(A)>=|det A|/||A||_F.
The triangle inequality and submultiplicativity therefore imply
\[
\boxed{
|h_{rj}|\sqrt{m_{sj}}
\le\sqrt{m_{rj}}\sum_{k\ne j}\sqrt{m_{rk}m_{sk}}.
}
\]
The inequality extends continuously when the selected block is singular.

Consider the virtual moment point
\[
m_*=
\begin{pmatrix}
2/3&0&4/3\\
4/3&2/3&0\\
0&4/3&2/3
\end{pmatrix},
\qquad h_*=-I/3.
\]
It satisfies m>=2|h|, all row and column sums of m equal two, and the
Weyl-convex h condition. Yet it cannot come from an SO(6) matrix: its
invertible block R_11 would be orthogonal to nonzero R_21 through a
single shared block column, forcing R_21=0.

The contradiction is quantitatively stable. If an actual (m,h) were
within epsilon<=1/27 in entrywise sup norm, then
\[
\frac{|h_{11}|^2m_{21}}{m_{11}}
\ge\frac{(8/27)^2(35/27)}{19/27}
=\frac{2240}{13851}.
\]
The squared right side of the divided row inequality would be at most
\[
2\epsilon(m_{22}+m_{13})
\le\frac{112}{729}
=\frac{2128}{13851},
\]
a strict contradiction. Therefore every actual moment point has
\[
\boxed{\|(m,h)-(m_*,h_*)\|_\infty>1/27.}
\]
This bound separates the missing joint orthogonality from orientation
alone. It supplies a concrete nonlinear condition that an actual-spectral
dual argument can try to exploit.

## Round 008 — A positive theorem for two independent compressions

**Status: proved for arbitrary complex spectra; no normality of the
compressed two-by-two matrices is assumed.**

Let X,Y be two-by-three complex coisometries:
XX*=YY*=I_2. Write their columns x_i,y_j. For arbitrary a,b in C^3,
\[
\boxed{
\det(XD_aX^*+YD_bY^*)
\in\operatorname{conv}
\{(a_i+b_j)(a_k+b_l): i\ne k,\ j\ne l\}.
}
\]
Moreover the weights can be chosen independently of a and b.

Define F_ij=|det[x_i,y_j]|^2. In C^2,
|det[x,y]|^2=||x||^2||y||^2-|x*y|^2. The coisometry identities imply
\[
\sum_jF_{ij}=\|x_i\|^2\le1,\quad
\sum_iF_{ij}=\|y_j\|^2\le1,\quad
\sum_{ij}F_{ij}=2.
\]
This is the fixed-cardinality bipartite matching polytope. Its integral
vertices are incidence matrices of matchings containing exactly two
edges; this follows directly from the integral network-flow formulation.
Thus F is a convex combination of size-two matchings.

Assign a matching with edges {(i,l),(k,j)} to the product
(a_i+b_j)(a_k+b_l). Its mixed monomials are a_i b_l+a_k b_j, so its
expected mixed coefficients are exactly F.

It remains to verify the pure a and b coefficients, which is where the
three-parent-node hypothesis is decisive. Every matching selects two of
three a-indices. The probability that the pair {i,k} is selected is the
probability that the remaining index r is omitted:
\[
1-\|x_r\|^2=|\det[x_i,x_k]|^2.
\]
The last identity is complementary Cauchy–Binet for a two-by-three
coisometry. The analogous identity holds for y.

Finally Cauchy–Binet expands the actual determinant as
\[
\sum_{i<k}a_i a_k|\det[x_i,x_k]|^2+
\sum_{j<l}b_j b_l|\det[y_j,y_l]|^2+
\sum_{ij}a_i b_jF_{ij}.
\]
All coefficients agree with the matching construction, proving the
theorem. This is a complete positive result for generally nonnormal
compressions, obtained through transport rather than spectral replacement.

## Round 009 — A compactification boundary of MOC_4 is controlled by Round 008

**Status: proved leading-order MOC inequality on a double-rank-one
degeneration; finite-parameter extension remains open.**

Let v,w be independent unit vectors in C^4, alpha beta !=0, and let
\[
A(t)=\alpha vv^*+tA_1,\qquad
B(t)=\beta ww^*+tB_1,
\]
where A_1 is normal, kills v, and preserves v-perp, while B_1 is normal,
kills w, and preserves w-perp. These are normal matrices for real t.
Let H=(span(v,w))-perp, a two-dimensional plane, and
delta=1-|v*w|^2 in (0,1].

On L=span(v,w), the nonzero leading block
alpha vv*+beta ww* has determinant alpha beta delta. In the orthogonal
decomposition L+H, block determinant expansion gives the exact leading
formula
\[
\boxed{
\frac{\det(A(t)+B(t))}{t^2}
\longrightarrow
\alpha\beta\delta\,
\det(P_H(A_1+B_1)|_H).
}
\]
Equivalently,
\[
\det(A(t)+B(t))
=t^2\alpha\beta\delta\,
\det(P_H(A_1+B_1)|_H)+O(t^3).
\]
This follows from an invertible two-by-two Schur block and is valid even
if the compressed leading determinant vanishes.

Let a_1,a_2,a_3 and b_1,b_2,b_3 be the small spectral triples of A_1 and
B_1. Their compressions to H have the form XD_aX* and YD_bY* for
two-by-three coisometries. Round 008 puts their determinant in the hull
of the two-factor products using distinct indices on each side.

The permutation products for A(t),B(t), divided by t^2 alpha beta, tend
either to one of exactly these two-factor products (when the two large
eigenvalues are paired separately), or to zero (when the large eigenvalues
are paired with each other). Multiplication by delta in [0,1] is
therefore admissible through the zero vertex. Hence the limiting
determinant lies in the limiting permutation hull.

This proves the required MOC inequality on this boundary stratum,
including its nonnormal two-dimensional compressions. It gives a valid
endpoint for a configuration-space continuation proof. An inward
derivative or finite-t inequality is still needed; boundary positivity
alone does not establish the conjecture in the interior.


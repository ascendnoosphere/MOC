# Fixed-anchor realification fails for actual order-five mixers

This is a negative result for a proposed extension of the order-four
orthogonal two-table construction of [Zheng, preprint DOI
10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923).
It does **not** rule out an orthogonal convexification in which the anchor
row varies across the summands, and it is not a counterexample to MOC.

## Actual residual effects with no supported splitting direction

Let $H$ be the symmetric adjacency matrix of the graph consisting of
a triangle $1,2,3$ and the extra edge $1,4$. For real $t$, let
$W(t)=\exp(itH)\in U(4)$. Write $x_i(t)$ and $y_i(t)$ for the real
and imaginary parts of its $i$-th row, as column vectors. Define
$$
E_i(t)=x_i(t)x_i(t)^\top+y_i(t)y_i(t)^\top .
$$
Unitarity gives $\operatorname{tr}E_i=1$ and $\sum_i E_i=I$,
so these are actual residual effects, not an arbitrary PSD tuple.
The limits $x_i(t)\to e_i$ and $y_i(t)/t\to h_i=H_i^\top$ follow
from the first-order matrix exponential. In particular, since every
$h_i$ is nonzero and orthogonal to $e_i$, the support of each
$E_i(t)$ has dimension two for small nonzero $t$.

The two-dimensional spaces of traceless symmetric matrices supported
on these planes vary continuously. For example, use the normalized
$x_i(t)$ as first basis vector and normalize the component of $y_i(t)/t$
orthogonal to it as second; these converge to $e_i$ and $h_i/\|h_i\|$.
At the limiting planes, an equivalent pair of basis matrices is
$$
A_i=d_i e_i e_i^\top-h_i h_i^\top,\qquad
B_i=e_i h_i^\top+h_i e_i^\top,\qquad d_i=\deg(i).
$$
The graph-algebra core of the following proof appears in
[GraphEffectIndependence.lean](MOC/GraphEffectIndependence.lean).

Suppose $\sum_i \alpha_i A_i+\sum_i\beta_i B_i=0$. Its diagonal
at $j$ reads $d_j\alpha_j-\sum_{i\sim j}\alpha_i=0$. A maximizer
of the finite function $\alpha$ forces all neighboring values to
agree with it, and connectivity propagates equality to every vertex.
Write the common coefficient $\alpha_*$. The $(2,4)$ entry gives
$-\alpha_*(H^2)_{24}=0$, because this is a nonedge and all $B_i$
contribute zero there. There is a two-edge path through vertex 1,
so $(H^2)_{24}>0$ and $\alpha_*=0$. On each edge $j\sim k$ the
remaining equation reads $\beta_j+\beta_k=0$. The triangle
forces its vertices to zero, and connectivity propagates this to
all vertices.

The eight limiting directions are therefore independent. Their
Gram determinant is nonzero and continuous in the two local frame
vectors, so they remain independent for all sufficiently small
nonzero real $t$. Therefore the only tuple $\Delta_i$ of supported,
traceless symmetric matrices with zero total is the zero tuple.

This implies that $(E_i(t))$ is an extreme trace-one PSD tuple,
and in particular not a convex mixture of rank-one orthogonal
basis tuples. Indeed, if $E_i=\lambda F_i+(1-\lambda)G_i$ with
$0<\lambda<1$, every vector in $\ker(E_i)$ has zero quadratic form
under both PSD matrices $F_i$ and $G_i$, so is in both kernels.
Thus $F_i-G_i$ is supported on the range of $E_i$, and is traceless.
The total of those differences is zero, so the independence
argument forces equality. This is the supported-perturbation
principle found in [D'Ariano–Lo Presti–Perinotti,
DOI 10.1088/0305-4470/38/26/010](https://doi.org/10.1088/0305-4470/38/26/010),
with the extra trace-one equations imposed here.

## Transfer to minor tables with the anchor fixed

Choose a real unit row $r\in\mathbf R^5$ with no zero entries and
complete it to a real orthogonal matrix $R$ with first row $r$.
Then $U(t)=(1\oplus W(t))R$ is unitary and its first row is $r$. Any
unitary with first row $r$ has residual rows in the complexification
of $r^\perp$. For one such row $u$, its singleton squared moduli
and its 2-minors using the anchor row recover its entire real
symmetric effect in the ambient coordinates, since
$$
2r_jr_k\operatorname{Re}(\overline u_j u_k)
 =r_j^2|u_k|^2+r_k^2|u_j|^2-|r_j u_k-r_k u_j|^2.
$$
The recovery is linear in the minor data with $r$ fixed and each
$r_jr_k\ne0$. Projecting into the fixed real residual basis from $R$
then recovers $E_i(t)$.

In a proposed convex decomposition into orthogonal tables with
anchor row equal to $r$, or with the same anchor coordinate
moduli as $r$, adjust individual column signs first. This changes
no squared minor and makes all anchor rows equal to $r$. The linear
reconstruction would write $(E_i(t))$ as a convex mixture of
rank-one orthogonal basis tuples, contradiction. In particular the
order-four construction cannot generalize to order five as a
fixed-anchor mixture even if arbitrarily many orthogonal summands
are allowed. Only singleton and anchor-row two-minor matching data
are needed for this obstruction. It does not apply to a mixture
whose summands have different anchor coordinate moduli.

The order-five instance and transfer are a paper proof. The symbolic
graph core is separate from the matrix exponential and effect
realization steps.

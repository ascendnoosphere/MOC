# MOC: verified spectral and profile identities

17 October 2026

**Unrestricted Marcus–de Oliveira is not proved here.** The results include a quantitative order-four spectral inequality, MOC for a nearby complex spectral family, supporting-configuration reductions, and exact profile geometry. No historical priority claim is made.

Write
\[
z_\pi(a,b)=\prod_i(a_i+b_{\pi(i)}),\qquad
d_U(a,b)=\det(D_a+UD_bU^*).
\]
The target remains \(d_U(a,b)\in\operatorname{conv}\{z_\pi(a,b)\}\) for every complex \(a,b\) and every unitary \(U\).

**1. A quantitative spectral inequality in order four**

Fix arbitrary \(a,b\in\mathbb C^4\) and \(\eta\in\mathbb C\). Set
\[
h=\max_\pi\Re(\eta z_\pi),\quad g_\pi=h-\Re(\eta z_\pi),\quad m=\max_\pi g_\pi.
\]
For \(s\in\{0,1\}^4\), define
\[
p_s=(12)^{s_1}(34)^{s_2},\quad
q_s=(13)^{s_3}(24)^{s_4},\quad
\pi_s=q_s\circ p_s,\quad \delta_s=g_{\pi_s}.
\]
With \(\bar s=(1-s_1,\ldots,1-s_4)\), put
\[
K=\sum_s(-1)^{s_1+\cdots+s_4}\delta_s,\qquad
B=2\sum_{s_1=0}\sqrt{\delta_s\delta_{\bar s}}.
\]
Then
\[
\boxed{B\,m^{17}\ge2^{-144}|K|^{18}.}
\]
The undivided statement includes \(m=0\), and applies to arbitrary complex spectra.

Proof. The cone of nonnegative order-four common-minor costs has 82 extreme rays: 34 ordinary minor indicators and 48 mixed rays. The mixed rays need not be nonnegative on unitaries; they are used only to decompose permutation costs. Completeness is certified by an exact oriented boundary chain.

Choose the smaller deficit in each complementary pair. From an 82-ray decomposition of \(g\), delete every ray positive at a chosen coordinate. The remaining \(g_0\) satisfies
\[
B(g_0)=0,\quad0\le g-g_0\le B(g)\mathbf1,\quad
|K(g)-K(g_0)|\le B(g).
\]
All positive ray entries are at least one, all entries are at most two, and every ray has \(|K|\le2\). The total deleted coefficient is at most \(B/2\).

A homogeneous polynomial \(N\) of degree 18 vanishes on every actual spectral support cost. Exact factorizations on the zero-budget faces give
\[
|N(g_0)|\ge |K(g_0)|^{18}/2^{16}.
\]
Its coefficient norm in 14 selected permutation coordinates is at most
\[
31575966576774975049121280000000<2^{105}.
\]
The segment from \(g_0\) to \(g\) lies in \([0,m]^{14}\), so the derivative bound and \(N(g)=0\) give
\[
|N(g_0)|\le18\,2^{105}m^{17}B.
\]
If \(B<|K|/2\), combine these inequalities with \(|K(g_0)|>|K|/2\). If \(B\ge|K|/2\), use \(|K|\le8m\). Both cases prove the theorem.

This is quantitative separation: after normalization, actual spectral costs with nonzero cycle residual cannot approach a zero-budget face too quickly. It strengthens \(B=0\Rightarrow K=0\), but does **not** establish the linear estimate \(B\ge|K|\) needed to close that route.

The construction of \(N\), its spectral vanishing, the face factorizations, and the norm bound are in the accompanying notes. The proof uses no converse spectral-realization theorem and no assumed global nonic-square identity.

**2. Full MOC for a nearby complex spectral family**

Start at
\[
a^0=\left(0,\frac12,\frac{1+i\sqrt3}{2},\frac{1-i\sqrt3}{2}\right),\qquad
b^0=\left(-1,1,\frac{-2+i\sqrt3}{7},\frac{-2-i\sqrt3}{7}\right),
\]
with multiplier \(\eta_*=\frac{14}{3}-\frac{14}{9}i\sqrt3\).

The certificate specifies a rational tangent in the coordinates
\[
(\Re a_1,\Im a_1/\sqrt3,\ldots,\Re b_4,\Im b_4/\sqrt3).
\]
Five independent real equations retain the six support contacts
\[
1423,\ 2314,\ 2341,\ 2413,\ 3142,\ 3241.
\]
Their Jacobian has rank five, and the prescribed tangent lies in its kernel. The real analytic implicit-function theorem gives an analytic curve \((a(t),b(t))\) with those ties. Every initially coincident product pair has a nonzero splitting derivative. For sufficiently small \(t>0\), all 24 products are distinct and nonzero.

**Theorem.** For every analytic curve with the specified base point, tangent, and retained tie equations, there is \(\epsilon>0\) such that
\[
d_U(a(t),b(t))\in\operatorname{conv}\{z_\pi(a(t),b(t)):\pi\in S_4\}
\]
for every \(U\in U(4)\) and \(0<t<\epsilon\).

This covers every support direction of the family. The polygon has exactly the five edges
\[
3241\to1234\to4213\to2431\to2341\to3241.
\]
For each edge, exact rational certificates give a positive decomposition using ordinary squared minors and relabelings of the proved tetrahedral gap from N114/N128 of the supplied record.

The proof controls the analytic curve beyond its tangent. For each edge deficit \(G(t)\), the certificates give
\[
G(0)=\sum_j b_jR_j,\qquad G'(0)=\sum_j d_jR_j,
\]
where \(b_j\ge0\) and \(d_j>0\) whenever \(b_j=0\). The generators span the entire subspace of costs vanishing on the final contacts. A fixed linear right inverse represents the \(O(t^2)\) remainder with \(O(t^2)\) coefficient corrections. All coefficients remain positive for sufficiently small positive \(t\), uniformly over \(U\).

One edge splits a coincident base vertex. Its normalized normal has an unknown derivative involving the spectral second derivative. That contribution vanishes on all four coincident old products. Generators with already-positive base coefficients span that ten-dimensional subspace and absorb the contribution without changing the strictly positive emerging coefficients.

The five exposed edges exhaust the hull, so their positive decompositions prove full MOC for the family. The new transfer argument and certificates were independently audited. The theorem explicitly uses the established N114/N128 tetrahedral inequality as an input.

**3. Eleven-contact configurations**

Assume \(n=4\), **all 24 matching products are pairwise distinct**, and a supporting line \(\Re(\eta z)=h\), with \(h\ne0\), contains at least eleven products. Its support deficit is then a nonnegative combination of ordinary squared minors, hence nonnegative on every unitary.

Four products from two disjoint swaps satisfy \(z_{00}z_{11}=z_{10}z_{01}\). If three rotated products are \(h+iy_0,h+iy_1,h+iy_2\), then
\[
h-\Re(\eta z_{11})
=\frac{h(y_1-y_0)(y_2-y_0)}{h^2+y_0^2}.
\]
Thus four distinct active products cannot form a disjoint-swap rectangle when \(h\ne0\).

The complete ray cone leaves two symmetry orbits of mixed eleven-contact faces, containing 288 and 144 faces. On one orbit the spectral polynomial has a strictly nonzero factor throughout the mixed interior. On the other, its vanishing forces \(ab=\alpha^2\) and \(h=\alpha/2\). A coefficientwise Hessian row identity then forces two active products to have equal imaginary parts. Their real parts already agree, contradicting distinctness. Only ordinary minor rays remain.

The enumeration, polynomial identities, and Hessian identity have separate exact verifiers. This excludes additional terminal configurations; it does not cover six-to-ten-contact cases or supporting lines through the origin. The pairwise-distinct hypothesis is not replaced by a count of distinct values while allowing other active labels to coincide.

**4. Exact profile dimension and the order-two determinant identity**


For the complete squared-minor profile, the correct dimension is
\[
\dim_{\mathbb R}P(U(n))
=\dim_{\mathbb C}\overline{P(U(n))}^{\,\mathrm{Zar}}=(n-1)^2.
\]
Left/right diagonal phases have effective dimension \(2n-1\). An explicit Jacobian calculation gives the matching lower bound. The Euclidean image is compact semialgebraic and is not a real algebraic set for \(n\ge2\).

The \(n=2\) image is a line segment. Its complex Zariski closure has degree one. For \(n=3\), complementary minors identify the full profile with the singleton profile; its complex closure is an affine four-space, also of degree one.

These dimension statements agree with Karabegov’s [A mapping from the unitary to doubly stochastic matrices and symbols on a finite set](https://arxiv.org/abs/0806.2357). The accompanying audit includes an elementary all-\(n\) Jacobian proof.

The correct \(n=2\) determinant identity proves the complex case directly. For \(B=UD_bU^*\) and \(p=|u_{11}|^2\),
\[
B_{12}B_{21}=p(1-p)(b_1-b_2)^2,
\]
and consequently
\[
\boxed{d_U=p(a_1+b_1)(a_2+b_2)
+(1-p)(a_1+b_2)(a_2+b_1).}
\]
The profile is affine. For complex \(b\), the proof uses the displayed product \(B_{12}B_{21}\), not an off-diagonal absolute square.

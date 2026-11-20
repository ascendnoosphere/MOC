## 1. The cost space and the algebraic input

Let \(\mathcal V\subset\mathbb R^{S_4}\) be the fourteen-dimensional common-minor cost space. Its elements are real functions on the 24 permutations. The functions

\[
\pi\longmapsto 1_{\{\pi(I)=J\}},\qquad |I|=|J|,
\]

span this space. Equivalently, it is spanned by the real and imaginary parts of the rank-at-most-two matching products

\[
\pi\longmapsto\prod_{i=1}^4 C_{i,\pi(i)}.
\]

Write \(\mathbf1\) for the constant function and use

\[
\|g\|_\infty=\max_{\pi\in S_4}|g_\pi|.
\]

There is a real homogeneous degree-nine polynomial \(P_9\) on \(\mathcal V/\mathbb R\mathbf1\), pulled back to \(\mathcal V\), with the following properties.

1. It vanishes on the projected complex secant cone of the rank-two matching-product variety, including its Zariski closure. Therefore it vanishes on every actual complex spectral support cost, and on every constant shift of such a cost.
2. On the five-dimensional space \(\mathcal W\) of costs vanishing on all nine derangements,

   \[
   P_9|_{\mathcal W}=\pm F^3,
   \tag{1}
   \]

   where \(F\) is the normalized invariant cubic.

The degree-nine statement uses the primary theorem of Howard, Millson, Snowden and Vakil, *The geometry of eight points in projective space: representation theory, Lie theory, dualities*, [arXiv:1103.5255](https://arxiv.org/abs/1103.5255): the invariant cubic's Hessian divisor is twice the secant divisor. The coordinate elimination and the restriction (1) are proved in this campaign, not supplied by that paper. The independent derivation is recorded in `review_final_batch_proofs.md`; all finite polynomial identities used here are rebuilt in `code/theorems/finite_and_spin_geometry/review_final_batch_exact.py`.

The rest of the stability proof is elementary real algebra and finite-dimensional linear algebra. It applies to the full set \(P_9(g)=0\), which is potentially larger than the set of actual spectral costs.

## 2. Exact geometry of the nonnegative derangement face

The derangement restriction map

\[
D:\mathcal V\longrightarrow\mathbb R^9,
\qquad Dg=(g_\pi)_{\pi\text{ a derangement}},
\]

has rank nine. Its kernel \(\mathcal W\) is parametrized by five real numbers \((a,b,c,d,e)\). The nonzero coordinates are as follows; all omitted permutations have value zero.

| Permutation | Value |
|---|---:|
| \(1234\) | \(a+c\) |
| \(1243\) | \(a\) |
| \(1324\) | \(b+e\) |
| \(1342\) | \(b-d+e\) |
| \(1423\) | \(b\) |
| \(1432\) | \(b+c-d\) |
| \(2134\) | \(c\) |
| \(2314\) | \(d\) |
| \(2431\) | \(c-d\) |
| \(3124\) | \(e\) |
| \(3214\) | \(a-b+d\) |
| \(3241\) | \(a-b+d-e\) |
| \(4132\) | \(c-e\) |
| \(4213\) | \(a-b\) |
| \(4231\) | \(a-b+c-e\) |

Nonnegativity is equivalent to

\[
b,d,e\ge0,\quad a-b\ge0,\quad c-d\ge0,\quad c-e\ge0,
\quad b-d+e\ge0,\quad a-b+d-e\ge0.
\tag{2}
\]

On this space,

\[
Q=D_{\mathbf1}F=(d-e)^2,
\]

\[
F=(a-b)\bigl[bc+e(c-d)\bigr]+bd(c-e).
\tag{3}
\]

The two chambers of (2) admit useful positive parametrizations. When \(d-e=k\ge0\), write

\[
(a,b,c,d,e)=(A+B+k,\ B+k,\ E+k+C,\ E+k,\ E),
\tag{4}
\]

with \(A,B,C,E,k\ge0\). Then

\[
F=(E+k)(B+k)(A+k)
+C\bigl[A(B+E+k)+(B+k)(E+k)\bigr].
\tag{5}
\]

When \(e-d=k\ge0\), write

\[
(a,b,c,d,e)=(A+B+k,\ B,\ E+k+C,\ E,\ E+k),
\tag{6}
\]

and obtain

\[
F=(E+k)(A+k)(B+k)
+C\bigl[(A+k)(B+E+k)+BE\bigr].
\tag{7}
\]

All coefficients in these two polynomials are nonnegative, and each contains \(k^3\). In particular,

\[
F\ge |d-e|^3\ge0.
\tag{8}
\]

Setting \(k=0\) in either chamber gives the diagonal assignment deficit

\[
g^{(2)}_\pi=\sum_{i=1}^4w_i1_{\{\pi(i)=i\}},
\qquad (w_1,w_2,w_3,w_4)=(B,A,C,E)\ge0,
\tag{9}
\]

and

\[
F(g^{(2)})=e_3(w_1,w_2,w_3,w_4).
\tag{10}
\]

The table shows directly that deleting \(k\) changes every permutation value by at most \(2k\). Positivity of the coefficients in (5) and (7) also gives

\[
e_3(w)\le F(g).
\tag{11}
\]

At \(P_9(g)=0\), equations (1) and (8) first force \(k=0\), and then (10) forces at most two of the nonnegative weights to be nonzero. Thus the exact nonnegative zero set on this face is the union \(\mathcal S\) of six closed cones

\[
\mathcal S=
\left\{\left(\sum_iw_i1_{\{\pi(i)=i\}}\right)_{\pi\in S_4}:
w_i\ge0,\ \#\{i:w_i>0\}\le2\right\}.
\tag{12}
\]

## 3. A quantitative distance theorem

**Theorem 1.** There is a fixed constant \(C_*>0\), depending only on the chosen coordinate normalization, such that every \(g\in\mathcal V\) satisfying

\[
0\le g_\pi\le1\quad(\pi\in S_4),\qquad P_9(g)=0
\tag{13}
\]

obeys

\[
\boxed{\operatorname{dist}_\infty(g,\mathcal S)
\le C_*\epsilon^{1/9}},
\qquad
\epsilon=\max_{\pi\text{ a derangement}}g_\pi.
\tag{14}
\]

The conclusion includes \(\epsilon=0\). No assertion that the exponent \(1/9\) is sharp is needed.

**Proof.** Since \(D\) has rank nine, fix a linear right inverse

\[
R:\mathbb R^9\longrightarrow\mathcal V,
\qquad DR=I_9.
\]

Regard \(R\) as a \(24\times9\) matrix of permutation values, and put

\[
\beta=\max_\pi\sum_{j=1}^9|R_{\pi j}|.
\tag{15}
\]

Then \(\beta\ge1\), and \(\|Ru\|_\infty\le\beta\|u\|_\infty\). Define

\[
g^{(0)}=g-RDg.
\]

It vanishes on every derangement, satisfies \(g^{(0)}_\pi\ge-\beta\epsilon\), and differs from \(g\) by at most \(\beta\epsilon\).

Let \(\kappa_\pi\) be the number of fixed points of \(\pi\). This function belongs to \(\mathcal V\), vanishes exactly on the derangements, and lies between one and four on the other permutations. Therefore

\[
g^{(1)}=g^{(0)}+\beta\epsilon\kappa
\tag{16}
\]

belongs to the nonnegative cone of \(\mathcal W\), and

\[
\|g^{(1)}-g\|_\infty\le5\beta\epsilon,
\qquad \|g^{(1)}\|_\infty\le1+5\beta.
\tag{17}
\]

Choose the fourteen independent permutation evaluations used in the exact coordinate certificate as coordinates on \(\mathcal V\). Write \(M_0=1+5\beta\), and let

\[
L=\sup_{\|x\|_{\infty,14}\le M_0}
\sum_{j=1}^{14}|\partial_jP_9(x)|.
\tag{18}
\]

This is finite because \(P_9\) is a fixed polynomial on a compact box. The segment joining \(g\) and \(g^{(1)}\) lies in this box. Its fourteen-coordinate sup norm is bounded by its 24-coordinate sup norm. The mean-value inequality and \(P_9(g)=0\) give

\[
|P_9(g^{(1)})|\le5\beta L\epsilon.
\tag{19}
\]

Set \(B_0=5\beta L\). Since \(g^{(1)}\) is in the nonnegative derangement face, (1) and (8) imply

\[
0\le F(g^{(1)})\le B_0^{1/3}\epsilon^{1/3},
\qquad
k=|d-e|\le B_0^{1/9}\epsilon^{1/9}.
\tag{20}
\]

Use the relevant chamber parametrization and delete \(k\). This gives the nonnegative diagonal assignment deficit \(g^{(2)}\) of (9), with

\[
\|g^{(2)}-g^{(1)}\|_\infty\le2k,
\qquad e_3(w)\le F(g^{(1)}).
\tag{21}
\]

Order the four weights so that \(w_{(1)}\ge w_{(2)}\ge w_{(3)}\ge w_{(4)}\ge0\). Since

\[
e_3(w)\ge w_{(1)}w_{(2)}w_{(3)}\ge w_{(3)}^3,
\]

both smaller weights are at most \(B_0^{1/9}\epsilon^{1/9}\). Delete them to obtain \(g^*\in\mathcal S\). Every permutation value changes by at most their sum, so

\[
\|g^*-g^{(2)}\|_\infty\le2B_0^{1/9}\epsilon^{1/9}.
\tag{22}
\]

Combining (17), (20), (21), and (22), and using \(0\le\epsilon\le1\), yields

\[
\|g-g^*\|_\infty
\le\left[5\beta+4(5\beta L)^{1/9}\right]\epsilon^{1/9}.
\]

Thus one explicitly specified constant is

\[
\boxed{C_*=5\beta+4(5\beta L)^{1/9}}.
\tag{23}
\]

Neither \(\beta\) nor \(L\) depends on \(g\). The proof at \(\epsilon=0\) is included, or follows directly from (12). This proves the theorem. \(\square\)

The constant in (23) is a rigorously specified finite constant. A numerical value for it has not been computed, and none is claimed.

## 4. Uniform control on every complex unitary

For \(U\in U(4)\), define the complex signed determinant coefficients

\[
\omega_\pi(U)=
\frac{\operatorname{sgn}(\pi)\prod_iU_{i,\pi(i)}}{\det U}.
\tag{24}
\]

Their sum is one. Laplace expansion followed by the complementary-minor identity gives

\[
|\det U[I,J]|^2
=\sum_{\pi:\pi(I)=J}\omega_\pi(U).
\tag{25}
\]

Although the individual coefficients may be complex or negative, the right side of (25) is real. Consequently every common-minor cost has the well-defined extension

\[
g(U)=\sum_\pi\operatorname{Re}\omega_\pi(U)\,g_\pi.
\tag{26}
\]

Every entry of a unitary has modulus at most one, and \(|\det U|=1\). Hence

\[
\sum_\pi|\operatorname{Re}\omega_\pi(U)|\le24,
\qquad
|g(U)-s(U)|\le24\|g-s\|_\infty.
\tag{27}
\]

For \(s\in\mathcal S\), equation (25) gives

\[
s(U)=\sum_iw_i|U_{ii}|^2\ge0.
\]

**Corollary 2.** Under the hypotheses of Theorem 1,

\[
\boxed{g(U)\ge-24C_*\epsilon^{1/9}\quad\text{for every }U\in U(4).}
\tag{28}
\]

More generally, suppose \(g_\pi\ge0\), \(P_9(g)=0\),

\[
M=\max_\pi g_\pi,\qquad
\delta=\max_{\pi\text{ a derangement}}g_\pi.
\]

For \(M>0\), apply Theorem 1 to \(g/M\). Homogeneity yields

\[
\boxed{g(U)\ge-24C_*M^{8/9}\delta^{1/9}.}
\tag{29}
\]

If \(M=0\), then every permutation value is zero and (26) gives \(g(U)=0\) exactly.

For an actual spectral support cost \(c\), put \(h=\max_\pi c_\pi\) and \(g=h\mathbf1-c\). Then \(P_9(g)=0\), and (29) becomes

\[
\boxed{c(U)-h\le24C_*M^{8/9}\delta^{1/9}.}
\tag{30}
\]

The same constant works after any row or column relabeling: the full permutation sup norm is unchanged, and the projected secant equation is invariant as a zero set.

The bound in (27) is deliberately elementary. Cauchy--Schwarz also gives \(\sum_\pi|\omega_\pi(U)|\le\sqrt{24}\), because \(\sum_\pi\prod_i|U_{i,\pi(i)}|^2\le\prod_i\sum_j|U_{ij}|^2=1\). Thus \(24\) can be replaced throughout (28)--(30) by \(\sqrt{24}\) if desired. The weaker integer constant suffices for the stated result.

## 5. An exact reflection contact and its quantitative face map

Consider

\[
R_0=\frac13
\begin{pmatrix}
1&-2&0&2\\
-2&-1&2&0\\
0&2&1&2\\
2&0&2&-1
\end{pmatrix},
\qquad \pi_0=(13)(24).
\tag{31}
\]

This is a Hermitian unitary rank-two reflection. All four entries \((i,\pi_0(i))\) vanish.

The complete common-minor polytope has the previously audited 82-facet description. At the identity vertex, 26 mixed facets are active. An exact reconstruction of those facets and of all basic singleton and two-minor facets establishes:

1. Exactly two active mixed facets and four active basic facets have zero value at \(R_0\).
2. Their six value vectors have rank five.
3. Their common-zero permutation vertices are exactly

   \[
   \mathcal D_{\pi_0}=\{\pi:\pi(i)\ne\pi_0(i)\text{ for every }i\},
   \]

   the nine derangements relative to \(\pi_0\).
4. Every identity-active facet \(\phi\) obeys, for each \(\pi\in\mathcal D_{\pi_0}\),

   \[
   \phi_\pi\le\frac{81}{4}\phi(R_0).
   \tag{32}
   \]

For zero-slack facets, (32) is the common-zero assertion. For all other active facets it is a finite rational inequality. The maximum ratio over these facets and vertices is exactly \(81/4\). The reviewer rebuilt the entire orbit and all minor values independently; the checked values are verified in the `zero_gap_reflection` section of `code/theorems/finite_and_spin_geometry/review_final_batch_exact.py`.

Let now \(g\in\mathcal V\) be any deficit with \(g_\pi\ge0\) and \(g_{\mathrm{id}}=0\). The normal-cone theorem for a polytope expresses \(g\), modulo the affine equations, as a nonnegative combination of the facets active at the identity. The affine equations also hold on every actual unitary profile by (25). Evaluating (32) term by term therefore proves the exact inequality

\[
\boxed{\max_{\pi\in\mathcal D_{\pi_0}}g_\pi
\le\frac{81}{4}g(R_0).}
\tag{33}
\]

In particular, the right side is nonnegative. This also follows from the Hermitian-unitary tangent-cone theorem in `continuous_reversible_dimension_boundary.md`.

**Corollary 3: exact zero-gap contact.** If in addition \(P_9(g)=0\) and \(g(R_0)=0\), then there are nonnegative weights, at most two nonzero, with

\[
\boxed{g(U)=\sum_iw_i|U_{i,\pi_0(i)}|^2\quad\text{for every }U\in U(4).}
\tag{34}
\]

Indeed, (33) forces all nine relative derangement deficits to vanish, and the transported classification (12) applies. Since the four indicated entries of \(R_0\) are zero, (34) has zero first derivative at \(R_0\) along every differentiable unitary curve. This proves, in particular, that the cubic covector \(\ell\) in the rank-two Cayley reduction vanishes at this contact.

**Corollary 4: small reflection gap.** Without requiring exact zero gap, let \(M=\max g_\pi\). For \(P_9(g)=0\), combine (29) and (33) to obtain

\[
\boxed{g(U)\ge
-24C_*M^{8/9}
\left(\frac{81}{4}g(R_0)\right)^{1/9}
\quad\text{for every }U\in U(4).}
\tag{35}
\]

Both (34) and (35) apply to actual spectral support deficits whose original identity pairing is maximizing. Row and column symmetry copies of \(R_0\) have the corresponding statements. No classification of all reflection contact strata is claimed.

## 6. What this does and does not close

The zero-gap result closes a concrete obstruction found by the continuous track: an arbitrary nonnegative common-minor cost can have zero reflection gap and a nonzero endpoint derivative at exactly this real reflection. The spectral constraint prohibits that configuration here.

For a maximizing commuting base, the full fixed-plane support condition remains

\[
g(R)\ge\frac14\ell^T\mathcal A^+\ell.
\tag{36}
\]

At \(R_0\) with zero gap, (34) makes both sides zero, so that particular boundary obligation is solved. The Hölder estimates do not provide the quantitative rate needed to establish (36) for nearby positive gaps, and they do not classify other reflection strata. A general first-contact continuation proof still needs that missing control.

The new theorem is therefore a rigorous local-face stability result and a uniform approximate support bound. It is not a proof of the unrestricted determinant conjecture.

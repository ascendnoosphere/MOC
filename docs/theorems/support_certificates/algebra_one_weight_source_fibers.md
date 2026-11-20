# Actual complex-product fibers at a one-weight contact

## Status and scope

This note closes two algebraic questions arising at a one-weight boundary
contact of the four-by-four complex Marcus–de Oliveira problem. First, it
classifies the entire fiber of actual complex product vectors with a
specified real one-weight cost, including the change at zero constant
height. Second, it proves a leading quadratic lemma for a purely imaginary
rank-one mode in an explicit local model of the real four-plus-four node.

The quadratic lemma forces that particular first real cost term into a
two-weight assignment cone. Consequently its cubic covector vanishes for
the fixed real reflection family used in the direct track. This is a
restriction on a specified class of local approaches. It does not classify
all real projected Puiseux jets, and it does not prove the uniform bound
`E <= g` required by the unrestricted complex MOC argument.

The exact identities are reconstructed in
`algebra_one_weight_source_exact.py`, with their rational data in the
corresponding JSON file. The geometric input identifying the invariant
cone with the singular locus of the skew cubic, and the finite spectral
chart lemma, are documented in
`../moc200/categorical_spectral_moduli_final.md`, Sections 1–3 and 5.
The underlying primary source for the cubic model is
Howard–Millson–Snowden–Vakil,
[The geometry of eight points in projective space](https://arxiv.org/abs/1103.5255).
The fiber and leading-mode arguments below are proved explicitly here.

## 1. Product coordinates and the constant lift

Let `V` be the fourteen-dimensional real space of permutation cost
functions on `S_4` obtained from the common-minor coefficient space. Let

\[
e(\pi)=1,\qquad p_{ij}(\pi)=1_{\{\pi(i)=j\}},\qquad p=p_{11}.
\tag{1}
\]

Write `M` for the complex affine invariant cone in `V_C`. Every point of
`M` is a vector of finite complex spectral products, with a common scalar
allowed. In the fourteen coordinates fixed in the preceding notes,

\[
M=\{z:\nabla F(z)=0\},
\tag{2}
\]

where `F` is the real homogeneous cubic of the eight-point model. Write
`H(x)` for its Hessian. Since the gradient is quadratic,

\[
\nabla F(c+id)=\nabla F(c)-\nabla F(d)+iH(c)d.
\tag{3}
\]

A normalized one-weight *deficit* is `p`. The corresponding real spectral
cost is

\[
c=h e-p.
\tag{4}
\]

Its maximum is indeed `h`: `p` takes the values zero and one. The constant
height cannot be discarded when analyzing the actual complex source
fiber. Although it disappears from the support inequality, it changes
the Hessian rank from four at `h=0` to eight at every `h != 0`.

All vectors in (4) lie in the first-row assignment plane and hence in
`M`. Therefore `grad F(c)=0`, and (3) gives the exact condition

\[
c+id\in M\quad\Longleftrightarrow\quad
H(c)d=0\ \text{ and }\ \nabla F(d)=0.
\tag{5}
\]

In particular the source condition includes the full quadratic equations
on `d`; membership in the linear Hessian kernel alone is insufficient.

## 2. The full fiber at every nonzero height

Let

\[
R_i=\operatorname{span}_{\mathbb R}\{p_{i1},p_{i2},p_{i3},p_{i4}\},
\qquad
C_j=\operatorname{span}_{\mathbb R}\{p_{1j},p_{2j},p_{3j},p_{4j}\}.
\tag{6}
\]

Every complexified `R_i` and `C_j` is a linear four-plane contained in
`M`. For instance, a rank-two matrix with one arbitrary row and all three
other rows equal to `(1,1,1,1)` has permutation products depending only on
the selected image of that row. This realizes any vector in `R_i`.
The column construction is the transpose.

### Theorem 1: nonzero-height fiber

For every nonzero real `h`,

\[
\boxed{
\{z\in M:\Re z=h e-p\}
=(h e-p+iR_1)\ \cup\ (h e-p+iC_1).
}
\tag{7}
\]

Thus at nonzero height the actual product fiber is the union of the
ordinary row and column assignment fibers. This is a statement about
product vectors; it does not try to remove the usual Möbius and scaling
redundancies among spectral tuples that realize the same product vector.

**Proof.** The exact Hessian identities are

\[
\operatorname{rank}H(e)=\operatorname{rank}H(p)=4,
\qquad
\dim(\operatorname{im}H(e)+\operatorname{im}H(p))=8.
\tag{8}
\]

Consequently the two images have zero intersection. If `h != 0`, the
equation `h H(e)d=H(p)d` forces both sides to be zero. Hence

\[
\ker H(h e-p)=\ker H(e)\cap\ker H(p)=R_1+C_1.
\tag{9}
\]

The last equality follows either from the six explicit independent kernel
vectors below, or from the four independent equations in each of two
disjoint Hessian images. The intersection of `R_1` and `C_1` is the
two-plane `span(e,p)`, so the sum has dimension six. A useful basis is

\[
e,\ p,\ p_{12},\ p_{13},\ p_{21},\ p_{31}.
\tag{10}
\]

Write an element of this kernel as

\[
d=a e+b p+u p_{12}+v p_{13}+w p_{21}+z p_{31}.
\tag{11}
\]

The gradient vanishes identically on either assignment plane. Every mixed
term involving the common two-plane also vanishes. Therefore

\[
\nabla F(d)=uw V_{11}+uz V_{12}+vw V_{21}+vz V_{22},
\tag{12}
\]

where

\[
V_{11}=H(p_{12})p_{21},\quad
V_{12}=H(p_{12})p_{31},\quad
V_{21}=H(p_{13})p_{21},\quad
V_{22}=H(p_{13})p_{31}.
\]

These four vectors are linearly independent. In the fixed fourteen
coordinates, only their first five entries are nonzero; those entries are

\[
\begin{pmatrix}
-1&1&0&0&0\\
0&0&1&0&-1\\
0&0&1&-1&0\\
0&-1&-1&1&1
\end{pmatrix}.
\tag{13}
\]

Thus (12) is zero exactly when all four products `uw,uz,vw,vz` vanish.
Equivalently, `(u,v)=0` or `(w,z)=0`. This places `d` in `C_1` or
`R_1`, respectively. Conversely, either choice makes `c+id` belong to
the corresponding complex assignment plane. Equation (5) completes the
proof. The argument uses the direct-sum images in (8), so it is uniform
in `h` and is not an extrapolation from finitely many height samples.

## 3. The zero-height fiber has eight components

The kernel at `p` has dimension ten. Its intersection with the *actual*
invariant cone is nevertheless a finite union of linear four-planes. We
first establish the analogous description at `e`.

### Lemma 2: constant-node intersection

\[
\boxed{
M\cap\ker H(e)=
\bigcup_{i=1}^4 (R_i)_{\mathbb C}
\ \cup\ 
\bigcup_{j=1}^4 (C_j)_{\mathbb C}.
}
\tag{14}
\]

**Proof.** The Hessian kernel at `e` is exactly `B(z)=0`, where the
four entries of the singlet block are

\[
B(z)=
\begin{pmatrix}[12][34]\\[13][24]\end{pmatrix}
\begin{pmatrix}[56][78]&[57][68]\end{pmatrix}
\tag{15}
\]

on any representing eight-spinor configuration. The equality of these
four linear equations with the Hessian kernel follows from their equal
rank four and their equal row span; the verifier checks both exactly.

An outer product of two two-vectors is zero exactly when one factor is
zero. For a quartet of nonzero spinors, the two products
`[12][34]` and `[13][24]` vanish simultaneously exactly when at least
three of its four projective points coincide. Indeed, choosing a zero
bracket from each product produces two coincident pairs with a common
index; these give a triple collision. The converse is immediate.

If three row points coincide, every permutation product depends only on
the column assigned to the remaining row. The factors contributed by the
other three rows are independent of their ordering. The product vector
therefore lies in the corresponding `R_i`. Triple column collision gives
`C_j`. All eight planes are themselves contained in `M` and in the
kernel. The zero cone point belongs to them as well, proving (14).

### Theorem 3: zero-height fiber

Let `sigma` be the involution of the eight labels that swaps
`2 <-> 6`, `3 <-> 7`, and `4 <-> 8`, while fixing `1` and `5`.
Let `A_sigma` denote its signed action on bracket-product coordinates,
and put `T=-A_sigma`. Then

\[
T^2=I,\qquad Te=p,\qquad Tp=e,\qquad F(Tx)=F(x).
\tag{16}
\]

Define the eight real four-planes

\[
L_i=T(R_i),\quad 1\le i\le4,
\qquad
L_{4+j}=T(C_j),\quad1\le j\le4.
\tag{17}
\]

Every one contains `p`. The full zero-height actual fiber is

\[
\boxed{
\{z\in M:\Re z=-p\}=
\bigcup_{\nu=1}^{8}(-p+iL_\nu).
}
\tag{18}
\]

The same formula holds with `+p` in place of `-p`.

**Proof.** Differentiating (16) shows that `T` carries `ker H(e)`
to `ker H(p)`, and it preserves `M`. Thus (14) becomes

\[
M\cap\ker H(p)=\bigcup_{\nu=1}^{8}(L_\nu)_{\mathbb C}.
\tag{19}
\]

All planes are defined over the reals. Applying (5) at `c=-p` proves
(18). The eight transformed bases, their rank, their pairwise
distinctness, their containment of `p`, and their vanishing quadratic
equations are included in the exact certificate.

The mixed four-plus-four node has collision groups

\[
\{\text{row }1,\text{column }2,\text{column }3,\text{column }4\},
\quad
\{\text{row }2,\text{row }3,\text{row }4,\text{column }1\}.
\tag{20}
\]

The eight components correspond to choosing a triple collision in either
group. Two components are the ordinary first-row and first-column
assignment planes. The other six arise from mixed triple collisions.
They are genuine additional imaginary directions and cannot be removed
by assuming that every zero-height source is an ordinary assignment
point.

Equations (18)–(19) classify points whose full gradient vanishes. They
must not be confused with a description of every rank-one direction in
the larger local tangent cone. A tangent direction need satisfy only the
appropriate projected leading quadratic equations; it need not generate
an entire line contained in `M`.

## 4. An explicit local rank-one model at the real node

For `x,y` in `C^3`, consider the rank-at-most-two matrix

\[
C(x,y)=
\begin{pmatrix}
1&y_1&y_2&y_3\\
x_1&1+x_1y_1&1+x_1y_2&1+x_1y_3\\
x_2&1+x_2y_1&1+x_2y_2&1+x_2y_3\\
x_3&1+x_3y_1&1+x_3y_2&1+x_3y_3
\end{pmatrix}.
\tag{21}
\]

It is the sum of two outer products. Put `M=xy^T`. All permutation
products depend polynomially on the nine entries of `M`, subject to
`rank M <= 1`. Denote this product vector by `z(M)`. At `M=0`,
`z(0)=p`.

If `pi(1)=1`, its product is a product of three terms `1+M_ij`.
If `pi(1)=j+1` and `pi(i+1)=1`, its product is

\[
z_\pi(M)=M_{ij}
\prod_{\substack{k\ne i\\k\in\{1,2,3\}}}
\bigl(1+M_{k,\pi(k+1)-1}\bigr).
\tag{22}
\]

This explicit family suffices for the next lemma. No classification of
all possible source curves is needed or asserted.

Consider a curve in this rank-one model with

\[
M(t)=itN+t^2V+O(t^3),\qquad N=uv^T,\quad u,v\in\mathbb R^3.
\tag{23}
\]

The first mode is required to be purely imaginary and real rank one.
The second-order coefficient `V` may be complex; it is constrained by
the existence of the rank-one curve, but the argument below does not need
to use those additional constraints.

Take the actual scalar cost `c(t)=-Re z(M(t))`, and its nonnegative
permutation deficit

\[
g(t)=h(t)e+\Re z(M(t)),\qquad h(t)=\max_\pi c_\pi(t).
\tag{24}
\]

Then `g(0)=p`. Suppose its first potentially nonzero real correction is

\[
g(t)=p+t^2q+O(t^3),
\tag{25}
\]

and that `q` is zero on all nine ordinary derangements. Nonnegativity
of the deficit then implies

\[
q_\pi\ge0\qquad\text{whenever }\pi(1)\ne1.
\tag{26}
\]

The zero-derangement assumption is the leading contact condition relevant
when the reflection gap vanishes to a higher order than this real cost
correction.

### Theorem 4: leading imaginary mode produces an assignment correction

Under (21)–(26), there exist a real number `alpha`, a nonnegative number
`tau`, and an index `j` in `{2,3,4}` such that

\[
\boxed{q=\alpha p_{11}+\tau p_{jj}.}
\tag{27}
\]

The case `tau=0` is allowed.

**Proof.** For each pair `(i,j)` in `{1,2,3}^2`, precisely two
permutations satisfy `pi(1)=j+1` and `pi(i+1)=1`. Exactly one of
these is a derangement. Call them `D_ij` and `N_ij`, respectively.
The nine derangements and the nine other permutations partition the
eighteen permutations outside `p_{11}`.

Both paired products in (22) have the same first factor `M_ij`.
Expanding (22) to order `t^2` in (23), and subtracting the paired
values, cancels both `Re V_ij` and the common height correction. Since
`q(D_ij)=0`, this gives

\[
q(N_{ii})=-u_i v_i(u_k-u_l)(v_k-v_l),\qquad\{i,k,l\}=\{1,2,3\},
\tag{28}
\]

and, when `i != j` and `k` is the remaining index,

\[
q(N_{ij})=-u_i v_j(u_j-u_k)(v_i-v_k).
\tag{29}
\]

Define cyclically indexed three-vectors

\[
A_i=u_i(u_{i+1}-u_{i+2}),\qquad
B_i=v_i(v_{i+1}-v_{i+2}).
\tag{30}
\]

Their coordinate sums are zero. Equations (28)–(29) become

\[
q(N_{ii})=-A_iB_i,\qquad
q(N_{ij})=A_iB_j\quad(i\ne j).
\tag{31}
\]

All nine identities are checked as polynomial identities in the six
independent coordinates of `u,v`; no numerical evaluation is used.

We now classify the signs in (31). If `A=0` or `B=0`, every value
outside `p_{11}` is zero. Suppose both are nonzero. The zero-sum vector
`A` cannot have two positive coordinates: their off-diagonal constraints
would force every coordinate of `B` to be nonnegative, whence `B=0`.
The same argument excludes two negative coordinates. Thus `A` has one
positive coordinate, one equally large negative coordinate, and one zero
coordinate. Write their indices as `a,b,c`.

The off-diagonal inequalities from rows `a,b` force `B_c=0`,
`B_a <= 0`, and `B_b >= 0`. The zero sum then gives
`B=-lambda A` for some `lambda>0`. Consequently the four entries of
(31) indexed by `{a,b} x {a,b}` are all the same positive value

\[
\tau=\lambda A_a^2,
\tag{32}
\]

and all other entries are zero. These four permutations are exactly the
permutations outside `p_{11}` that fix label `c+1`. Therefore
`q-tau p_{c+1,c+1}` is supported on the six permutations with
`pi(1)=1`.

Finally, the subspace of `V` supported on those six permutations is
one-dimensional, spanned by `p_{11}`. Equivalently, the restriction
from the fourteen-dimensional space to the other eighteen permutation
coordinates has rank thirteen. The exact certificate reconstructs this
rank and its kernel. It proves (27), including the zero branch.

The vanishing case in (30) also has a simple description: `A=0` exactly
when `u` lies on one of the three coordinate axes or on the line
`u_1=u_2=u_3`. This follows immediately by separating the cases in which
all three coordinates are nonzero and in which one vanishes. The same
holds for `B`. These eight choices of ruling families reflect the eight
linear source components above. This correspondence motivates further
analysis, but is not used to identify all global lines with all local
tangent directions.

## 5. What this gives for the reflection energy

For the real reflection family

\[
R=\begin{pmatrix}
a&0&b&c\\
0&a&-c&b\\
b&-c&-a&0\\
c&b&0&-a
\end{pmatrix},\qquad a^2+b^2+c^2=1,\quad abc\ne0,
\tag{33}
\]

the direct track uses the relative permutation `pi_0=(12)(34)`. After
the corresponding column relabeling, the nine relative derangements
become the ordinary derangements used above, and the diagonal assignment
cone becomes

\[
s(U)=\sum_i w_i|U_{i,\pi_0(i)}|^2.
\tag{34}
\]

Every selected entry is zero at `R`, so these assignment functions have
zero differential there. Their cubic covectors consequently vanish, as
proved explicitly in `direct_quantitative_contact_rigidity.md`,
Section 8. Linearity and (27) therefore give

\[
\ell_y(q)=0
\tag{35}
\]

for the first real term in Theorem 4, even though the coefficient
`alpha` need not be nonnegative.

This rules out a nonzero leading cubic covector in this specific
purely-imaginary rank-one approach to the real node. It supplies no
uniform estimate for all remaining approaches. In particular it does
not turn the currently available local estimate `E <= C_R g(R)` into
the required estimate with constant one.

## 6. The remaining jet obligation

There are three distinct issues that the fiber and leading-mode results
do not settle.

1. **Other finite source points.** At zero height the source may be
   `-p+id` with nonzero `d` in any of the eight planes in (18). Such
   a point need not be the real node used in (21). At nonzero height the
   source lies in an assignment plane by (7), but the imaginary
   assignment parameters still affect its complex tangent space.
2. **Higher and mixed orders.** For an actual complex curve
   `z(t)=z_0+t z_1+t^2 z_2+...`, the first equations are

   \[
   H(z_0)z_1=0,\qquad H(z_0)z_2+\nabla F(z_1)=0.
   \tag{36}
   \]

   Real parts can begin later than imaginary parts. Reparametrization
   can produce fractional powers in the real-cost scale. Theorem 4
   handles one explicit second-order pattern and does not cover all
   such patterns.
3. **Uniformity of the projection.** A sequence of real cost vectors
   approaching the one-weight axis need not have a bounded chosen
   imaginary source or a bounded constant lift. A finite-source
   classification alone gives no uniform bound along such sequences.

The coefficient-one blowup obligation remains

\[
\ell_y(q)^2\le 4A_{yy}(p)\,g_R(r)
\tag{37}
\]

for every admissible leading real expansion
`g_epsilon=p+epsilon q+epsilon^2 r+...` with the relevant reflection
gap of order `epsilon^2`, together with the necessary treatment when
these displayed leading terms vanish. The results here eliminate one
possible nonzero numerator and identify the exact finite source
components that a complete analysis must consider. They do not prove
(37) in full or a uniform little-oh energy estimate.

## 7. Certificate contents

The verifier uses rational arithmetic and the previously audited cubic
coordinates. It independently reconstructs the following finite data:

| Identity or rank | Exact result |
|---|---:|
| Ranks of `H(e)` and `H(p)` | 4 and 4 |
| Dimension of their combined image | 8 |
| Common-kernel dimension | 6 |
| Rank of the four mixed gradient vectors | 4 |
| Singlet kernel equals `ker H(e)` | Yes |
| Involution carries `e` to `p` and preserves `F` | Yes |
| Distinct zero-height source planes | 8 |
| Dimension of each plane | 4 |
| Rank of restriction outside `p_{11}` | 13 |
| Exact paired quadratic differences | 9 |

The sign classification, quartet collision argument, and limits of the
local conclusion are mathematical parts of the proof above. The finite
certificate is not presented as a substitute for those arguments.

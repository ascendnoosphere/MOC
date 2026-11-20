# Holomorphic reduction to a small positive face

This note proves a holomorphic minimum-face bound for every polynomial degree.

## 1. General theorem

Let t belong to a compact positive weight polytope

\[
\mathcal P=\{t\in\mathbb R_{\ge0}^n:At=b\},
\]

and let F be holomorphic on an open set containing the complex affine span of L(\mathcal P), where L is complex-linear on complexified weight coordinates. Assume F extends holomorphically along the affine lines used below; an entire polynomial certainly suffices.

Choose a maximizer t* of Re F(Lt) with the minimum possible number s of positive coordinates. Restrict all maps to these active coordinates. Let d be the real rank of A on them, and let e be an upper bound for the complex dimension of the space containing L(ker A).

Then

\[
\boxed{s\le d+e.}
\tag{1}
\]

To prove this, the active tangent space T=ker A has real dimension s-d. If L has a nonzero kernel on T, an exact constant line reaches a smaller face. Otherwise L is injective on T. If s-d>e, its real image W in a complex e-dimensional space satisfies

\[
\dim_{\mathbb R}(W\cap iW)\ge2\dim_{\mathbb R}W-2e>0.
\]

Choose a nonzero z with z,iz in W, and tangent vectors u,v mapping to z,iz. Because every active coordinate of t* is strictly positive, a small real disk t*+xu+yv lies in the feasible active face. The function

\[
\xi\longmapsto F(Lt^*+\xi z)
\]

is holomorphic and its real part has a local maximum at zero. The harmonic maximum principle makes it constant on that disk; the one-variable identity theorem makes it constant along the relevant affine line. Follow t*+xu to its first nonnegative boundary point. It is another maximizer with smaller support, a contradiction.

The affine nature of the weight slice matters. A complex tangent direction to a curved real manifold alone does not provide the small complex disk used in this proof.

## 2. Apply it to actual unitary updates

Use the notation of `continuous_finite_witness.md`:

\[
U=I+Y(V-I_r)Y^*,\quad W_i=y_i^*y_i,\quad
N(t)=\sum_i t_iP_i\otimes W_i,
\quad \sum_i t_iW_i=I_r.
\]

The weight polytope is compact after discarding zero rows, since taking traces gives sum_i t_i tr W_i=r. The determinant support is the real part of an entire polynomial in N(t).

Let d=dim_R span{W_i}, and suppose the P_i lie in a complex affine space of dimension q. Choose P_0 in that affine space and write P_i=P_0+sum_{alpha=1}^q c_{alpha i}Q_alpha. On the normalized weight slice,

\[
N(t)=P_0\otimes I_r+
\sum_{\alpha=1}^q Q_\alpha\otimes
\left(\sum_i t_i c_{\alpha i}W_i\right).
\]

The varying part lies in a complex space of dimension at most qd. Applying (1) gives

\[
\boxed{s\le(q+1)d\le4d,}
\tag{2}
\]

because trace-one two by two matrices have complex affine dimension three.

The support objective can increase in this reduction; the entire determinant trajectory need not be preserved. Retain only the active spectral labels and rescale frame rows by sqrt(t_i). Every new permutation product extends to an old permutation fixing deleted labels, exactly as in the finite-witness note. Therefore a strict scalar MOC counterexample descends.

For a generic real two-plane, d≤3 and q≤3, so a strict counterexample descends to at most12 labels. For a complex two-plane, d≤4, so at most16 labels suffice. On a q≤2 spectral branch, these improve to9 and12. For a one-dimensional phase update, d=1, giving at most4 labels without using quadraticity. Combined with the four-label common law, this is a second complete proof of the all-dimensional rank-one scalar MOC theorem.

## 3. The q≤2 condition in spectral coordinates

For P_i=(a_i+b_i)^{-1}[[a_i,1],[a_ib_i,b_i]], an affine linear condition on their entries is equivalent, after multiplying by a_i+b_i, to

\[
\alpha a_ib_i+\beta a_i+\gamma b_i+\delta=0
\quad\text{for every retained label }i,
\tag{3}
\]

with coefficients not all zero. This is a paired bilinear/Möbius relation. The bound depends on the chosen pairing underlying the finite-rank update; changing that pairing may change the rank class, so the condition must not be asserted after an arbitrary permutation normalization without checking it.

The isospectral branch b_i=a_i has q≤2. It includes the actual real-stable determinant polynomial discussed in `continuous_isospectral_obstruction.md`; real stability does not imply a common polynomial coefficient law.

## 4. A degree-independent compression bound

The same argument applies to a scalar compressed determinant

\[
\det\left(\sum_i a_i t_iE_i+B\right),
\quad E_i=x_ix_i^*,\quad \sum_i t_iE_i=I_r.
\]

Let d=dim_R span{E_i}. The varying matrix lies in the complexification of this d-dimensional real space. Thus e≤d and a maximizing scalar support has at most2d active parent labels. Deleting labels preserves the set inclusion of matching vertices.

Consequently any strict scalar CMC(r;m,n) counterexample can be reduced on each parent side to at most2r² labels, or r(r+1) labels for real frames. Repeating on the second side preserves the strict violation and the already obtained bound on the first. For r=2 these are8 and6, recovering the earlier quadratic finite reduction; the holomorphic proof establishes the same form in every rank.

## 5. Why this does not complete MOC

The weight-slice reduction is effective when there are more parent labels than independent normalization constraints plus complex variation coordinates. An arbitrary full-dimensional unitary can have linearly independent frame effects and no nontrivial positive weight tangent at all. The proof therefore reduces fixed finite-rank update classes, not every unitary to rank one or rank two. A new step must create compatible positive weight freedom, or directly settle the remaining finite classes.

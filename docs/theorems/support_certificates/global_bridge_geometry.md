## 1. The proposed global bridge

Let \(\Phi(U)\) be the vector consisting of the sixteen squared entry moduli and the thirty-six squared two-minor moduli of an order-four unitary. Complementarity recovers all other exterior degrees. The established profile identities put this vector in an affine space of dimension thirteen.

The earlier real-profile purification theorem gives

\[
\operatorname{conv}\Phi(U(4))=\operatorname{conv}\Phi(SO(4)).
\]

Let \(\mathcal R_2\) denote the set of unitary matrices \(V\) for which some monomial unitary \(M\) satisfies \(\operatorname{rank}(V-M)\le2\). A potentially sufficient structural bridge is

\[
\operatorname{conv}\Phi(U(4))
 =\operatorname{conv}\Phi(\mathcal R_2). \tag{1}
\]

This is weaker than a pointwise monomial rank-two normal form. The latter is already false. Identity (1) remains unproved in this investigation.

If (1) holds and every actual spectral support functional is bounded by its permutation maximum on every relative rank-two orbit at **every monomial base**, then MOC follows in order four by linearity and convexity. A result restricted to the maximizing monomial base is insufficient for this implication: (1) uses all monomial bases. At a base whose value is below the support height, the prescribed-height six-by-six pencil retains the nonzero height offset; the maximizing-base energy formula cannot simply be reused with that offset deleted.

For real orthogonal matrices, the earlier exact completion theorem characterizes \(\mathcal R_2\) by twenty-four discriminants. For each orientation-corrected column permutation \(V\), put

\[
a=\det V[123,124],\quad b=-\det V[23,24],\quad
c=-\det V[13,14],\quad d=V_{34},
\]

\[
\Delta(V)=4(ab-cd)^2-(a^2+b^2-c^2-d^2)^2.
\]

An order-four real orthogonal matrix has a monomial rank-two completion if and only if at least one of these discriminants is nonnegative. Thus the set where all twenty-four are strictly negative is an open region of pointwise inaccessibility.

## 2. A general finite-jet interior theorem

Let \(M\) be a smooth manifold, let \(\Phi:M\to\mathbb R^N\) be twice continuously differentiable, and let \(A\) be the affine hull of \(\Phi(M)\), of dimension \(d\). Fix \(x\in M\) and local tangent coordinates of dimension \(m\). Write

\[
G_\alpha=d\Phi_\alpha(x)\in\mathbb R^m,
\qquad H_\alpha=d^2\Phi_\alpha(x)\in\operatorname{Sym}_m.
\]

Assume the following two properties.

1. There are \(W\succ0\) and \(v\in\mathbb R^m\) satisfying
   \[
   \operatorname{tr}(WH_\alpha)+G_\alpha\cdot v=0
   \quad\text{for every }\alpha. \tag{2}
   \]
2. The first and second derivatives together span the full translated affine hull:
   \[
   \operatorname{span}\{d\Phi(x)[u],d^2\Phi(x)[u,w]:u,w\in T_xM\}
   =A-A. \tag{3}
   \]

**Theorem.** If \(\operatorname{conv}\Phi(M)\) is compact, then \(\Phi(x)\) lies in its relative interior.

**Proof.** Suppose a nonconstant affine support functional \(F=c\cdot\Phi\) has a maximum at \(x\). Then \(dF(x)=0\) and \(H_F\preceq0\). Summing (2) against \(c\) gives \(\operatorname{tr}(WH_F)=0\). Since \(W\succ0\), this forces \(H_F=0\). The coefficient vector \(c\) therefore annihilates every vector in (3), so it is constant on \(A\), contradicting the choice of a nonconstant support functional. Every relative-boundary point of a compact convex set has such a support functional. Hence the point is in the relative interior. \(\square\)

The result is invariant under changes of tangent coordinates. The drift term accounts for the first-derivative contribution to the coordinate change of a Hessian. This is a finite-jet argument; it does not require a differential equation, continuation of \(W\), or a strong maximum principle.

## 3. An exact rational diffusion certificate

Apply the theorem to \(SO(4)\), with the six skew generators \(K_{ij}=E_{ij}-E_{ji}\), at the earlier rational matrix

\[
O_0=\frac1{882259}
\begin{pmatrix}
862328&12753&10842&-185718\\
5499&460784&-752232&13260\\
-135564&566670&336062&-570921\\
127920&494754&315393&646346
\end{pmatrix}.
\]

The exact verifier `global_bridge_elliptic_exact.py` constructs rational \(W,v\) and checks all fifty-two equations (2). It also checks

\[
W\succ\frac1{1500}I_6,
\quad \operatorname{rank}d\Phi(O_0)=6,
\quad \operatorname{rank}(d\Phi,d^2\Phi)(O_0)=13.
\]

Consequently the normal Hessians have rank seven, and the finite-jet theorem applies. The full rational coefficients and exact positive LDL pivots are in `global_bridge_elliptic_exact.json`.

**Provenance qualification.** The earlier campaign had already supplied a positive fourteen-permutation profile representation of this same matrix in `categorical_collision_and_rank_two_bridge.md`. Thus this example was already known to be harmless to a convex rank-two bridge. The present result supplies a different local geometric certificate and a general criterion; it is not the first proof that the old pointwise normal-form obstruction admits a convex profile representation.


## 5. Exact derivative calculation and verification

For a representation matrix \(R(O)\), equal either to \(O\) or to its second compound, and its induced skew generators \(B_i\), define \(M=R(O)\). For each squared coordinate \(\phi=M_{ab}^2\),

\[
\partial_i\phi=2M_{ab}(B_iM)_{ab},
\]

\[
\partial_i\partial_j\phi
=2(B_iM)_{ab}(B_jM)_{ab}
 +M_{ab}\{(B_iB_j+B_jB_i)M\}_{ab}. \tag{6}
\]

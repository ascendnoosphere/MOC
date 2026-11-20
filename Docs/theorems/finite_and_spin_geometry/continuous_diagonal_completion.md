# Imaginary diagonal completion and two commuting rank-two factors

This note proves an infinitesimal imaginary-diagonal completion criterion under the nonzero-edge hypothesis and a factorization of every orientation-preserving real four by four matrix into two commuting complex rank-two updates, modulo a scalar phase.

## 1. The infinitesimal completion problem

Let

\[
K=\begin{pmatrix}
0&x&y&z\\-x&0&w&v\\-y&-w&0&t\\-z&-v&-t&0
\end{pmatrix},
\qquad xyzwvt\ne0,
\]

and define

\[
p=xt,\quad q=yv,\quad r=zw,
\qquad \phi=\operatorname{Pf}(K)=p-q+r.
\]

We ask whether real numbers (d_1,\ldots,d_4) make

\[
H=iK+\operatorname{diag}(d_1,d_2,d_3,d_4)
\tag{1}
\]

a Hermitian matrix of rank at most two.

**Theorem.** Under the nonzero-edge hypothesis,

\[
\boxed{\text{A completion (1) exists}
\quad\Longleftrightarrow\quad
\operatorname{Pf}(K)\prod_{i<j}k_{ij}\le0.}
\tag{2}
\]

When the Pfaffian vanishes, (D=0) is a completion. When the inequality is strict, a real algebraic completion can be obtained from a two by two Schur complement.

## 2. Exact Schur complement equations

Partition the indices as (12\mid34), and suppose

\[
\delta=d_1d_2-x^2\ne0.
\]

The internal block has inverse

\[
\begin{pmatrix}d_1&ix\\-ix&d_2\end{pmatrix}^{-1}
=\frac1\delta\begin{pmatrix}d_2&-ix\\ix&d_1\end{pmatrix}.
\]

The off-diagonal Schur complement, multiplied by (\delta), is

\[
-(yz,d_2+wv,d_1)
+i\{t(d_1d_2-x^2)-x(zw-yv)\}.
\]

It vanishes exactly when

\[
\boxed{d_1d_2=\frac{x\phi}{t},\qquad
yz,d_2+wv,d_1=0.}
\tag{3}
\]

After solving (3), choose

\[
d_3=\frac{y^2d_2+w^2d_1}{\delta},\qquad
d_4=\frac{z^2d_2+v^2d_1}{\delta}.
\tag{4}
\]

These real choices make the entire Schur complement zero, hence make the full matrix have rank exactly two.

Eliminating (d_2) in (3) gives

\[
d_1^2=-\frac{xyz\,\phi}{twv}.
\tag{5}
\]

Because every edge is nonzero, the right side is nonnegative exactly when (\phi xyzwvt\le0). This is the sign condition in (2).

## 3. Degenerate Schur blocks do not invalidate the criterion

Necessity requires knowing that a suitable internal block exists. A rank-one Hermitian matrix cannot have these off-diagonal entries: for any rank-one Hermitian matrix the triangle product (H_{ij}H_{jk}H_{ki}) is real, whereas here it is nonzero and purely imaginary. A Hermitian matrix of rank two has a nonsingular two by two principal submatrix. Indeed write it as (V\operatorname{diag}(\lambda_1,\lambda_2)V^*), with (V) of column rank two and both eigenvalues nonzero. A nonzero two by two row minor of (V) gives a principal minor equal to (\lambda_1\lambda_2) times the squared modulus of that minor. Thus any rank-at-most-two completion admits a Schur argument after relabeling its internal pair.

The sign (\operatorname{Pf}(K)\prod_{i<j}k_{ij}) is invariant under such relabeling: each of the two factors changes by the sign of the permutation. Applying (5) in the successful partition proves necessity.

For sufficiency, (\phi=0) is already handled by (D=0). Suppose (\phi\prod k_{ij}<0). Then (5) has two nonzero real solutions. The resulting internal determinant for the pair (12) is

\[
\delta_{12}=\frac{x(r-q)}{t}.
\]

The corresponding determinants for the choices of internal pairs (13) and (14) vanish respectively only when (p+r=0) and (p=q). These three failures cannot occur together: they would give (r=q=p) and (p=-r), contradicting (pqr\ne0). Choose one of these nonsingular partitions, solve (3), and use (4). This proves sufficiency and completes the theorem.

The theorem makes no claim about the additional degenerate strata where some edge is zero. Those strata may have further completions; they are not needed for either the obstruction or the positive certificate below.

## 4. An exact successful completion

Take the upper edges

\[
(x,y,z,w,v,t)=(1,8/3,1,1,1,1),
\]

and

\[
D=\operatorname{diag}(4/3,-1/2,4/3,-1/2).
\]

Here (\phi=-2/3), (d_1d_2=-2/3), (yz,d_2+wv,d_1=0), and (\delta=-5/3). Formula (4) returns exactly the displayed last two diagonal entries. Thus (iK+D) has rank two. The companion exact certificate also verifies all its three by three minors vanish and one two by two minor is nonzero.

## 5. What this says about actual support Hessians

Suppose (A) is diagonal and the support objective is stationary at the base point. Imaginary diagonal tangent directions are then in the full Hessian kernel, including mixed pairings, because their left unitary action leaves the objective invariant. Consequently

\[
\operatorname{Hess}F(K-iD,K-iD)
=\operatorname{Hess}F(K,K).
\tag{6}
\]

If the real direction (K) has positive curvature and satisfies (2), then (K-iD) is a complex skew-Hermitian rank-two generator with the same positive curvature, since

\[
i(K-iD)=iK+D.
\]

Exponentiating a rank-two skew-Hermitian matrix fixes its kernel, so the unitary update differs from identity by rank at most two. This is an actual local complex rank-two escape.

If the sign in (2) is positive, only this particular diagonal-completion mechanism is ruled out. There may still be a different positive complex rank-two direction, a finite rank-two move, or a sequence of flat and improving moves. No support Hessian realization is asserted by the sign criterion alone.

## 6. A finite replacement: two commuting complex rank-two updates

**Proposition.** For every (O\in SO(4)), there are two commuting orthogonal projections (P_+,P_-) on (\mathbb C^4), each of rank two and with rank-one intersection, and real numbers (r_+,r_-), such that

\[
\boxed{O=e^{i(r_++r_-)}G_+G_-,\qquad
G_\pm=I+(e^{-2ir_\pm}-1)P_\pm.}
\tag{7}
\]

In particular each (G_\pm-I) has rank at most two and the scalar factor disappears in (OBO^T).

**Proof.** Real orthogonal spectral decomposition gives an orthonormal basis in which (O=\operatorname{diag}(R_\alpha,R_\beta)), including the possibilities of angles zero and (\pi). Let (J_1,J_2) be the oriented quarter-turn generators on those two mutually orthogonal real planes, extended by zero on the other plane, and conjugate them back to the original basis. They commute and satisfy

\[
J_1J_2=0,\qquad J_1^2+J_2^2=-I.
\]

Set

\[
S_+=J_1+J_2,\qquad S_-=J_1-J_2,
\qquad r_+=\frac{\alpha+\beta}{2},\quad
r_-=\frac{\alpha-\beta}{2}.
\]

Then (S_+,S_-) commute, both square to (-I), and

\[
O=e^{r_+S_+}e^{r_-S_-}.
\]

Each has two (+i) and two (-i) eigenvalues. Therefore

\[
P_\pm=\frac{I+iS_\pm}{2}
\]

are Hermitian orthogonal projections of rank two. They commute because the (S_\pm) commute. Their common (-i) eigenspace is one dimensional: it is the negative imaginary eigenspace of the first real plane. Thus their intersection has rank one. Finally the two scalar spectral calculations

\[
e^{-ir_\pm}e^{r_\pm S_\pm}
=I+(e^{-2ir_\pm}-1)P_\pm
\]

give (7). \(\square\)

If the starting real orthogonal matrix has determinant minus one, multiplying it on the right by a diagonal sign matrix changes its determinant and leaves its conjugation of a diagonal spectral matrix unchanged. Thus the same two-factor representation applies to its spectral conjugacy action.

## 7. Why this does not finish the scalar inequality

The determinant support after (G_+G_-) cannot be bounded by iterating a theorem that only applies when the base matrices commute: after applying one factor, the intermediate base generally does not commute. Commutativity of the two updating projections does not imply commutativity of that intermediate base with (A). Nor does (7) supply a monotone path; a factor may first lower and then raise the support.

The exact torus criterion in `continuous_rank_two_torus.md` concerns two rank-one axes, whose total update rank is at most two. In contrast, (7) uses two rank-two projections with a three-dimensional union. Its determinant can carry additional frequencies. A useful composition theorem must control these actual additional terms or reduce the shared one-dimensional intersection with a justified support argument.

All numerical examples asserted in this note are verified using exact Gaussian rational arithmetic in `code/theorems/finite_and_spin_geometry/continuous_third_batch_exact.py`. The proofs above specify the full scope, including the nonzero-edge hypothesis and the distinction between local gauge completion and finite factorization.

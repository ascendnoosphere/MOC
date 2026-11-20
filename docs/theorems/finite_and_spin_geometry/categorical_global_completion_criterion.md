# An exact phase-completion criterion for every real four-dimensional orthogonal matrix

## Result and scope

Let \(O\in SO(4)\). For each column permutation \(\pi\), orient the
permuted matrix by changing the sign of its first column when needed:

\[
W_\pi=\Pi_\pi\operatorname{diag}(\det\Pi_\pi,1,1,1),
\qquad V_\pi=OW_\pi\in SO(4).
\]

For \(V=V_\pi\), use one-based labels and put

\[
a=\det V[123,124]=-V_{43},\quad
b=-\det V[23,24],\quad c=-\det V[13,14],\quad d=V_{34},
\]

\[
\Delta(V)=4(ab-cd)^2-(a^2+b^2-c^2-d^2)^2.
\]

Then, with **no assumption on entries, minors, or feedback denominators**,

\[
\boxed{\exists\text{ diagonal unitary }Z:\ \operatorname{rank}(V-Z)\le2
       \quad\Longleftrightarrow\quad \Delta(V)\ge0.}
\tag{1}
\]

Consequently

\[
\boxed{\exists\text{ monomial unitary }M:\operatorname{rank}(O-M)\le2
       \quad\Longleftrightarrow\quad
       \max_{\pi\in S_4}\Delta(OW_\pi)\ge0.}
\tag{2}
\]

The quaternion identity in QUATERNION_PHASE_COMPLETION.md, already checked
there by exact integer polynomial arithmetic, is the main algebraic input:

\[
V=L(q)R(r),\quad \|q\|=\|r\|=1
\quad\Longrightarrow\quad
\Delta(V)=-16\prod_{i=0}^3(q_i^2-r_i^2).
\tag{3}
\]

The new point of this note is the complete treatment of all degenerate
matrices. It does not prove the proposed common-law-or-rank-two disjunction,
and it does not prove scalar Marcus–de Oliveira.

## 1. Necessity without a Schur complement

Suppose \(Z=\operatorname{diag}(z_1,z_2,z_3,z_4)\), all \(|z_i|=1\),
and \(\operatorname{rank}(V-Z)\le2\). The three-by-three minor with rows
123 and columns 124 must vanish. Its expansion is

\[
p(z_1,z_2)=a+bz_1+cz_2+dz_1z_2=0.
\tag{4}
\]

This is a minor identity, so it holds even when every prospective Schur
complement is singular. A bilinear polynomial with real coefficients has
a zero on the two-torus if and only if

\[
|a^2+b^2-c^2-d^2|\le2|ab-cd|.
\tag{5}
\]

Indeed, for a fixed \(|z_1|=1\), solving for \(z_2\) requires
\(|a+bz_1|=|c+dz_1|\). Their squared-modulus difference equals
\(a^2+b^2-c^2-d^2+2(ab-cd)\Re z_1\), whose range is the interval centered
at the first term with radius \(2|ab-cd|\). If both linear expressions
vanish, any \(z_2\) works; otherwise their quotient supplies a unit-modulus
solution. Thus (5), including its coefficient degeneracies, is equivalent
to \(\Delta\ge0\). This proves necessity in (1).

## 2. Sufficiency when the cross block is invertible

Write

\[
V=\begin{pmatrix}A&B\\C&E\end{pmatrix},
\]

with two-by-two blocks. If \(C\) is invertible, unitarity gives

\[
I-A^*A=C^*C\succ0,
\]

so \(\|A\|<1\). Hence \(A-Z_0\) is invertible for **every** two-by-two
diagonal unitary \(Z_0\): an equality \(Ax=Z_0x\) for a nonzero vector
would contradict strict contraction.

For \(Z_0=\operatorname{diag}(z_1,z_2)\), the feedback matrix

\[
F(Z_0)=E-C(A-Z_0)^{-1}B
\]

is unitary. To see this, put \(x=(Z_0-A)^{-1}By\), so the first component
of \(V(x,y)\) is \(Z_0x\) and the second is \(F(Z_0)y\). Norm preservation
then gives \(\|F(Z_0)y\|=\|y\|\).

Its upper-right entry has numerator (4) and denominator
\(\det(A-Z_0)\). When \(\Delta\ge0\), choose a torus zero of (4).
Then this entry of \(F(Z_0)\) vanishes. A two-by-two unitary with one
vanishing off-diagonal entry is diagonal, say \(Z_1\). The Schur-complement
identity now gives

\[
\operatorname{rank}
\begin{pmatrix}A-Z_0&B\\C&E-Z_1\end{pmatrix}=2.
\]

This proves sufficiency for every matrix with invertible \(C\), including
\(\Delta=0\). No separate assumption on \(B\) is needed.

## 3. Every zero discriminant is approached by positive discriminants

We prove this directly on the probability simplices underlying (3).
Let

\[
p_i=q_i^2,\qquad s_i=r_i^2,\qquad \delta_i=p_i-s_i.
\]

Then \(p,s\) are probability vectors and \(\sum_i\delta_i=0\). Suppose
\(\Delta=0\), so at least one \(\delta_i\) is zero.

First move both vectors into the open simplex by

\[
p^{(\varepsilon)}=(1-\varepsilon)p+\varepsilon(1/4,1/4,1/4,1/4),
\qquad
s^{(\varepsilon)}=(1-\varepsilon)s+\varepsilon(1/4,1/4,1/4,1/4).
\]

Their difference is \((1-\varepsilon)\delta\), and every coordinate is
at least \(\varepsilon/4\). We may therefore make any additional
zero-sum difference perturbation of size \(o(\varepsilon)\), split equally
between the two probability vectors, while preserving strict positivity.

If \(\delta\ne0\), its nonzero entries include both signs. Since at least
one entry is zero, one of the two signs occurs exactly once among the
nonzero entries. Give all formerly zero entries the other sign, with
sufficiently small magnitudes, and compensate their sum by a small change
to an already nonzero coordinate. The original nonzero signs remain
unchanged. The resulting difference has exactly one positive and three
negative entries, or exactly three positive and one negative entry.

If \(\delta=0\), use a sufficiently small positive multiple of
\((-3,1,1,1)\) as the new difference. This also has the required sign
pattern. In every case the product of the four difference coordinates is
strictly negative, so (3) gives \(\Delta>0\).

Finally lift the perturbed probability vectors back to quaternions:
use \(q_i^{(\varepsilon)}=\operatorname{sgn}(q_i)\sqrt{p_i^{(\varepsilon)}}\)
at originally nonzero coordinates, choosing either sign at an originally
zero coordinate; do the same for \(r\). The resulting unit quaternions
converge to \(q,r\). The square-root lift is continuous at zero, so zero
probability coordinates introduce no exception. This proves

\[
\{V\in SO(4):\Delta(V)=0\}
\subseteq\overline{\{V\in SO(4):\Delta(V)>0\}}.
\tag{6}
\]

## 4. Density of regular cross blocks

The function \(V\mapsto\det C\) is real analytic on the connected real
analytic manifold \(SO(4)\), and it is not identically zero: an oriented
permutation matrix exchanging the two coordinate blocks has invertible
\(C\). Its zero set therefore has empty interior.

Every open set on which \(\Delta>0\) consequently contains a matrix with
invertible \(C\). Combining this fact with (6), every matrix with
\(\Delta\ge0\) is a limit of matrices satisfying both
\(\Delta>0\) and \(\det C\ne0\). Each approximating matrix has a diagonal
rank-two completion by Section 2.

## 5. Compactness closes the argument

If \(V_k\to V\) and diagonal unitaries \(Z_k\) satisfy
\(\operatorname{rank}(V_k-Z_k)\le2\), compactness of the four-torus gives
a subsequence with \(Z_k\to Z\), where \(Z\) is diagonal unitary. Every
three-by-three minor of \(V_k-Z_k\) vanishes. Taking limits shows that
every such minor of \(V-Z\) vanishes, hence
\(\operatorname{rank}(V-Z)\le2\). Thus the completion set is closed,
and Sections 3–4 prove sufficiency in (1) at all remaining points.

For (2), right multiplication by a monomial unitary preserves ranks.
Given any monomial \(M\), one of the \(W_\pi\) makes \(MW_\pi\) diagonal;
its phases absorb the orientation-correcting sign. Conversely, a diagonal
completion of \(OW_\pi\) becomes a monomial completion of \(O\) after
multiplication by \(W_\pi^*\).

## 6. Exact implication for the common-law bridge

The accepted facet classification in COMMON_MINOR_POLYTOPE.md says that
an actual kernel fails the common permutation hull precisely when one of
the 48 row/column relabelings of the representative facet \(f\) is negative.
Combining that theorem with (2), the structural disjunction is now
**exactly** the following finite semialgebraic statement:

\[
f(R(O))<0\quad\Longrightarrow\quad
\max_{\pi\in S_4}\Delta(OW_\pi)\ge0,
\qquad O\in SO(4).
\tag{7}
\]

There are no singular-chart qualifications left in (7). Establishing (7)
remains an open step in this research campaign. Even a proof of (7) would
still require the scalar rank-two MOC theorem to complete that route.

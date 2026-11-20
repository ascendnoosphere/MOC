# A sharp common-minor facet bound for every complex unitary matrix of order four

## Result and logical scope

Let \(U\in U(4)\). For a row set \(I\) and column set \(J\) of equal size, write
\(\rho_{I,J}(U)=|\det U[I,J]|^2\). Single indices denote singleton sets. Define

\[
f(U)=\rho_{3,3}+\rho_{2,4}+\rho_{12,13}-\rho_{13,23}.
\tag{1}
\]

Let \(t\) be the unique real root of

\[
t^3+t^2+3t-1=0,
\tag{2}
\]

and put

\[
\delta=\frac{t(1-t^2)}4.
\tag{3}
\]

Then

\[
\boxed{\min_{U\in U(4)} f(U)=-\delta
       \quad\text{with}\quad \delta\approx0.067442248868.}
\tag{4}
\]

Every permutation matrix has \(f\ge0\). Thus (4) quantifies, sharply, the failure of this common-minor permutation inequality on actual unitaries. It is a result about a stronger common-law conjecture, and is not a MOC counterexample.

The algebraic identities below are checked by code/theorems/finite_and_spin_geometry/dual_common_facet_sharp_exact.py. The global minimization is proved here by angle elimination and concavity, rather than inferred from optimization samples.

## 1. The anchored profile form

Use rows \(r,v,s,t_{\rm row}\), in that order, with \(v\) the anchor. Put

\[
R_i=|r_i|^2,\quad S_i=|s_i|^2,\quad
P_{ij}=|r_iv_j-r_jv_i|^2,\quad
Q_{ij}=|s_iv_j-s_jv_i|^2.
\]

The same functional is

\[
f=R_1+S_3-P_{12}+Q_{14}.
\tag{5}
\]

Indeed, with \(m_i=|v_i|^2\), the third anchor wedge satisfies
\(P^{t_{\rm row}}_{ij}=m_i+m_j-P_{ij}-Q_{ij}\).
Complementarity gives
\(\rho_{13,23}=P^{t_{\rm row}}_{14}\), while
\(\sum_{j\ne1}P_{1j}=R_1+m_1\). Substituting these two identities in (1) proves (5).

## 2. Quaternion coordinates

Every real special orthogonal matrix of order four has the form
\(O=L(q)R(r)\), with \(q,r\) unit real quaternions. Here \(L\) and \(R\) are ordinary left and right quaternion multiplication, so that

\[
L(q)=
\begin{pmatrix}
q_0&-q_1&-q_2&-q_3\\
q_1&q_0&-q_3&q_2\\
q_2&q_3&q_0&-q_1\\
q_3&-q_2&q_1&q_0
\end{pmatrix},
\]

\[
R(r)=
\begin{pmatrix}
r_0&-r_1&-r_2&-r_3\\
r_1&r_0&r_3&-r_2\\
r_2&-r_3&r_0&r_1\\
r_3&r_2&-r_1&r_0
\end{pmatrix}.
\]

Expanding (1), using the two unit norm identities, gives the sparse quartic

\[
\begin{aligned}
f(q,r)={}&(q_0^2-q_2^2)(q_3^2-q_1^2)
 +(r_0^2-r_2^2)(r_3^2-r_1^2)\\
&+(q_0r_0-q_2r_2)^2+(q_0r_2-q_2r_0)^2\\
&+(q_1r_1+q_3r_3)^2+(q_1r_3+q_3r_1)^2.
\end{aligned}
\tag{6}
\]

The original integer expansion is recorded in code/theorems/finite_and_spin_geometry/root_quaternion_completion_exact.py. The companion verifier independently expands the right side of (6) and checks equality with its eighteen monomials.

## 3. Eliminate all four angles exactly

Write

\[
X=q_0^2+q_2^2,\quad Y=1-X,\qquad
U=r_0^2+r_2^2,\quad V=1-U.
\]

The following four vectors range independently over circles of the stated radii:

\[
\begin{array}{c|c}
\text{vector}&\text{radius}\\ \hline
(a,x)=(q_0^2-q_2^2,\;2q_0q_2)&X\\
(b,y)=(q_3^2-q_1^2,\;2q_1q_3)&Y\\
(c,u)=(r_0^2-r_2^2,\;2r_0r_2)&U\\
(d,v)=(r_3^2-r_1^2,\;2r_1r_3)&V
\end{array}
\]

Equation (6) becomes

\[
f=ab+cd+XU+YV-xu+yv.
\tag{7}
\]

Hold the second and third circle vectors fixed. Minimizing over the first and fourth gives

\[
XU+YV-X\sqrt{b^2+u^2}-V\sqrt{c^2+y^2}.
\tag{8}
\]

Since \(u^2=U^2-c^2\) and \(y^2=Y^2-b^2\), put \(w=b^2-c^2\).
The variable \(w\) ranges over the entire interval \([-U^2,Y^2]\).
Thus \(z=U^2+w\) ranges over \([0,U^2+Y^2]\), and the two squared radicals in (8) are \(z\) and \(U^2+Y^2-z\).

Cauchy's inequality is attained:

\[
\max_{0\le z\le U^2+Y^2}
\left(X\sqrt z+V\sqrt{U^2+Y^2-z}\right)
=\sqrt{(X^2+V^2)(U^2+Y^2)}.
\tag{9}
\]

For \(X^2+V^2>0\), the maximizing value is
\(z=(U^2+Y^2)X^2/(X^2+V^2)\), which lies in the permitted interval.
If \(X=V=0\), both sides vanish. The choices of circle angles giving each admissible \(z\) exist because \(b^2,c^2\) vary independently over their full intervals.

Consequently the exact angular minimum is

\[
m(X,U)=XU+(1-X)(1-U)
-\sqrt{\bigl(X^2+(1-U)^2\bigr)
       \bigl((1-X)^2+U^2\bigr)}.
\tag{10}
\]

No inequality has been lost in passing from (6) to (10), including at degenerate radii.

## 4. A radial concavity argument reduces the square to its boundary

Set

\[
p=X+U-1,\qquad d=X-U.
\]

The square \(0\le X,U\le1\) becomes the diamond \(|p|+|d|\le1\), and (10) becomes

\[
m=\frac12\left[
1+p^2-d^2-\sqrt{(1+p^2+d^2)^2-4d^2}
\right].
\tag{11}
\]

This depends only on \(p^2,d^2\). On each ray write
\(|p|=\rho a,\ |d|=\rho b\), where \(a,b\ge0,\ a+b=1,\ 0\le\rho\le1\).
With \(s=\rho^2\), \(C=a^2-b^2\), and \(D=(a^2+b^2)^2\), the value is

\[
g(s)=\frac12\left(1+Cs-\sqrt{1+2Cs+Ds^2}\right).
\tag{12}
\]

If \(a,b>0\), the radical is positive and

\[
g'(0)=0,\qquad
g''(s)=-\frac{D-C^2}
 {2(1+2Cs+Ds^2)^{3/2}}
=-\frac{2a^2b^2}
 {(1+2Cs+Ds^2)^{3/2}}<0.
\tag{13}
\]

Hence \(g\) decreases along that ray, and its minimum is at \(\rho=1\).
If \(a=0\) or \(b=0\), (12) is identically zero on the permitted interval, including its endpoint by continuity.

Therefore the global minimum occurs on the diamond boundary, equivalently where at least one of \(X,U\) equals \(0\) or \(1\). The four sides reduce by substitution to the same one-variable problem:

\[
\min m=-\max_{0\le y\le1}
(1-y)(\sqrt{1+y^2}-1).
\tag{14}
\]

This proves the boundary reduction globally, including the corners at which a derivative expression for the radical could otherwise be singular.

## 5. Solve the remaining one-variable problem

Let

\[
C_0(y)=(1-y)(\sqrt{1+y^2}-1).
\]

Its endpoint values are zero and it is positive in the interior.
For \(y>0\), a stationary point satisfies

\[
\sqrt{1+y^2}=1+2y^2-y.
\tag{15}
\]

The right side is positive for all real \(y\), so squaring introduces no sign ambiguity. The difference of squares factors as

\[
(1+2y^2-y)^2-(1+y^2)
=2y(2y^3-2y^2+2y-1).
\tag{16}
\]

The cubic on the right has derivative \(6y^2-4y+2>0\), takes opposite signs at \(0\) and \(1\), and therefore has exactly one root in the interval. The derivative of \(C_0\) changes from positive to negative there, so that root is its unique maximum.

At the maximizing root, (15) gives

\[
C_0(y)=y(1-y)(2y-1).
\]

Set \(t=2y-1\). The cubic becomes (2), and

\[
C_0(y)=\frac{t(1-t^2)}4=\delta.
\]

The derivative of (2) is \(3t^2+2t+3>0\). Exact evaluations give
\(p(29/100)<0<p(3/10)\), so \(29/100<t<3/10\). In particular,

\[
0<\delta<\frac3{40}.
\tag{17}
\]

Combining Sections 2–5 proves the lower bound for every \(O\in SO(4)\).

## 6. An explicit matrix attaining the bound

For a real parameter \(t\), define

\[
O(t)=\frac1{\sqrt{t^2+3}}
\begin{pmatrix}
t&1&1&-1\\
-1&1&-1&-t\\
-1&-1&t&-1\\
-1&t&1&1
\end{pmatrix}.
\tag{18}
\]

Its rows are orthonormal and its determinant is \(1\). Direct use of (5) gives

\[
-f(O(t))=\frac{4t}{(t^2+3)^2}
-\frac{2t^2}{t^2+3}.
\tag{19}
\]

At the root of (2), this equals \(\delta\). After clearing the positive denominator, the difference of (19) and (3) is divisible by the cubic (2); the exact verifier checks this identity.

Thus the lower bound is attained, completing the real special orthogonal case. Row sign changes preserve every squared minor, so the same bound holds on all of \(O(4)\).

## 7. Extension from real orthogonal to complex unitary profiles

This step uses the special three-dimensional anchor complement.

Make the anchor row \(v\) real by column phases. The other three rows define real symmetric effects

\[
E_\alpha=\operatorname{Re}(r_\alpha r_\alpha^*)\bigm|_{v^\perp},
\qquad \alpha=R,S,T.
\]

They are PSD, have trace one, and sum to the identity on the three-dimensional real space \(v^\perp\). Every anchored singleton and wedge coordinate is linear in the corresponding \(E_\alpha\).

We prove that any such triple is a convex combination of rank-one orthogonal frames. Consider an extreme triple. If all three effects have rank at least two, the space of symmetric perturbations supported in their ranges has dimension at least \(3+3+3=9\). The constraints that each perturbation has trace zero and their sum is zero impose at most eight independent equations: six sum equations and three traces, with one redundant trace equation. There is consequently a nonzero supported perturbation satisfying every constraint. A sufficiently small perturbation in either sign preserves PSD, contradicting extremality.

At least one effect at an extreme point has rank one. Its trace being one, it is an orthogonal projection \(ww^T\). The remaining two effects vanish on \(w\), are supported on the two-dimensional complement, and sum to its identity. They commute and can be diagonalized together. Their trace-one condition makes them a convex combination of the two ordered orthogonal rank-one frames on that complement. Unless the original triple is already a frame, this again contradicts extremality.

Hence every extreme triple is a frame. Compactness and finite-dimensional convexity now express every effect triple as a finite mixture of frames. The corresponding real orthogonal matrices have the same anchor, and their averaged twenty profiles equal the original complex profile.

Applying the real bound to each frame and averaging proves (4) for every complex unitary \(U\). The real matrix (18) remains an attainer in the complex class.

This argument is dimension-specific. The analogous effect purification is false for an anchor complement of dimension four.

## 8. Relabelings

Column permutations and permutations of the three nonanchor rows preserve the twenty-profile moment lift described in dual_outer_profile_geometry.md. Their orbit of (1), modulo the affine profile identities, consists of 48 distinct functionals. Each vanishes on thirteen affinely independent permutation vertices and defines a facet of the thirteen-dimensional common-minor permutation polytope. The companion integer verifier checks the orbit size and face dimensions.

Every one of these 48 inequalities therefore has the same sharp actual-unitary correction \(-\delta\).

## Verification files

- code/theorems/finite_and_spin_geometry/dual_common_facet_sharp_exact.py: exact quartic, one-variable, orthogonality, attainer, and orbit identities.
- code/theorems/finite_and_spin_geometry/root_quaternion_completion_exact.py: the initial quaternion minor expansion.
- dual_outer_profile_geometry.md: the complete normalized dual construction and its scope.


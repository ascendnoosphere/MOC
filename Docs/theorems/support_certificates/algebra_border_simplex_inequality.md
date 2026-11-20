# The complementary tetrahedral simplex inequality

## Status and consequence

This note proves the second sharp probability-vector inequality requested
after the initial ten algebra investigations:

\[
\boxed{
\frac12\|p-q\|_2^2+
8\left(\sqrt{\prod_i p_i}+\sqrt{\prod_i q_i}\right)\le1,
\qquad p,q\in\mathbb R_{\ge0}^4,\quad
\sum_i p_i=\sum_i q_i=1.
}
\tag{1}
\]

Together with the exact quaternion formulas, it gives the universal
order-four profile inequality

\[
\boxed{Y+|Z|\le1.}
\tag{2}
\]

It therefore proves the full \(x=0\) component of the restricted nonic,
including the points that only have border-secant representations.
Consequently the complete tetrahedrally symmetric support theorem extends
from actual costs to every real cost on the projected spectral secant
closure.

The proof below is independent of a numerical search. Its polynomial
certificates are in algebra_border_simplex_exact.py. The polyhedral agent
also produced an exact outer profile satisfying the previous nonnegative
minor and relabeled-hard-ray inequalities but violating (2), so (2)
adds an inequality outside that finite certificate cone. No historical novelty claim is made.

## 1. Objective and boundary

Write

\[
P=\sqrt{\prod_i p_i},\qquad Q=\sqrt{\prod_i q_i},
\qquad
W(p,q)=\frac12\|p-q\|_2^2+8(P+Q).
\]

The product of the two simplices is compact. We prove that every boundary
point and every interior stationary point has \(W\le1\).

Suppose \(P=0\). On the boundary face containing \(p\), the expression
\(W(p,q)\), with \(q\) fixed, is a convex quadratic in \(p\). Every point
on that face is a convex combination of its vertices, so it is enough
to prove the bound with \(p=e_i\). More explicitly,

\[
\sum_i p_iW(e_i,q)-W(p,q)
=\frac12(1-\|p\|_2^2)\ge0.
\tag{3}
\]

By relabeling, let \(p=e_1\), \(q=(t,a,b,c)\), where
\(t+a+b+c=1\). Then

\[
\begin{aligned}
1-W(e_1,q)
&=t^2+2t(a+b+c)+ab+ac+bc-8\sqrt{tabc}\\
&=t^2+
\sum_{\mathrm{cyc}(a,b,c)}
\left[
2\left(\sqrt{ta}-\frac23\sqrt{bc}\right)^2
+\frac19bc
\right]\ge0.
\end{aligned}
\tag{4}
\]

This is an exact sum-of-squares certificate. Interchanging \(p,q\)
handles \(Q=0\).

The boundary equality cases are precisely \(p=e_i,q=e_j\), \(i\ne j\).
Indeed (3) is strict unless \(p\) is a vertex. At a vertex, equality
in (4) forces \(t=0\) and \(ab+ac+bc=0\), so \(q\) is a different
vertex.

## 2. Interior stationary equations

At an interior stationary point, put

\[
A=4P>0,\qquad B=4Q>0.
\]

The Lagrange equations are

\[
p_i-q_i+\frac A{p_i}=\alpha,\qquad
q_i-p_i+\frac B{q_i}=\beta.
\tag{5}
\]

Multiply the first by \(p_i\), the second by \(q_i\), and sum. This gives

\[
\gamma:=\alpha+\beta
=\|p-q\|_2^2+16(P+Q)=2W>0.
\tag{6}
\]

Adding the equations in (5) gives

\[
\frac A{p_i}+\frac B{q_i}=\gamma,\qquad
q_i=\frac{Bp_i}{\gamma p_i-A}.
\tag{7}
\]

The denominator is positive. The rational function in (7) has derivative

\[
-\frac{AB}{(\gamma p-A)^2}<0.
\tag{8}
\]

Thus unequal \(p\)-coordinates have strictly oppositely ordered
\(q\)-coordinates. Equal coordinates in either vector imply equality
in the other by (5).

Eliminating \(q_i\) from (5) and (7), every \(p_i\) is a root of

\[
\boxed{
\gamma z^3-(\gamma\alpha+A+B)z^2
+A(\gamma+\alpha)z-A^2=0.
}
\tag{9}
\]

There can therefore be at most three distinct coordinate-pair types.

## 3. Three pair types have value \(4/5\)

Suppose the multiplicities are \(2+1+1\), and write

\[
p=(t,t,a,b),\qquad q=(u,u,c,d).
\]

The three distinct roots of (9) are \(t,a,b\). Since
\(A^2=16P^2=16t^2ab\), comparison with the root product gives

\[
tab=\frac{A^2}{\gamma}
=\frac{16t^2ab}{\gamma},
\qquad \gamma=16t.
\tag{10}
\]

The symmetric cubic in \(q\) gives \(\gamma=16u\), hence \(u=t\).

Set \(r=\sqrt{ab}\), \(s=\sqrt{cd}\). Then
\(P=tr,Q=ts\), and the repeated coordinates in (5) give

\[
\alpha=4r,\qquad\beta=4s.
\tag{11}
\]

Sum the first equation of (5) over the two unrepeated coordinates.
The sums \(a+b=c+d=1-2t\) cancel, leaving

\[
\frac{4t(1-2t)}r=8r,
\qquad r^2=\frac{t(1-2t)}2.
\tag{12}
\]

The same argument gives \(s^2=t(1-2t)/2\), so \(r=s>0\).
Equations (10)--(11) yield

\[
16t=\gamma=8r,\qquad r=2t.
\]

Substitution in (12) gives \(t=1/10\). Hence

\[
\boxed{W=\gamma/2=4/5<1.}
\tag{13}
\]

It is not necessary to exclude these stationary points. They really
exist, for example at

\[
p=\left(\frac1{10},\frac1{10},
\frac{2+\sqrt3}{5},\frac{2-\sqrt3}{5}\right),
\]

with \(q\) obtained by swapping the last two coordinates.

## 4. Two pair types

### 4.1 Multiplicities two and two

Write

\[
p=(1/4+s,1/4+s,1/4-s,1/4-s),
\]

\[
q=(1/4+t,1/4+t,1/4-t,1/4-t).
\]

Direct substitution gives the exact identity

\[
\boxed{
W(p,q)=1-4(s+t)^2-2(s-t)^2\le1.
}
\tag{14}
\]

Equality requires \(s=t=0\), the uniform point.

### 4.2 Multiplicities one and three

Write

\[
p=(a,b,b,b),\qquad q=(c,d,d,d),
\qquad a+3b=c+3d=1.
\]

Set \(r=\sqrt{a/b}\), \(s=\sqrt{c/d}\). Subtract the stationary
equations between the distinguished and repeated coordinates:

\[
(a-b)(1-4/r)=c-d,\qquad
(c-d)(1-4/s)=a-b.
\tag{15}
\]

If a difference is zero, both vectors are uniform. Otherwise, cancel
the nonzero differences after multiplying (15). The result is

\[
(1-4/r)(1-4/s)=1,\qquad r+s=4.
\tag{16}
\]

Equation (8) says that \(a-b\) and \(c-d\) have opposite signs.
Interchanging the two vectors if needed, take \(r>1\), \(0<s<1\).
Equation (16) then gives \(3<r<4\). Thus

\[
v=rs\in(0,3).
\tag{17}
\]

Since \(b=1/(r^2+3)\), \(d=1/(s^2+3)\), equation (7) at the
repeated coordinate gives

\[
W=\frac{\gamma}{2}
=2\left(\frac r{r^2+3}+\frac s{s^2+3}\right)
=\frac{8v+24}{v^2-6v+57}.
\tag{18}
\]

Consequently

\[
\boxed{
1-W=\frac{(3-v)(11-v)}{v^2-6v+57}>0.
}
\tag{19}
\]

## 5. Completion and equality

The only remaining case has one coordinate-pair type: both vectors are
uniform, and \(W=1\). We have covered every interior stationary point,
and Section 1 covers the entire boundary. Compactness proves (1).

The complete equality set is

\[
\boxed{
p=q=(1/4,1/4,1/4,1/4),
\quad\text{or}\quad
p=e_i,\ q=e_j,\ i\ne j.
}
\tag{20}
\]

## 6. The profile inequality

For the quaternion model of a real orthogonal matrix of order four,
write \(p_i=\xi_i^2,q_i=\eta_i^2\), where \(\xi,\eta\) are unit
quaternions. The exact profile formulas are

\[
X=2-\|p\|_2^2-\|q\|_2^2,\qquad
Y=\frac12\|p-q\|_2^2,
\]

\[
Z=8\left(\prod_i\xi_i-\prod_i\eta_i\right)
\]

with the orientation convention of the companion notes. Therefore

\[
Y+|Z|
\le \frac12\|p-q\|_2^2+8(P+Q)\le1.
\tag{21}
\]

Row signs preserve squared minors, so both components of \(O(4)\) are
covered. The previously proved order-four complex-to-real convexification
of common-minor profiles extends each linear inequality \(Y+Z\le1\)
and \(Y-Z\le1\) to every complex \(U(4)\).

## 7. Completion of the entire symmetric projected-secant closure

On the nonic component \(x=0\), the support height is
\(h=\max(0,y,|k|)\). Since \(Y\ge0\) and (2) holds,

\[
yY+kZ\le hY+h|Z|\le h.
\tag{22}
\]

Thus no finite-realization assumption is needed on this component.
The other two nonic components were already proved in
algebra_a4_full_support_theorem.md. The strengthened theorem is:

**Every real tetrahedrally symmetric cost on the projected M8 secant
closure satisfies the full order-four unitary support inequality.**

This remains a restricted theorem. A general spectral cost or its
tetrahedral average is not thereby placed on the same symmetric
nonic intersection.


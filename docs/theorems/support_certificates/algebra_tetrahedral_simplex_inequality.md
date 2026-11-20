# A tetrahedral simplex inequality and one complex MOC theorem

## Status and scope

The probability-vector inequality proved below, together with the exact Hodge
and quaternion identities in root_quaternion_reduction_exact.py, completes
the hard support inequalities for the explicit complex spectral pair in
algebra_a4_real_form_and_full_unitary_target.md. The argument proves MOC
for that pair, in every unitary conjugation and every support direction.

The result does not prove unrestricted complex MOC. In particular, averaging
a general actual spectral cost over the alternating group need not preserve
the spectral nonic. All identities and deductions in this note were obtained
during this research campaign; no novelty priority is asserted.

## 1. The simplex inequality

**Theorem.** If \(p,q\in\mathbb R_{\ge0}^4\) and
\(\sum_i p_i=\sum_i q_i=1\), then

\[
\boxed{\Phi(p,q):=
\sum_i p_i^2+\sum_i q_i^2+4\sum_i p_iq_i-1
-4\sqrt{\prod_i p_i}-4\sqrt{\prod_i q_i}\ge0.}
\tag{1}
\]

The proof uses compactness, an exact boundary estimate, and a complete
classification of the possible multiplicities at an interior stationary
point.

### 1.1 Both products vanish

Put \(P=\sqrt{\prod_i p_i}\) and \(Q=\sqrt{\prod_i q_i}\).
If \(P=Q=0\), then

\[
\Phi(p,q)=\|p+q\|_2^2+2p\cdot q-1\ge0,
\tag{2}
\]

because \(\sum_i(p_i+q_i)=2\), so \(\|p+q\|_2^2\ge1\).

### 1.2 A vector supported on at most two coordinates

By simultaneous relabeling and symmetry in the two vectors, suppose
\(p=(t,1-t,0,0)\). For fixed \(q\), minimizing the quadratic dependence
on \(t\) over the entire real line gives a lower bound. Write
\(u=q_1q_2\), \(v=q_3q_4\). Direct completion of the square gives

\[
\Phi(p,q)\ge \frac12+6u-2v-4\sqrt{uv}.
\tag{3}
\]

Also \(q_1+q_2\ge2\sqrt u\), and therefore

\[
0\le v\le\frac{(1-2\sqrt u)^2}{4},
\qquad 0\le\sqrt u\le\frac12.
\tag{4}
\]

The right side of (3) decreases with \(v\). Substituting the upper bound
from (4) gives exactly \(8u\ge0\). This proves the required boundary case,
including support one.

### 1.3 A support-three vector cannot cause a negative global minimum

Suppose \(p_4=0\), \(p_1p_2p_3>0\), and \(Q>0\).
For small \(\varepsilon>0\), replace \(p_4\) by \(\varepsilon\) and
\(p_1\) by \(p_1-\varepsilon\), leaving everything else fixed. The
polynomial part of \(\Phi\) changes by \(O(\varepsilon)\), whereas

\[
-4\sqrt{\prod_i p_i(\varepsilon)}
=-4\sqrt{p_1p_2p_3}\sqrt{\varepsilon}
+O(\varepsilon^{3/2}).
\tag{5}
\]

Consequently \(\Phi\) strictly decreases for sufficiently small positive
\(\varepsilon\). Such a boundary point cannot be a global minimum.
If \(Q=0\), equation (2) already proves nonnegativity.

The compact domain thus has no negative global minimum on its boundary.
It remains to show that every interior stationary point has
\(\Phi\ge0\).

## 2. Interior stationary points

At an interior stationary point, \(P,Q>0\). Use half the ordinary
Lagrange multipliers and write the stationary equations as

\[
p_i+2q_i-\frac{P}{p_i}=\alpha,\qquad
q_i+2p_i-\frac{Q}{q_i}=\beta.
\tag{6}
\]

Equal \(p\)-coordinates imply equal \(q\)-coordinates by the first
equation; equal \(q\)-coordinates imply equal \(p\)-coordinates by the
second. Thus the multiplicity partitions of the four pairs
\((p_i,q_i)\) agree with those of either coordinate vector.

Multiplying (6) by \(p_i,q_i\) respectively and summing gives the useful
identity

\[
\alpha+\beta=\Phi(p,q)+1.
\tag{7}
\]

### 2.1 At most three distinct coordinate pairs

Eliminate

\[
q_i=\frac{-p_i^2+\alpha p_i+P}{2p_i}
\]

from the other stationary equation. Every positive \(p_i\) is a root
of the quartic

\[
\begin{aligned}
f(z)={}&-3z^4+2(\alpha+\beta)z^3\\
&+(\alpha^2-2\alpha\beta+2P-4Q)z^2\\
&+2P(\alpha-\beta)z+P^2.
\end{aligned}
\tag{8}
\]

If all four \(p_i\) were distinct, they would be all the roots of \(f\);
their product would be \(-P^2/3<0\), which is impossible. There are at
most three distinct coordinate pairs.

### 2.2 Three distinct coordinate pairs are impossible

Assume there are exactly three pair types, and relabel them as

\[
p=(t,t,a,b),\qquad q=(u,u,c,d).
\tag{9}
\]

Here \(t,a,b\) are distinct, and so are \(u,c,d\).
Since \(P^2=t^2ab\), the fourth root of the quartic (8), whose other
three roots are \(t,a,b\), equals \(-t/3\). Comparing the root sum with
the cubic coefficient gives

\[
2(\alpha+\beta)=3-4t.
\tag{10}
\]

Apply the same quartic argument after interchanging \(p,q\). It gives
\(2(\alpha+\beta)=3-4u\), hence \(u=t\).

Put \(r=\sqrt{ab}\), \(s=\sqrt{cd}\). Then \(P=tr\), \(Q=ts\), and
the repeated coordinates in (6) give

\[
\alpha=3t-r,\qquad\beta=3t-s.
\tag{11}
\]

Sum the first equation in (6) over the two unrepeated coordinates.
Using \(a+b=c+d=1-2t\) and \(1/a+1/b=(1-2t)/r^2\), this becomes

\[
2r^2-(12t-3)r-t(1-2t)=0.
\tag{12}
\]

The symmetric argument gives the same equation for \(s\).
Since \(0<t<1/2\), its constant term is negative. The quadratic therefore
has exactly one positive root, so \(r=s\). It follows that
\(P=Q\), \(\alpha=\beta\), and the pairs \((a,b)\), \((c,d)\) have the
same sum and product.

If \((c,d)=(a,b)\), then \(p=q\). Equation (6) makes
\(3p_i-P/p_i\) constant; this expression is strictly increasing on
positive arguments, forcing uniformity, a contradiction.

Otherwise \((c,d)=(b,a)\), with \(a\ne b\). Subtract the two equations
in (6):

\[
(p_i-q_i)\left(\frac{P}{p_iq_i}-1\right)=0.
\tag{13}
\]

For an unrepeated coordinate this implies \(ab=P=tr\), hence
\(r^2=tr\) and \(r=t\). Now (11) gives \(\alpha+\beta=4t\).
Combining with (10) yields \(t=1/4\). But then
\(a+b=1/2\), \(ab=1/16\), forcing \(a=b=1/4\), again a contradiction.

There are no interior stationary points with exactly three distinct
coordinate pairs.

## 3. The remaining multiplicity partitions

### 3.1 One pair type

Both vectors are uniform, and \(\Phi=0\).

### 3.2 Two pair types with multiplicities two and two

Write

\[
p=(1/4+s,1/4+s,1/4-s,1/4-s),
\]

\[
q=(1/4+t,1/4+t,1/4-t,1/4-t).
\]

The parameter \(t\) may have either sign; this includes both relative
orderings of the two types. Direct substitution gives

\[
\boxed{\Phi(p,q)=8(s+t)^2\ge0.}
\tag{14}
\]

This identity holds throughout this family, without stationarity.

### 3.3 Two pair types with multiplicities one and three

Write

\[
p=(a,b,b,b),\qquad q=(c,d,d,d),
\qquad a+3b=c+3d=1,
\]

and set \(r=\sqrt{a/b}\), \(s=\sqrt{c/d}\).
Subtract the stationary equations between the distinguished coordinate
and a repeated coordinate. Since \(P/(ab)=1/r\) and \(Q/(cd)=1/s\),

\[
(a-b)(1+1/r)+2(c-d)=0,
\]

\[
(c-d)(1+1/s)+2(a-b)=0.
\tag{15}
\]

If either difference vanishes, both vanish, giving the uniform point.
Otherwise they have opposite signs. Interchanging \(p,q\) if necessary,
assume \(r>1\), \(s<1\). Multiplying the two equations in (15) after
canceling the nonzero differences gives

\[
(r+1)(s+1)=4rs,\qquad s=\frac{r+1}{3r-1}.
\tag{16}
\]

Normalization gives

\[
a-b=\frac{r^2-1}{r^2+3},\qquad
c-d=\frac{s^2-1}{s^2+3}.
\tag{17}
\]

Substitute (16)--(17) into the first equation of (15), and cancel
\(r-1>0\). The resulting equation is

\[
4r^2(r^2+3)=(r+1)^2(7r^2-4r+1).
\tag{18}
\]

But its right side minus its left side factors as

\[
(r-1)(3r^3+13r^2+r-1)>0\qquad(r>1),
\tag{19}
\]

a contradiction. No nonuniform stationary point of this type exists.

All possible interior stationary points have now been covered. Together
with the boundary argument and compactness, this proves Theorem (1).

Equality is exactly the continuous family, up to simultaneous relabeling,

\[
p=(a,a,b,b),\qquad q=(b,b,a,a),\qquad a,b\ge0,\quad a+b=1/2.
\tag{20}
\]

For completeness, any interior equality point is stationary, so the above
classification puts it in (20). A support-three equality with the other
vector interior is impossible by the same square-root perturbation. If
both products vanish, equality in (2) requires both \(p+q=(1/2,1/2,1/2,1/2)\)
and \(p·q=0\); therefore each vector is uniform on two complementary
coordinates. If one vector has support at most two and the other is
interior, the lower bound \(8u>0\) excludes equality. These are precisely
the endpoints already included in (20).

## 4. Consequence for the hard unitary minor inequality

For \(U\in U(4)\), define

\[
s_1(U)=\sum_i|U_{ii}|^2,\qquad
s_2(U)=\sum_{|I|=2}|\det U[I,I]|^2.
\]

Let \(s_+(U)\) sum the twelve squared minors with one-based row/column
index pairs

\[
(12,13),(12,24),(13,14),(13,23),(14,12),(14,34),
\]

\[
(23,12),(23,34),(24,14),(24,23),(34,13),(34,24).
\tag{21}
\]

The quaternion calculation in root_quaternion_reduction_exact.py proves
for \(O\in SO(4)\) that

\[
2s_1(O)+4s_2(O)+s_+(O)-2
=6\left(\sum_i p_i^2+\sum_i q_i^2+4\sum_i p_iq_i-1
-4\prod_i \xi_i+4\prod_i\eta_i\right),
\tag{22}
\]

where \(\xi,\eta\) are unit quaternions and \(p_i=\xi_i^2\),
\(q_i=\eta_i^2\). The right side is at least \(6\Phi(p,q)\), proving
nonnegativity. Changing the determinant sign of a real orthogonal
matrix by a row sign leaves all squared minors unchanged, so the
inequality also holds for every \(O\in O(4)\).

The previously proved order-four equality of the convex hulls of unitary
and real orthogonal common-minor profiles extends this linear profile
inequality to every \(U\in U(4)\). The explicit proof is in
../moc200/dual_common_facet_sharp_bound.md, Section 7: after making an
anchor row real, the three remaining rows give trace-one real positive
semidefinite effects summing to the identity on its three-dimensional
orthogonal complement. Every extreme such triple is a real orthogonal
frame, so every complex profile is a convex mixture of real profiles.
We therefore obtain

\[
\boxed{2s_1(U)+4s_2(U)+s_+(U)\ge2\qquad(U\in U(4)).}
\tag{23}
\]

The transpose inequality follows by applying (23) to \(U^{\mathsf T}\).

The equal-norm condition in (22) is essential. The superficially stronger
unrestricted homogeneous quartic is false: \(\xi=(2,2,1,2)\),
\(\eta=(0,0,2,0)\) gives value \(-3\) for the version with both product
terms negative. Its squared norms are 13 and 4. A global homogeneous
sum-of-squares proof of that stronger assertion is therefore impossible.

## 5. A complete complex MOC theorem for an explicit finite pair

Let \(\omega=(-1+i\sqrt3)/2\), and take

\[
\boxed{a=(0,1/2,-\omega^2,-\omega),\qquad
b=\left(-1,1,\frac{2\omega-1}{7},\frac{2\omega^2-1}{7}\right).}
\tag{24}
\]

For every pair of normal matrices \(A,B\) having these ordered spectra,

\[
\boxed{\det(A+B)\in
\operatorname{conv}\left\{
\prod_{i=1}^4(a_i+b_{\pi(i)}):\pi\in S_4
\right\}.}
\tag{25}
\]

Here is the reduction to the preceding theorem. After multiplying
permutation products by \(7/9\), their convex hull has vertices

\[
-\frac32,\qquad\frac16,\qquad
\frac{i}{\sqrt{12}},\qquad-\frac{i}{\sqrt{12}}.
\tag{26}
\]

The exact field computation in algebra_a4_fixed_geometry.py verifies all
twenty-four products. Real support directions on this plane are parameterized
by \((x,k)\), with support-edge rays

\[
(-2,3),\quad(-2,-3),\quad(6,1),\quad(6,-1).
\tag{27}
\]

For the first two rays the support deficits are

\[
s_++\frac23s_c,\qquad s_-+\frac23s_c,
\]

where \(s_c\) is the sum of complementary two-minor squares and \(s_-\)
is the transpose of the orbit in (21). These are nonnegative term by term.
The other two deficits are

\[
\frac{-2+2s_1+4s_2+s_+}{3},\qquad
\frac{-2+2s_1+4s_2+s_-}{3},
\]

which are nonnegative by (23) and its transpose. The four edges determine
the entire polygon, so every support direction is proved.

Equivalently, all actual \(A_4\)-symmetric costs in the plane \(y=4x/3\)
satisfy full order-four MOC. This is a complete restricted theorem;
the other nonic branches and general nonsymmetric actual spectra require
additional arguments.


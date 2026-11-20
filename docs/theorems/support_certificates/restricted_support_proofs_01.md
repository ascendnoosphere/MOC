## 1. Principal theorem: the full simplex inequality

For probability vectors \(p,q\in\mathbb R_+^4\), define

\[
\Phi(p,q)=\sum_i p_i^2+\sum_iq_i^2+4\sum_i p_iq_i-1
 -4\sqrt{p_1p_2p_3p_4}-4\sqrt{q_1q_2q_3q_4}.
\]

**Theorem.** \(\Phi(p,q)\ge0\) for every such pair.

The equal-normalization hypotheses \(\sum p_i=\sum q_i=1\) are essential
to this proof. The unequal-norm homogeneous extension proposed earlier is
false and is not used.

### 1.1 Boundary points with a support of size at most two

After permuting coordinates and possibly exchanging the two vectors, write
\(p=(t,1-t,0,0)\), with \(0\le t\le1\). Put
\(u=q_1q_2\), \(v=q_3q_4\). Minimizing the quadratic expression in \(t\)
over all real \(t\), a larger domain than required, gives the exact bound

\[
\Phi(p,q)\ge \frac12+6u-2v-4\sqrt{uv}.
\tag{1}
\]

Indeed the expression before minimization is

\[
2t^2+(-2+4q_1-4q_2)t+4q_2+\sum q_i^2-4\sqrt{uv}.
\]

Now \(q_1+q_2\ge2\sqrt u\), and hence

\[
v\le\frac{(1-q_1-q_2)^2}{4}
\le\frac{(1-2\sqrt u)^2}{4},
\qquad 0\le\sqrt u\le\frac12.
\]

The right side of (1) decreases as \(v\) increases. Substituting this
upper bound yields

\[
\Phi(p,q)\ge8u\ge0.
\tag{2}
\]

This includes support one and all other degeneracies of this boundary
stratum.

### 1.2 A negative minimum must be interior

The product of the two closed simplices is compact and \(\Phi\) is
continuous, so a negative value, if one existed, would give a negative
global minimum. Section 1.1 excludes a support of size at most two in
either vector.

If one vector has exactly one zero entry and its other three entries are
positive, increase the zero entry by \(\epsilon\) and decrease any one
positive entry by \(\epsilon\), leaving the other vector unchanged. All
quadratic terms change by \(O(\epsilon)\). The negative square-root term
changes by

\[
-4C\sqrt\epsilon+O(\epsilon^{3/2}),\qquad C>0.
\]

The total change is strictly negative for sufficiently small positive
\(\epsilon\). Such a point cannot be a global minimum. Thus a negative
global minimum would have all eight coordinates strictly positive.

### 1.3 The stationary equations and a quartic obstruction

At an interior critical point put

\[
P=\sqrt{\prod p_i}>0,\qquad Q=\sqrt{\prod q_i}>0.
\]

The Lagrange equations, after division by two, are

\[
p_i+2q_i-\frac P{p_i}=\alpha,
\qquad
2p_i+q_i-\frac Q{q_i}=\beta.
\tag{3}
\]

The first equation gives

\[
q_i=\frac{\alpha-p_i+P/p_i}{2}.
\tag{4}
\]

As a function of a positive variable \(p_i\), this is strictly decreasing.
Therefore the equality classes of the \(p_i\) and the \(q_i\) coincide,
and the ordering of their distinct values is reversed.

Eliminating \(q_i\), each \(p_i\) is a root of

\[
\begin{aligned}
f(z)={}&-3z^4+2(\alpha+\beta)z^3
 +(\alpha^2-2\alpha\beta+2P-4Q)z^2\\
 &+2P(\alpha-\beta)z+P^2.
\end{aligned}
\tag{5}
\]

For an independent derivation, multiply

\[
(-z^2+\alpha z+P)
(3z^2+(\alpha-2\beta)z+P)-4Qz^2.
\]

The product of all four roots of (5), with multiplicity, is
\(-P^2/3<0\). Consequently the four \(p_i\) cannot all be distinct and
positive. There are at most three distinct coordinate values.

### 1.4 Three distinct values are impossible at a critical point

Suppose there are exactly three. Relabel so that

\[
p=(t,t,a,b),\qquad q=(u,u,c,d),
\]

where \(t,a,b\) are distinct and \(u,c,d\) are distinct. By the product
of the quartic roots, the fourth root of (5) is \(-t/3\): the product of
the three positive roots is \(tab\), while \(P^2=t^2ab\).

Since \(2t+a+b=1\), the sum of the four roots is
\(1-4t/3\). Comparing with the coefficient of \(z^3\) gives

\[
2(\alpha+\beta)=3-4t.
\tag{6}
\]

The same argument for the \(q\)-quartic gives
\(2(\alpha+\beta)=3-4u\), so \(u=t\).

The repeated-coordinate equations in (3) become

\[
\alpha=3t-P/t,\qquad \beta=3t-Q/t.
\tag{7}
\]

Sum the first equation of (3) over all four indices and use
\(a+b=1-2t\), \(ab=P^2/t^2\). Combining the result with (7) gives

\[
2P^2-(12t^2-3t)P-(1-2t)t^3=0.
\tag{8}
\]

Exactly the same quadratic holds for \(Q\). Here \(0<t<1/2\), so its
constant term is strictly negative. It has exactly one positive root.
Therefore \(P=Q\), and then \(\alpha=\beta\).

The remaining pairs \((a,b)\) and \((c,d)\) have equal sums and products.
The decreasing correspondence (4) forces the reverse ordering:
\((c,d)=(b,a)\). Subtracting the two equations (3) now gives

\[
(q_i-p_i)\left(1-\frac P{p_iq_i}\right)=0.
\]

Since \(a\ne b\), this implies \(ab=P\). But \(P=t\sqrt{ab}\), so
\(P=t^2\). From (7), \(\alpha=2t\), while the equation at coordinate
\(a\) gives \(\alpha=a+b=1-2t\). Hence \(t=1/4\).

Finally \(a+b=1/2\) and \(ab=1/16\) force \(a=b=1/4\), contradicting
the assumed three distinct values. This case is impossible.

### 1.5 Two types with multiplicities two and two

Write the vectors as

\[
p=(1/4+s,1/4+s,1/4-s,1/4-s),
\]
\[
q=(1/4+t,1/4+t,1/4-t,1/4-t),
\qquad |s|,|t|\le1/4.
\]

This parametrization retains the common equality classes forced by (4).
Direct substitution, without assuming stationarity, gives

\[
\boxed{\Phi(p,q)=8(s+t)^2\ge0.}
\tag{9}
\]

### 1.6 Two types with multiplicities one and three

Write \(p=(a,b,b,b)\), \(q=(c,d,d,d)\). The one distinct coordinate is
in the same position because of (4). Let

\[
r=\sqrt{a/b},\qquad s=\sqrt{c/d}.
\]

The vectors are nonconstant, so both ratios differ from one. The ordering
reversal permits exchanging \(p,q\) to arrange \(r>1\), \(0<s<1\).
Subtract the repeated-coordinate equation from the exceptional-coordinate
equation in (3). Since \(P/(ab)=1/r\), \(Q/(cd)=1/s\), one obtains

\[
(a-b)(1+1/r)+2(c-d)=0,
\]
\[
2(a-b)+(c-d)(1+1/s)=0.
\tag{10}
\]

The two differences are nonzero, so the determinant of this two-by-two
system vanishes. It follows that

\[
s=\frac{r+1}{3r-1}.
\tag{11}
\]

Normalization gives

\[
a-b=\frac{r^2-1}{r^2+3},\qquad
c-d=\frac{s^2-1}{s^2+3}.
\]

Substitute (11) into the first equation in (10) and cancel the nonzero
factor \(r-1\). The resulting necessary equation is

\[
(r+1)^2(7r^2-4r+1)=4r^2(r^2+3).
\tag{12}
\]

The left side minus the right side is exactly

\[
(r-1)(3r^3+13r^2+r-1)>0\qquad(r>1).
\tag{13}
\]

This contradiction excludes the last nonconstant type of interior critical
point.

### 1.7 Complete the proof

If one vector has only one coordinate value, it is uniform, and (3) makes
the other uniform too; \(\Phi=0\). All other possible interior critical
points have either been excluded or shown nonnegative in (9). A negative
global minimum was forced to be interior, so it cannot exist. This proves
the theorem. The argument includes all boundary and repeated-coordinate
degeneracies.

The equality family
\(p=(a,a,b,b)\), \(q=(b,b,a,a)\), \(a+b=1/2\), shows that the lower
bound zero is sharp. No full equality classification is required above.

## 2. Audit of the global complex-unitary application

The root's `root_quaternion_reduction_exact.py` has been read, including its
normalization conventions. The real orthogonal matrix is written as the
product of left and right quaternion multiplication. On the two unit
spheres its exterior-square action splits into two three-dimensional
rotation blocks \(Q,S\). The Hodge-basis identities give

\[
2s_1+4s_2+s_+-2
=6\left[\sum_iq_i^4+\sum_ir_i^4+4\sum_iq_i^2r_i^2-1
            -4\prod_iq_i+4\prod_ir_i\right].
\tag{14}
\]

The last bracket is at least \(\Phi(q_0^2,\ldots,q_3^2;
r_0^2,\ldots,r_3^2)\), since each signed product is bounded below by
minus its absolute value. The simplex theorem therefore proves
\(2s_1+4s_2+s_+\ge2\) for every real orthogonal matrix of order four.
The transposed inequality follows as well. It is not necessary to assume
that the two signed quaternion products have a common sign.

The previously established passage from real orthogonal to complex unitary
profiles is valid. For completeness, make one row of a complex unitary real
by column phases, calling it \(v\). On the real three-dimensional space
\(v^\perp\), the other rows give real symmetric PSD effects of trace one
whose sum is the identity. If all three effects at an extreme point have
rank at least two, their supported symmetric perturbation spaces have total
dimension at least nine. The zero-sum and individual trace constraints have
at most eight independent equations. A nonzero two-sided feasible
perturbation contradicts extremality.

Thus one extreme effect has rank one and is a projection. The remaining
two effects live on its orthogonal two-dimensional complement and sum to
the identity. They commute, and their trace-one condition expresses them
as a mixture of the two ordered orthogonal frames. Extremality forces an
actual frame. Every triple is consequently a convex combination of frames.

Each singleton squared entry and each two-minor containing the anchor row
is linear in the appropriate effect. Complementary-minor identities cover
the remaining two-minors. Hence every full complex-unitary squared-minor
profile is a convex combination of real orthogonal profiles. The hard gap
is linear in that profile, so (14) proves its nonnegativity for every
complex unitary of order four.

The soft-ray gaps in the algebra note are explicitly nonnegative sums of
squared minors. The two hard gaps have now been proved nonnegative. Those
four rays are the four edges of the permutation-product hull of the stated
finite spectral pair

\[
a=(0,1/2,-\omega^2,-\omega),\qquad
b=(-1,1,(2\omega-1)/7,(2\omega^2-1)/7),\qquad
\omega^2+\omega+1=0,\ \Im\omega>0.
\]

Thus the entire complex MOC assertion for this fixed spectral pair is
proved, for every \(U\in U(4)\) and every complex support direction. This
is a restricted-family theorem, and supplies no reduction of unrestricted
MOC to this particular pair.

## 3. Audit of the all-reflection zero-gap theorem

The new theorem in `direct_zero_gap_reflections.md` is accepted, conditional
only on the previously established complete 82-facet catalog and the
audited degree-nine derangement-face classification. No new gap was found.

### 3.1 Facet and affine-space reduction

The signed determinant weights express every unitary squared-minor profile
in the affine span of permutation profiles. Consequently exact linear
identities on the 24 vertices extend to all unitary profiles. By the
complete facet description and duality of the tangent cone at identity,
every nonnegative common-minor gap vanishing at identity is a nonnegative
combination of identity-active facet functions.

The independent checker regenerates all 48 mixed facets, selects the 26
identity-active facets, and verifies all their nonnegative transpose
symmetrizations. Thus every summand is nonnegative at a Hermitian
reflection. If their sum vanishes, every positively weighted summand
vanishes there.

A basic squared minor vanishing at the reflection has zero first
differential, because it is the squared modulus of a function vanishing
there. The endpoint derivative of a full two-plane Cayley orbit is an
invertible reparametrization of the cubic covector. It therefore vanishes
for these basic summands.

### 3.2 Orbit A, including the zero diagonal

The six vanishing two-minors give
\(rH-vv^*\) diagonal for the decomposition
\(R=\left(\begin{smallmatrix}r&v^*\\v&H\end{smallmatrix}\right)\).
At \(r=0\), \(vv^*\) diagonal implies at most one nonzero coordinate
of \(v\). At \(r\ne0\), the diagonal correction in
\(H=D+vv^*/r\) equals \(-1/r\) on the support of \(v\).
Two supported coordinates would produce an eigenvector with eigenvalue
\(-1/r\), contradicting \(R^2=I\) and \(\|v\|^2=1-r^2>0\).

If \(v=0\), then \(r=\pm1\) and \(H\) is diagonal. If exactly one
coordinate is nonzero, the off-diagonal equations in \(R^2=I\) decouple
that two-coordinate block from the other two coordinates. This covers all
degenerate cases and proves the coordinate-block conclusion.

### 3.3 Orbit B, including rank-one cross coupling

The cross block \(X\) has determinant zero. If it is nonzero, write
\(X=suv^*\) with \(s>0\). The equations for a traceless Hermitian
involution give the displayed two rank-one perturbations of scalar
matrices in the author's equation (7), including \(s=1\), \(a=0\).
The remaining two zero minors are exactly proportional to
\(\overline{u_1}v_2\) and \(\overline{u_2}v_1\). Unit normalization
forces both vectors to be matching coordinate vectors. The cross coupling
therefore joins only two coordinate positions. The case \(X=0\) already
has the desired coordinate blocks.

For such blocks, an adapted basis of the negative eigenspace makes all row
effects multiples of the two coordinate projections. The formula for every
triple cubic covector is then zero. This argument covers a block with two
negative eigenvalues as well as two separate one-dimensional negative
directions.

### 3.4 Orbit C and the complex phase issue

The zero conditions are the two opposite entry zeros \(R_{12}=R_{34}=0\).
If any entry of the remaining two-by-two cross block vanishes, its row and
column orthogonality equations reduce its support to a partial matching,
giving coordinate blocks. If all four cross entries are nonzero, the
diagonal entries on each side coincide with opposite signs, and the cross
block is a scalar multiple of a two-by-two unitary.

Independent row and column phases make any such two-by-two unitary real
orthogonal. They are available as diagonal conjugation of \(R\), which
preserves the spectral support because both spectral matrices are diagonal.
Signs then give the real family

\[
R(a,b,c)=\begin{pmatrix}
a&0&b&c\\0&a&-c&b\\b&-c&-a&0\\c&b&0&-a
\end{pmatrix},\qquad a^2+b^2+c^2=1.
\]

There is no omitted genuinely complex two-by-two phase invariant.

### 3.5 Nonbalanced and balanced contacts

The independent exact checker recomputes the entire continuous family.
For \(abc\ne0\), only mixed facets 4 and 17 vanish. Every other slack
has a nonzero polynomial with nonnegative coefficients in
\(a^2,b^2,c^2\). Exactly four active basic entry functions vanish, and
their common zero vertices together with those two mixed facets are exactly
the nine derangements relative to \((12)(34)\).

The spectral face theorem thus forces the full gap to be a sum of at most
two nonnegative assignment entry squares. Their first derivatives vanish
at the reflection, proving the required zero cubic covector.

For \(a=0\), \(bc\ne0\), all other mixed slacks remain positive: each
has a positive monomial independent of \(a\). Additional basic zero
minors still have zero differential. The Pluecker coordinates in the note
satisfy both the Pluecker relation and the normalization on
\(a^2+b^2+c^2=1\), and recover \((I-R)/2\). Substitution gives the two
remaining cubic covectors exactly as \(2abc\,y\) and \(-2abc\,y\).
They vanish in this balanced case.

All cases therefore give \(\ell=0\). At a maximizing identity base, the
exact Cayley numerator becomes \(4\mathcal A(T)\ge0\) when the
reflection gap is zero. The theorem follows on the chart and by continuity
on all of the two-plane unitary orbit.

This proves the zero-gap compatibility, not the positive-gap inequality
\(g(R)\ge\ell^T\mathcal A^+\ell/4\). No quantitative rate follows
solely from vanishing at every contact.

## 4. Audit of the A4 nonic, budget, and real form

The checker independently rebuilds the restricted cubic from the audited
14-coordinate M8 cubic and the four class-value parameters. It reconstructs
the Hessian in the recorded rational bases, verifies every cross-block zero,
and obtains the congruence determinant \(-1/144\). The two nonfixed
blocks have determinants

\[
S^2/36,\qquad -R^3/256.
\]

The fixed block and constant-height elimination give

\[
P_9\big|_{A_4\text{-fixed}}
=\pm x(3y-4x)^2(4k^2+xy-x^2)^3/32.
\]

Continuation through \(Q=0\) is legitimate because the identities are
polynomial identities and \(Q\) is not identically zero on this subspace.
This neither assumes finite spectral realizability nor makes group averaging
preserve the nonlinear variety.

The branch proof of \(K^2\le(32/9)TD\) is correct. In particular, on
\(x<0\) in the quadratic branch, the two margins are respectively
\(4u^2-9s^2\) for \(s\le u/2\), and
\(16s^4/u^2+3s^2\) for \(s\ge u/2\). Both signs are as claimed.
The sharp equality in the larger closure need not be a finite spectral
point; the companion note correctly separates that issue.

The explicit \(\mathbb Q(\omega)\) spectral pair does realize the entire
real plane \(y=4x/3\) as its support directions. The cubic gradient
identities and Hessian-kernel equations have the right signs for a real part
of one complex cone point. The generic \(x=0\), \(yk\ne0\) component's
two-dimensional Hessian kernel cannot supply the required gradient, so its
border-only conclusion is correct.

One harmless wording qualification is needed: the unique cubic lift on
\(y=4x/3\) is unique for \((x,k)\ne(0,0)\). At the zero centered cost,
the constant line is not fixed by that elimination. None of the support or
realization arguments relies on uniqueness at zero.

The earlier note's statement that the hard full-unitary ray remained open is
now superseded by Sections 1–2 of this review and the author's new complete
simplex note. The unrestricted problem remains open in this work.

## 5. Complete support theorem for actual A4-invariant costs

The algebra specialist subsequently supplied elementary certificates for the
quadratic nonic branch. They have been independently checked, including
every endpoint, and are included in the exact review script.

Use the nonnegative minor sums defined above and put

\[
X=(s_++s_-)/4,\qquad Y=s_c/4,\qquad Z=(s_--s_+)/6.
\]

Every symmetry-fixed cost has the full-unitary expression

\[
c(U)=h_0+xX(U)+yY(U)+kZ(U).
\tag{15}
\]

The exact profile identities are

\[
X+2Y=2-s_1/2,\qquad s_2+s_c+s_++s_-=6.
\tag{16}
\]

On the quadratic branch \(4k^2=x(x-y)\), transpose permits assuming
\(k\ge0\). If \(x\ne0\), write \(r=2k/|x|\ge0\).

For \(x>0\), one has \(y=x(1-r^2)\), with relative support height
\(h=x(3+r)/2\). The exact gap is

\[
\frac{h-(c(U)-h_0)}{x}
=\frac{3+r}{12}s_2+\frac r6s_+
  +\frac{r(3r+1)}{12}s_c\ge0.
\tag{17}
\]

For \(x=-u<0\), \(y=u(r^2-1)\). If \(0\le r\le1\), the relative
height is zero and

\[
\frac{h-(c(U)-h_0)}u
=\frac{3+r}{12}s_++\frac{3-r}{12}s_-
  +\frac{1-r^2}{4}s_c\ge0.
\tag{18}
\]

If \(r\ge1\), the relative height is \(u(r^2-1)\), and

\[
\frac{h-(c(U)-h_0)}u
=\frac{3r^2+2r+3}{24}s_+
 +\frac{3r^2-2r+3}{24}s_-
 +\frac{r^2-1}{4}s_1\ge0.
\tag{19}
\]

All coefficients have the stated nonnegative signs. The formulas agree at
\(r=1\), and include \(r=0\). For \(k<0\), exchange \(s_+\) and
\(s_-\). If \(x=0\) on this branch, then \(k=0\), covered next.

On the remaining nonic branch \(x=0\), an actual finite spectral cost
cannot have \(yk\ne0\), by the reviewed Hessian-kernel obstruction.
For \(k=0\), inequalities (16) and nonnegativity imply \(0\le Y\le1\),
so \(yY\le\max(0,y)\). For \(y=0\), the second identity in (16)
gives \(|Z|\le(s_++s_-)/6\le1\), so \(kZ\le|k|\).

The three branches of the nonic are therefore all covered for actual
spectral costs: the plane \(y=4x/3\) by the simplex theorem, the quadratic
branch by (17)–(19), and the actual portions of \(x=0\) by these axis
bounds. Thus:

**Full support theorem.** If the real permutation support costs of an
actual order-four complex MOC instance are invariant under simultaneous
conjugation by \(A_4\), their support maximum bounds the determinant for
every \(U\in U(4)\).

This statement concerns a fixed real support direction satisfying the
symmetry condition. It yields full complex MOC for any pair whose support
costs have the symmetry in every direction, including the explicit
tetrahedral pair. It does not imply the symmetry for general spectra.
It also does not use the unproved candidate inequality
\(Y+|Z|\le1\) on the generic border-only part of \(x=0\).


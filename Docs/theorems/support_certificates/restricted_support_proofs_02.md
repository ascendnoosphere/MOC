## 1. Quantitative contact theorem: algebraic multiplicities

The claims in `direct_quantitative_contact_rigidity.md` have been checked
as mathematical implications, including the degeneracies; the finite
certificate alone is not treated as a proof of the asymptotic estimates.

Let \(p_i(\pi)=1_{\{\pi(i)=i\}}\), let \(H_i=H(p_i)\), and let
\(H_e=H(\mathbf1)\). The independently reconstructed finite facts are

\[
B(p_i)=0,\quad \nabla F_3(p_i)=0,\quad
\operatorname{rank}H_i=\operatorname{rank}H_e=4,
\]

and, for every distinct pair,

\[
\dim(\operatorname{im}H_i+\operatorname{im}H_j)=7,
\qquad H_ip_j=H_jp_i\ne0.
\tag{1}
\]

For \(s=up_i+vp_j\), polarization gives \(F_3(s)=0\) and
\(H(s)(up_i-vp_j)=0\). Put
\(V=\operatorname{im}H_i+\operatorname{im}H_j\). By symmetry,
\(V^\perp\) is a common kernel of both matrices. When \(uv\ne0\),
the displayed kernel vector has a nonzero projection to \(V\), because
\(H_i(up_i-vp_j)=-vH_ip_j\ne0\). Its projection is still in
\(\ker H(s)\). Thus \(H(s)|_V\) has a kernel and

\[
\operatorname{rank}H(s)\le6.
\tag{2}
\]

This is a uniform two-parameter argument, including coefficients of either
sign. At an axis the rank is at most four. No inference from the sample
ranks in the author's certificate is needed.

In the degree-eighteen identity

\[
N=Q^2h_0-F_3Qh_1+F_3^2h_2+2F_3^3\det K=-4P_9^2,
\tag{3}
\]

the perturbation orders at a two-assignment point are

| Factor | Order at least |
|---|---:|
| \(Q\) | 2 |
| \(F_3\) | 1 |
| Each \(h_j\) | 4 |
| \(\det K\) | 3 |

Here \(B(s)=0\) gives the order of \(Q=\det B\). Also
\(\operatorname{rank}H(s+t\mathbf1)\le10\) for each fixed \(t\).
Four fixed values of \(t\) recover the four coefficients of its
degree-three height polynomial by a fixed invertible interpolation matrix;
therefore each \(h_j\) has order at least four. The principal split
submatrix \(K\) has size nine and rank at most six.

The four summands of (3) have respective orders at least \(8,7,6,6\),
so \(\operatorname{ord}_sP_9\ge3\). At an axis the stronger gradient
and rank facts give orders \(10,10,10,11\), so
\(\operatorname{ord}_{up_i}P_9\ge5\). At the origin the actual order
is nine by homogeneity; the stated lower bounds still hold. An overall
nonzero normalization factor in (3) has no effect on these conclusions.

## 2. The face cubic and its scale estimates

The two nonnegative parametrizations of the derangement face both give

\[
F_3=e_3(w)+ke_2(w)+k^2e_1(w)+k^3,\qquad w_i,k\ge0.
\tag{4}
\]

I checked the full expansions independently. Deleting \(k\) changes the
cost by at most \(2k\), leaving an assignment cost. The identity
permutation has its largest value, so
\(M_1=\sum_iw_i+2k\). With ordered weights
\(u\ge v\ge w\ge z\ge0\) and \(r=k+w+z\), the retained two-weight
point \(s\) satisfies

\[
\|g_1-s\|_\infty\le2r,\quad
u+v+r\le M_1\le2(u+v+r),\quad M_1\le2(u+r).
\tag{5}
\]

The comparison constants in the direct note are valid:

\[
\frac1{18}r(u+r)(v+r)\le F_3(g_1)
\le3r(u+r)(v+r).
\tag{6}
\]

For the lower bound, average the two subexpressions
\((u+k)(v+k)(w+k)\) and \((u+k)(v+k)(z+k)\), each contained
coefficientwise in (4). The average is at least
\(r(u+k)(v+k)/2\). Since \(w,z\le v\le u\), each of the factors
\(u+r,v+r\) is at most three times its version with \(k\).
This gives \(1/18\). The upper bound follows by grouping the cubic
terms according to their powers of \(r\).

The consequences

\[
F_3(g_1)\ge M_1r^2/36,
\qquad F_3(g_1)\ge uvr
\tag{7}
\]

are correct, including when a retained weight vanishes. The second estimate
then becomes vacuous, as it should at a one-weight corner.

The chamber coordinates can be chosen as continuous piecewise-linear
functions. In the original five coordinates \((a,b,c,d,e)\), for
example,

\[
k=|d-e|,\quad E=\min(d,e),\quad C=c-\max(d,e),
\]
\[
A=a-b-\max(e-d,0),\qquad B=b-\max(d-e,0).
\]

Thus the local continuity assertion used to retain the same two-weight
cone is valid even where the two chambers meet or the two positive weights
are equal.

## 3. Tensor divisibility and the distance estimates

The multiplicities in Section 1 imply that \(DP_9\) and \(D^2P_9\)
vanish on every two-assignment plane. Each component of
\(D^3P_9(up_i+vp_j)\) is a homogeneous polynomial of degree six in
\(u,v\). At either axis both its value and its first transverse
derivative vanish, because they are values of \(D^3P_9\) and
\(D^4P_9\) at a point of multiplicity at least five. Hence it is
divisible by \(u^2v^2\). Similarly \(D^4P_9\) is divisible by \(uv\).
These are divisibility statements for every tensor component, rather than
only directional evaluations within the plane.

Homogeneity and the finite set of six assignment pairs therefore yield

\[
\|D^3P_9(s)\|\le C u^2v^2(u+v)^2,
\quad
\|D^4P_9(s)\|\le Cuv(u+v)^3,
\]
\[
\|D^jP_9(s)\|\le C(u+v)^{9-j},\qquad5\le j\le9.
\tag{8}
\]

Expanding the gradient in a finite Taylor series gives the homogeneous
bound

\[
\|DP_9(s+e)\|
\le C R^2(u+R)^2(v+R)^2(u+v+R)^2,
\qquad\|e\|\le R.
\tag{9}
\]

Its total degree is eight, as required. The fourth-derivative contribution
is absorbed by
\([(u+R)(v+R)]^2\ge2uvR(u+v)\). For all higher derivatives use
\((u+R)(v+R)\ge R(u+v+R)\) and
\(R^{j-1}(u+v)^{9-j}\le R^4(u+v+R)^4\). At \(u=v=0\), the same
bound reduces to the correct eighth-order bound. Thus no bounded-region
constant has been silently substituted for a homogeneous one.

Let \(D\) restrict a cost to the nine derangements, and let \(L\) be a
fixed linear right inverse with norm at most \(\beta\ge1\). Put
\(\delta=\max_{\mathrm{der}}g_\pi\), \(M=\|g\|_\infty\), and

\[
g_1=g-LDg+\beta\delta\sum_i p_i.
\tag{10}
\]

It is a nonnegative cost on the derangement-zero face: at a nonderangement
the fixed-point count is at least one and compensates the possible
\(-\beta\delta\) correction. At each derangement all terms vanish.
Furthermore,

\[
\|g_1-g\|_\infty\le5\beta\delta,
\qquad M_1\le(1+5\beta)M.
\tag{11}
\]

If \(r\le\delta\), the required distance estimate follows immediately
from (5), (11), and \(\delta\le M\). Otherwise the segment joining
\(g\) and \(g_1\) is within distance \((2+5\beta)r\) of the
retained two-weight point. Since \(P_9(g)=0\) and
\(P_9(g_1)=\pm F_3(g_1)^3\), integration of (9) gives

\[
F_3(g_1)^3
\le C\delta r^2(u+r)^2(v+r)^2(u+v+r)^2
\le C'\delta F_3(g_1)^2M_1^2.
\tag{12}
\]

If the cubic is zero, (6) already gives \(r=0\). Otherwise cancellation
is legitimate and yields \(F_3(g_1)\le C\delta M_1^2\). The same
bound holds in the earlier \(r\le\delta\) case by the upper bound
in (6). Combining with (7) proves

\[
\boxed{\operatorname{dist}_\infty(g,\mathcal S)
\le C\sqrt{M\delta}.}
\tag{13}
\]

All zero cases are covered: if \(M=0\), the cost is zero; if
\(\delta=0\), the exact face classification gives membership in
\(\mathcal S\). The fixed finite normalization supplies an absolute
constant for this order-four problem, not a dimension-independent claim.

Near a fixed point with two positive specified assignment weights,
\(uv\) stays bounded below and \(M_1\) stays bounded above. The second
bound in (7) gives \(r\le C\delta\), proving the local linear
distance estimate on the same particular two-weight cone. The factor
\(1/(uv)\) explains why this argument does not extend with a uniform
linear constant to a one-weight corner.

## 4. From distance to fixed-plane positive-gap control

For the fixed nonbalanced reflection

\[
R=\begin{pmatrix}
a&0&b&c\\0&a&-c&b\\b&-c&-a&0\\c&b&0&-a
\end{pmatrix},\quad a^2+b^2+c^2=1,\quad abc\ne0,
\]

the signed determinant weights are nonnegative and are supported on
exactly the nine derangements relative to \(\pi_0=(12)(34)\). They
are \(a^4\); two copies each of \(a^2b^2\), \(a^2c^2\), and
\(b^2c^2\); and \(b^4,c^4\). Their sum is one. The independent
checker reconstructs all twenty-four signed products, including the
fifteen zeros.

Consequently, for every nonnegative common-minor cost,

\[
\delta_{\pi_0}\le g(R)/q_{\min},\qquad q_{\min}>0.
\tag{14}
\]

Let the negative-eigenspace frame be real. For
\(T=\left(\begin{smallmatrix}s&x+iy\\x-iy&t\end{smallmatrix}\right)\),
every compressed entry has a real part depending only on \((s,t,x)\)
and imaginary part \(yp_{ij}\). The nonnegative quadratic form therefore
splits exactly into a real block and the single \(y\) direction. The
cubic covector vanishes on all real-symmetric \(T\), so it is confined
to that same one-dimensional direction.

At an assignment contact on the zero positions of \(R\),
\(\ell=0\). Its quadratic coefficient is

\[
A_{yy}=(w_1+w_2)(1-a)^2/4+(w_3+w_4)(1+a)^2/4>0.
\tag{15}
\]

The strict positivity holds for any nonzero nonnegative contact weight
because \(|a|<1\). Near a fixed two-positive-weight contact the local
linear distance estimate and (14) give
\(|\ell_y|\le Cg(R)\), while \(A_{yy}\) remains bounded below.
The pseudoinverse energy is exactly

\[
E(g)=\frac{\ell_y^2}{4A_{yy}}\le Cg(R)^2.
\tag{16}
\]

There is no hidden contribution from small eigenvalues of the real block:
the blocks decouple for every perturbed cost, and the covector has zero
component in the entire real block. This is the essential reason the
distance theorem suffices here.

By shrinking the cost neighborhood, \(Cg(R)<1\) for positive gaps, and
the exact Cayley criterion proves the support bound on the complete complex
\(U(2)\) orbit of this fixed plane. The zero-gap case is already covered
by the reflection-contact theorem.

**Limits.** The constant depends on the fixed reflection and contact. It
can deteriorate when \(abc\to0\), when an active contact weight tends to
zero, or when the positive scalar coefficient in (15) tends to zero. The
argument provides no uniform moving-plane theorem. At a one-weight corner
the square-root distance estimate yields only \(E\le Cg(R)\); it does
not prove the required coefficient one. These limitations are stated
correctly in the direct note.

## 5. Equality in the first simplex theorem

The added equality classification is accepted. Since the first simplex
inequality has been proved nonnegative, an interior equality point is an
interior global minimum and is stationary. The established multiplicity
classification therefore forces

\[
p=(a,a,b,b),\quad q=(b,b,a,a),\quad a+b=1/2.
\]

If both products vanish, equality in
\(\Phi=\|p+q\|^2+2p\cdot q-1\ge0\) requires both
\(p+q=(1/2,1/2,1/2,1/2)\) and \(p\cdot q=0\). These are precisely
the two complementary uniform two-point supports. A support-three vector
paired with an interior vector cannot give equality by the square-root
perturbation, and a support-at-most-two vector paired with an interior
vector has the strictly positive lower bound \(8u\). This exhausts the
boundary. The complete equality set is therefore the displayed family up
to simultaneous relabeling, including its endpoints.

## 6. Independent audit of the second simplex theorem

The new theorem is

\[
\boxed{W(p,q):=\tfrac12\|p-q\|^2+8(P+Q)\le1,}
\qquad P=\sqrt{\prod p_i},\ Q=\sqrt{\prod q_i}.
\tag{17}
\]

Its boundary argument is exact. If \(P=0\),

\[
\sum_i p_iW(e_i,q)-W(p,q)=\tfrac12(1-\|p\|^2)\ge0.
\]

For \(p=e_1\), \(q=(t,a,b,c)\), the proposed identity is

\[
1-W(e_1,q)=t^2+
\sum_{\mathrm{cyc}(a,b,c)}
\left[2(\sqrt{ta}-\tfrac23\sqrt{bc})^2+\tfrac19bc\right].
\tag{18}
\]

Each cyclic cross term contributes \(-8\sqrt{tabc}/3\), and the
remaining coefficients give exactly
\(t^2+2t(a+b+c)+ab+ac+bc\). Thus the SOS is correct. The convex
reduction is strict unless \(p\) is a vertex; then the SOS vanishes
only when \(q\) is a different vertex. These are all boundary equalities.

At an interior stationary point, write \(A=4P\), \(B=4Q\). The
equations are

\[
p_i-q_i+A/p_i=\alpha,\qquad q_i-p_i+B/q_i=\beta.
\]

Their sum yields \(\gamma=\alpha+\beta=2W>0\) and the rational,
strictly decreasing correspondence

\[
q_i=\frac{Bp_i}{\gamma p_i-A}.
\tag{19}
\]

The denominator is positive because \(q_i>0\). Eliminating \(q_i\)
gives the cubic

\[
\gamma z^3-(\gamma\alpha+A+B)z^2
+A(\gamma+\alpha)z-A^2=0.
\tag{20}
\]

This has at most three positive coordinate types, with the same equality
classes in both vectors. The remaining classification has been checked
independently:

| Multiplicity | Necessary conclusion |
|---|---|
| (2+1+1) | Cubic root products give (gamma=16t=16u). Normalization and the repeated-coordinate equations give (t=u=1/10), hence (W=4/5). |
| (2+2) | (W=1-4(s+t)^2-2(s-t)^2le1). |
| (1+3) | With (r=sqrt{a/b}), (s=sqrt{c/d}), stationary differences give (r+s=4). The decreasing correspondence permits (3<r<4), (0<s<1). Put (v=rsin(0,3)); then (1-W=(3-v)(11-v)/(v^2-6v+57)>0). |
| (4) | Both vectors are uniform and (W=1). |

The three-type critical points need not be excluded: they do exist, and
their value is strictly below the bound. This is handled correctly in the
author's argument. Compactness now proves (17). Its complete equality set
is the uniform pair together with the ordered pairs of distinct vertices.

## 7. Consequence for the entire symmetric nonic zero set

The quaternion formulas have the correct factors:

\[
X=2-\|p\|^2-\|q\|^2,\quad
Y=\tfrac12\|p-q\|^2,\quad
Z=8(\prod\xi_i-\prod\eta_i),
\]

where \(p_i=\xi_i^2\), \(q_i=\eta_i^2\). Therefore the second
simplex theorem gives \(Y+|Z|\le1\) on real orthogonal profiles.
Apply the previously proved complex-to-real convexification separately to
the two linear inequalities \(Y+Z\le1\) and \(Y-Z\le1\). They
then hold on all complex unitary profiles.

On the previously border-only nonic component \(x=0\), the relative
permutation maximum is \(h=\max(0,y,|k|)\). Since \(Y\ge0\),

\[
yY+kZ\le h(Y+|Z|)\le h.
\tag{21}
\]

Together with the two already proved branches, this establishes the full
support theorem for **every real A4-symmetric common-minor cost satisfying
the projected nonic equation**. No finite-realization hypothesis is now
required on this symmetric set. This strengthens the previous review's
actual-cost theorem, but it still does not put a general cost's group
average on the nonic.


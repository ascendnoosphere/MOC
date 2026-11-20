# Two-reflection stopping laws and exact projector-phase obstructions

31 October 2026. Unrestricted MOC remains unproved. The all-input
one-step rounding rule using a single projector phase is false in dimension
four, even when every projector rank and every continuous parameter are
allowed. An exact positive stopping law on the same input uses three products
of two noncommuting rank-one reflections. This suggests allowing a general
unitary with rank at most two away from the identity.

The new family has a complete all-dimensional parameterization. A second
exact result characterizes an entire two-phase torus at a stationary point
by one \(3\times3\) PSD matrix. Neither result establishes the remaining
global rounding inequality.

Code and exact artifacts:

- [circle certificate](../../code/research/moc_unrestricted_martingale_circle_certificate.py)
  and [saved certificate](../../build/moc_unrestricted_20261031/martingale/full_phase_n4_union_circle_certificate.json);
- [positive two-reflection law](../../code/research/moc_unrestricted_martingale_two_reflection.py)
  and [saved law](../../build/moc_unrestricted_20261031/martingale/two_reflection_union_repair.json);
- [two-phase torus verifier](../../code/research/moc_unrestricted_martingale_two_phase.py)
  and [three exact instances](../../build/moc_unrestricted_20261031/martingale/two_phase_torus_exact.json).

## 1. General rank-two unitary reducers

Let \(u=U[:,j]\), \(e=e_i\), \(\rho=e^*u\), and assume \(|\rho|<1\).
Choose \(|\lambda|=1\), and set

\[
x=u-\lambda e,\quad P_x=xx^*/\|x\|^2,\qquad
\xi=-\frac{1-\lambda\bar\rho}{1-\bar\lambda\rho},\quad
H_0=I+(\xi-1)P_x.
\]

Then \(H_0u=\lambda e\). Every unitary \(W\) satisfying

\[
Wu=\lambda e,\qquad \operatorname{rank}(W-I)\le2
\]

has the form

\[
W=[I+(\zeta-1)vv^*]H_0,\qquad
|\zeta|=1,\quad \|v\|=1,\quad v\perp e.
\tag{1}
\]

The identity phase includes the rank-one case.

For the converse, put \(S=\operatorname{ran}(W-I)\). This reducing subspace
contains \(u-\lambda e\), so it also supports \(H_0-I\). The unitary
\(R=WH_0^*\) fixes \(e\) and is supported on \(S\). Moreover \(P_Se\ne0\):
the projections of \(u\) and \(\lambda e\) outside \(S\) agree, so their
projections onto \(S\) have equal norm; \(P_Se=0\) would force \(u=\lambda e\).
Thus \(R|_S\) fixes a nonzero vector in a space of dimension at most two.
It differs from the identity on at most one orthogonal direction. This
proves (1), including \(v\perp e\).

The older rank-two projector-phase family is the restriction

\[
v\perp\operatorname{span}(e,u),\qquad \zeta=\xi.
\tag{2}
\]

Both restrictions matter. In (1), the second phase acts on the entire
residual coordinate space and need not commute with \(H_0\).

For arbitrary complex spectra, every endpoint of (1) has a reducing coordinate:

\[
D(W)=(a_i+b_j)
 \det(D_{a_{\widehat i}}+V D_{b_{\widehat j}}V^*),
\tag{3}
\]

with a genuine residual unitary \(V\). At fixed \(i,j,\lambda,v\), the
support as a function of \(\zeta=e^{it}\) is exactly

\[
c+\alpha\cos t+\beta\sin t.
\]

Its maximum is \(c+\sqrt{\alpha^2+\beta^2}\). This follows from the rank-one
phase degree bound and requires no inverse or nonsingularity hypothesis.
Thus the larger family still eliminates its second phase analytically.

A sufficient all-\(n\) stopping statement, for \(n\ge4\), is

\[
d_U(a,b)\in\operatorname{conv}\{D(W):W\text{ as in (1)}\}.
\tag{4}
\]

A planar convex combination can be reduced to at most three points by
eliminating affine dependencies. Under (4), choose at most three reducing
children, recurse to dimension three, then use a positive Birkhoff law for
the residual singleton matrix. The tower property gives the original
complex determinant as the first moment of the terminal assignment product.
The depth is bounded by \(n-3\), so no limiting or integrability argument is
needed. This law permits all branch choices to depend jointly on the
sources and imposes no Born marginal.

Statement (4) remains unproved. The exact law in Section 3 is a client of
this mechanism at one hostile input, rather than an existence proof for
all inputs.

## 2. An exact n=4 obstruction to every single-projector reducer

Put \(U=(I+X)(I-X)^{-1}\), where

\[
X=\frac1{50}
\begin{pmatrix}
0&1&-10&-34\\
-1&0&-10&25\\
10&10&0&16\\
34&-25&-16&0
\end{pmatrix}.
\]

This is rational orthogonal. Define

\[
t=(136-18i,-52-102i,29-3i,-113+122i)/50,
\]

\[
v=(70-136i,-71+7i,-25+8i,26+120i)/50,
\quad \varepsilon=10^{-6},
\]

\[
a_i=1/t_i,\qquad b_j=\varepsilon v_j,\qquad
\eta=\prod_i t_i.
\tag{5}
\]

For every single projector phase \(W=I+(\zeta-1)P\) that reduces any
coordinate/eigenvector pair, and for every projector rank,

\[
\Re\{\eta d_U(a,b)\}
-\Re\{\eta d_{WU}(a,b)\}
\ \ge\
\frac{10742906174255466604451039}
     {1953125000000000000000000000000000}
\ >5\cdot10^{-9}.
\tag{6}
\]

This is a strict failure of the stronger all-input rounding rule. It does
not refute a rounding statement restricted to actual support maxima.

The proof first certifies a singleton-cost separation. Set
\(H_{ij}=\Re(t_i v_j)\) and \(F_H(U)=\sum H_{ij}|U_{ij}|^2\). The exact
certificate establishes

\[
F_H(U)-F_H(WU)\ge 1/100
\tag{7}
\]

for the full rank-two projector-phase family. Every such reducer has
projector (P_x+Q): its action on (u) forces (u-lambda e) into the
range, and the remaining range direction is orthogonal to both (u) and
(e). Thus the complementary (Q) parameter below omits no reducer.

Here is how the verifier covers its continuous parameters. For each
\((i,j)\), take a rational, possibly nonorthogonal basis \(R\) of
\(\operatorname{span}(e_i,u_j)^\perp\). Put

\[
Y(s)=\tfrac12(s_0I+s_1\sigma_1+s_2\sigma_2+s_3\sigma_3),\quad
S(s)=RY(s)R^*,\quad g(s)=\operatorname{tr}S(s).
\]

On the real light cone \(s_0^2=s_1^2+s_2^2+s_3^2\), \(s_0>0\), every
complementary rank-one projector is \(Q=S(s)/g(s)\).
Let \(|\lambda|=1\), \(\rho=U_{ij}\), and write the single-phase reducer as
\(I+(\xi-1)(P_x+Q)\). After clearing \((\lambda-\rho)g(s)\), its matrix is
linear in \(s\) and quadratic in \(\lambda\). The numerator coefficients are

\[
N_0=g(ue^*-\rho I)+\rho S,\quad
N_1=g(I-uu^*-ee^*)-2S,\quad
N_2=geu^*+\bar\rho S.
\tag{8}
\]

Consequently the desired upper-bound deficit is a real quadratic
\(s^TP(\phi)s\), \(\lambda=e^{i\phi}\), whose matrix has Fourier degree two.
The saved certificate gives rational scalar extensions

\[
P(\phi_k)+\mu_k\operatorname{diag}(1,-1,-1,-1)
 \succeq \delta_k I,\qquad \delta_k>0
\]

at rational points of the unit circle. Exact rational LDL checks verify
every matrix. Between adjacent points, interpolate \(\mu\) linearly in
\(\phi\). The Fourier coefficients give an explicit bound \(M\) on the
second derivative in operator norm. An interval of angular length \(L\)
is covered whenever \(ML^2/8\le\min(\delta_k,\delta_{k+1})\).
The term involving \(\mu\) vanishes on the light cone, proving the desired
inequality throughout that interval.

The rational chart
\(\lambda=\pm(1-t^2+2it)/(1+t^2)\), \(-1\le t\le1\), covers the full circle.
The certificate has 1,478 rational endpoint matrices and 1,446 covering
intervals across all sixteen pairs. It also checks (8) against the original
unitary reducer at 64 rational phase/projector instances. The replay
regenerates every Fourier coefficient and uses no floating PSD tolerance.

For real \(U\), an arbitrary rank-one reducer has residual entries
\(V_0+\mu V_1\), with \(V_0,V_1\) real and \(|\mu|=1\).
Its singleton support is affine in \(\Re\mu\); its extrema are the two
real Householder reducers for that pair. The saved certificate checks all
32 extrema exactly and proves (7) for rank one as well.
A rank-three phase differs by a scalar from a rank-one phase, so it gives
the same conjugated normal matrix. These checks cover every projector rank.

Finally,

\[
\eta d_U(a,b)=\det(I+\varepsilon D_tUD_vU^*),\qquad
\eta z_\pi=\prod_i(1+\varepsilon t_i v_{\pi(i)}).
\tag{9}
\]

Both have first coefficient \(F_H\) after taking real parts. For any unitary,
the absolute \(k\)-th coefficient is at most
\(\binom4k T^kV^k\), where
\(T=\max_i(|\Re t_i|+|\Im t_i|)=47/10\) and \(V=103/25\).
Cauchy--Binet and the row sums of the squared-minor matrix prove this bound.
Thus all higher-order differences are bounded by

\[
2\sum_{k=2}^4\binom4k(\varepsilon TV)^k.
\]

Subtracting this from \(\varepsilon/100\) gives exactly (6).

MOC itself holds at (5). The same artifact includes a positive exact
three-permutation law on lexicographic indices \(21,2,5\), with weights
approximately \(0.5975311854,0.1676353322,0.2348334824\).
The verifier checks their full complex moment.

## 3. An exact positive two-reflection law on the same sources

For a real vector \(h\), let \(H_h=I-2hh^T/(h^Th)\). Starting from the
matrix in Section 2, take the following branches, with zero-based indices:

| First vector \(h\) | Reduced pair \((i,j)\) | \(\lambda\) | Probability |
| --- | --- | --- | --- |
| \((0,1,1,1)\) | \((1,3)\) | \(1\) | \(0.23374243958202887\ldots\) |
| \((1,0,1,-1)\) | \((0,3)\) | \(-1\) | \(0.5953679203469171\ldots\) |
| \((0,1,1,-1)\) | \((0,0)\) | \(-1\) | \(0.17088964007105403\ldots\) |

For each branch set \(x=H_hu_j-\lambda e_i\) and

\[
W=(I-2xx^T/(x^Tx))H_h.
\tag{10}
\]

All three matrices are rational orthogonal, satisfy
\(\operatorname{rank}(W-I)=2\), and reduce the specified pair.
Each is nonsymmetric, so none is a single projector phase.
The two reflections do not commute.

Let \(D_k=d_{W_kU}(a,b)\). The exact outer probabilities are the solution of

\[
\begin{pmatrix}
1&1&1\\
\Re D_1&\Re D_2&\Re D_3\\
\Im D_1&\Im D_2&\Im D_3
\end{pmatrix}\theta
=
\begin{pmatrix}1\\\Re d_U\\\Im d_U\end{pmatrix}.
\tag{11}
\]

The saved law gives the resulting positive rational numbers. In each child,
a positive Birkhoff decomposition of its residual three-dimensional
singleton matrix gives a terminal matching law. The combined law has
13 positive permutation weights and exact complex first moment \(d_U\).
Every sign, normalization, unitary identity, reduction, rank, and moment
is checked in rational arithmetic.

This is a source-dependent positive law through genuine normal matrices.
It resolves this particular single-phase obstruction by two phased moves.
Its existence at this input does not establish (4) in general.

## 4. A complete two-phase torus test at a stationary point

For any rank-one orthogonal projectors \(P,Q\), including noncommuting ones,
put

\[
f(s,t)=\Re\{\eta\det(A+e^{isP}e^{itQ}B e^{-itQ}e^{-isP})\}.
\]

The function has Fourier degree at most one in each variable. At a
stationary origin, write

\[
\begin{aligned}
f(0,0)-f(s,t)={}&
 A_1(1-\cos s)+B_1(1-\cos t)
 +C_1(1-\cos s)(1-\cos t)\\
&+D_1\sin s\sin t
 +E_1\sin s(1-\cos t)
 +G_1(1-\cos s)\sin t.
\end{aligned}
\]

The origin maximizes the entire two-phase torus exactly when

\[
M=\begin{pmatrix}
A_1&D_1&G_1\\
D_1&B_1&E_1\\
G_1&E_1&A_1+B_1+2C_1
\end{pmatrix}\succeq0.
\tag{12}
\]

Indeed, with \(x=\tan(s/2)\), \(y=\tan(t/2)\), the deficit times
\((1+x^2)(1+y^2)\) is

\[
2(x,y,xy)^TM(x,y,xy).
\]

The projective image of \((x,y,xy)\) is dense in \(\mathbb{RP}^2\):
a vector \(w\) with nonzero components is represented by
\(x=w_3/w_2,\ y=w_3/w_1\), up to a common scalar.
Thus nonnegativity on this surface forces \(M\succeq0\).
In derivatives at the origin,

\[
M=\begin{pmatrix}
-f_{ss}&-f_{st}&-f_{sst}\\
-f_{st}&-f_{tt}&-f_{stt}\\
-f_{sst}&-f_{stt}&-f_{ss}-f_{tt}-2f_{sstt}
\end{pmatrix}.
\tag{13}
\]

This is an exact finite-jet test for a whole two-phase family, valid in
every dimension and at singular determinant matrices.

For the archived complex Walsh source, choose
\(\lambda=(1+i\sqrt3)/2\), \(e=e_0\), \(u=U[:,0]\),
\(P=(u-\lambda e)(u-\lambda e)^*/(3/2)\), and

\[
h_1=(0,1,-1,0)/\sqrt2,\quad
h_2=(0,1,1,-2)/\sqrt6,\quad Q=vv^*,\quad v=(h_1+ih_2)/\sqrt2.
\]

The exact matrix is

\[
M=\begin{pmatrix}
16&-16&-16/\sqrt3\\
-16&16&-16/\sqrt3\\
-16/\sqrt3&-16/\sqrt3&0
\end{pmatrix},\qquad \det M=-16384/3.
\]

Its Hessian block is PSD. The third-order entries reveal the ascent:
\(f(\pi/2,\pi/2)=24+32/\sqrt3\), and the common reducing phase
\(e^{2\pi i/3}\) reaches support 48. The verifier also checks two
noncommuting stationary examples in dimensions three and four whose
matrices are PSD, by all principal minors.

## 5. Source tangents, optimization, and the remaining bridge

The exact multiplicative chart (9) gives a direct actual-source tangent
for every real assignment cost of rank at most two:

\[
\eta z_\pi=1+\varepsilon\sum_i t_i v_{\pi(i)}+O(\varepsilon^2),\qquad
\eta d_U=1+\varepsilon\sum_{ij}|U_{ij}|^2t_i v_j+O(\varepsilon^2).
\]

A common shift of the \(t_i\) avoids zero entries while adding only a
column cost, hence a constant on permutations and doubly stochastic
profiles. Rational \(t,v,\varepsilon\) give rational complex spectra.
This chart found the counterexample without substituting arbitrary
non-product spectral costs.

For \(n=4\), fixed \((i,j,\lambda)\) in the restricted family (2) leaves
\(Q=H(I+x\cdot\sigma)H^*/2\), \(x\in S^2\). The endpoint unitary is affine
in \(x\). A three-dimensional unitary has the signed singleton formula

\[
w_\pi=\frac{2\sum_k |V_{k,\pi(k)}|^2-1}{6}.
\]

It has total one and the correct singleton marginals; complementary minors
give its determinant identity. Consequently every endpoint support is a
quadratic \(c+\ell^Tx+x^TAx\). With \(g=\ell/2\), its maximum follows from

\[
\sum_\alpha\frac{g_\alpha^2}{(\mu-\lambda_\alpha(A))^2}=1,\qquad
\mu\ge\lambda_{\max}(A),
\]

including the usual top-eigenspace limiting case. The numerical adversary
solves this complementary problem globally, then refines the complete
one-dimensional phase circle. Coarse sampled endpoint hulls can falsely
exclude a profile; the rational circle certificate is what establishes
the strict final inequality.

Earlier exact controls remain in
[coupled_exact_laws.json](../../build/moc_unrestricted_20261031/martingale/coupled_exact_laws.json):
positive coupled laws for both hostile \(Q_{59}\) sources and the
dimension-three polar obstruction, together with exact failures of the
reflection-only and fixed-angle restrictions. They are finite controls.

The unresolved global claim is (4) for general rank-two unitary reducers,
or the weaker statement that an actual support maximum strictly above all
assignment supports must admit a reducing move of equal support.
The counterexample in Section 2 concerns an arbitrary input; it does not
reject that weaker maximum statement. Formula (1) and the torus matrix
(13) provide a larger exact framework for pursuing it.

Reproduction:

~~~sh
python3 code/research/moc_unrestricted_martingale_circle_certificate.py --candidate full_phase_n4_union_rational_candidate.json --include-rank-one --gap 1/100 --epsilon 1/1000000 --output full_phase_n4_union_circle_certificate.json
python3 code/research/moc_unrestricted_martingale_circle_certificate.py --replay --output full_phase_n4_union_circle_certificate.json
python3 code/research/moc_unrestricted_martingale_two_reflection.py --candidate full_phase_n4_union_rational_candidate.json --epsilon 1/1000000
python3 code/research/moc_unrestricted_martingale_two_phase.py
~~~

The new exact results use determinant expansions, elementary spectral
calculus, and rational arithmetic. No external theorem supplies (4).

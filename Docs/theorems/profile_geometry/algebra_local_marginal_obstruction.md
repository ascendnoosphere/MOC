# A quartic obstruction to positive minor transport arbitrarily near the identity

**Status.** This is a theorem about simultaneous permutation-minor weights, not a counterexample to Marcus–de Oliveira. It sharpens the separating functional from Round 100 of `algebra_theorem_notes_081_100.md` by locating the failure on a rational one-parameter path tending to I. It also computes a lower bound on the negative mass of every exact signed representation. No claim of publication priority is made.

Use indices 0,1,2,3. For a real orthogonal matrix O set

\[
q_{I,J}(O)=(\det O[I,J])^2.
\]

A simultaneous permutation law would be a probability lambda on S_4 satisfying

\[
q_{I,J}(O)=\sum_{\pi:\pi(I)=J}\lambda_\pi
\]

for every pair of equal-cardinality subsets. Such a law would prove the determinant identity for every pair of spectra with the same weights. It is stronger than the original, pointwise MOC assertion.

## 1. A five-coordinate separator with an elementary proof

Define

\[
Y(q)=q_{01,01}+q_{01,03}+q_{01,12}+q_{03,03}-q_{02,02}.    \tag{1}
\]

For a permutation profile write the sum of the first three terms as A, the fourth as B, and the last unsigned term as C. The first three events are mutually exclusive, so A,B,C belong to {0,1} and Y=A+B-C.

If A=B=1, then pi maps {0,3} to itself. If pi(0)=3, none of the three events defining A is possible. Thus pi(0)=0 and pi(3)=3. The only possible A-event is pi({0,1})={0,1}, forcing pi(1)=1 and pi(2)=2. Hence C=1.

Therefore

\[
\boxed{-1\le Y(q(P_\pi))\le1\quad\text{for every }\pi.}   \tag{2}
\]

Every probability mixture satisfies Y<=1.

## 2. Exact left-isoclinic calculation

Put

\[
L(a,b,c,d)=
\begin{pmatrix}
a&-b&-c&-d\\
b&a&-d&c\\
c&d&a&-b\\
d&-c&b&a
\end{pmatrix},\qquad s=a^2+b^2+c^2+d^2.
\]

Then L^T L=sI, and for s>0 the matrix O=L/sqrt(s) belongs to SO(4).

The five unsigned minors entering (1), before division by s, are

\[
a^2+b^2,\quad ac+bd,\quad ac+bd,\quad a^2+d^2,\quad a^2+c^2.
\]

Consequently the exact polynomial identity is

\[
\begin{aligned}
s^2\bigl(Y(q(O))-1\bigr)
={}&(a^2+b^2)^2+2(ac+bd)^2+(a^2+d^2)^2\\
&-(a^2+c^2)^2-s^2\\
={}&\boxed{2c(2abd-cs).}                                \tag{3}
\end{aligned}
\]

The repeated cross-minor is ac+bd in BOTH slots. Replacing one of these by ad+bc would give a different, generally false polynomial identity.

## 3. A rational path and a local no-go theorem

Take (a,b,c,d)=(1,t,t^2,t). Its squared norm is (1+t^2)^2. Thus

\[
\boxed{O(t)=\frac1{1+t^2}
\begin{pmatrix}
1&-t&-t^2&-t\\
t&1&-t&t^2\\
t^2&t&1&-t\\
t&-t^2&t&1
\end{pmatrix}\in SO(4).}                               \tag{4}
\]

The entries are rational functions, O(0)=I, and (3) yields

\[
\boxed{Y(q(O(t)))=1+g(t),\qquad
 g(t)=\frac{2t^4(1-2t^2-t^4)}{(1+t^2)^4}.}              \tag{5}
\]

In particular g(t)>0 whenever 0<t^2<sqrt(2)-1.

**Local obstruction theorem.** Every neighborhood of I in SO(4) contains a matrix having no simultaneous nonnegative permutation representation of its squared pair minors. The counterexamples can be chosen with rational entries.

**Proof.** Choose arbitrarily small nonzero rational t satisfying the displayed bound. Equation (5) violates (2). Continuity of (4) gives O(t)->I. This already excludes pair-minor laws, and hence excludes full-minor laws. No numerical search is used. ∎

### An exact rational instance

At t=1/2,

\[
O=\frac15
\begin{pmatrix}
4&-2&-1&-2\\
2&4&-2&1\\
1&2&4&-2\\
2&-1&2&4
\end{pmatrix}.
\]

The five squared minors in (1) are

\[
\frac{400}{625},\quad\frac{64}{625},\quad\frac{64}{625},
\quad\frac{400}{625},\quad\frac{289}{625}.
\]

Therefore Y=639/625=1+14/625.

## 4. A quantitative lower bound on unavoidable negative mass

Suppose a real signed law lambda has total mass one and reproduces these pair coefficients. Let

\[
N(\lambda)=\sum_{\lambda_\pi<0}|\lambda_\pi|.
\]

Its positive mass is 1+N. By the two-sided bound (2),

\[
1+g(t)=Y(q(O(t)))\le(1+N)+N.
\]

Hence every such law satisfies

\[
\boxed{N(\lambda)\ge\frac{g(t)}2
=\frac{t^4(1-2t^2-t^4)}{(1+t^2)^4}.}                    \tag{6}
\]

At t=1/2 the bound is 7/625. This is a lower bound, not an assertion that it is attained.

If a probability law approximates all five coordinates in (1) with coordinatewise error at most epsilon, the same separator gives

\[
\boxed{\epsilon\ge g(t)/5.}                            \tag{7}
\]

Thus the obstruction also has a quantitative approximation version.

## 5. Field change and infinitesimal jets

### Ordered infinitesimals retain the obstruction

Regard t as positive infinitesimal in R((t)), ordered by the sign of the leading coefficient, or in a real closure of that field. All entries in (4) are defined there. Since

\[
g(t)=2t^4+O(t^6)>0,
\]

the same proof excludes a nonnegative simultaneous law over that ordered field.

### Characteristic two annihilates it

The numerator in (3) is divisible by 2 as an integer polynomial. It vanishes identically after reduction to characteristic two. For t=1/2, use the explicit matrix with denominator 5 rather than the parameter: it is defined over Z[1/5] and reduces modulo two to the permutation matrix exchanging 0 with 2 and 1 with 3.

Thus an orthogonal lift of a characteristic-two permutation point can have a real minor profile strictly outside the permutation-profile polytope.

### Low-order jets cannot see this separator

On the path (4), Y(q(O(t))) is identically 1 modulo t^4, yet is strictly larger than 1 for all sufficiently small nonzero real t. A calculation retaining only terms through degree three cannot detect this obstruction. Truncated power-series rings are rings, not fields; passing to them also discards the leading term of this real inequality.

This does not say that all low-order minor information vanishes. It identifies the exact first order at which this particular transport obstruction appears.

## 6. The exact limitation for MOC

If weights lambda_pi(O), independent of a,b, represented

\[
\det(D_a+OD_bO^T)=\sum_\pi\lambda_\pi(O)\prod_i(a_i+b_{\pi(i)})
\]

as a polynomial identity for all a,b, coefficient comparison would force every subset marginal, including the five in (1). The local obstruction therefore rules out any such positive construction in any neighborhood of I.

But MOC permits lambda_pi to depend on a and b. Its assertion is only about the evaluated complex determinant, not simultaneous equality of all polynomial coefficients. Nothing above provides spectra whose determinant is outside the permutation hull.

**Consequences for proof design:** finite-characteristic identities, formal low-order expansions, and local DPP couplings cannot be promoted to universal positive coefficient laws. A valid transfer must preserve only the evaluated spectral functional or establish its support inequality by an additional, genuinely spectrum-dependent argument.

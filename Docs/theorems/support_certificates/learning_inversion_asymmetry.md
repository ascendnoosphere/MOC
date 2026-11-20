## 1. The metric and the strengthened obligation

Let an actual support cost be

\[
c_\pi=\Re\left\{\eta\prod_i(a_i+b_{\pi(i)})\right\},
\qquad h=c_{\rm id}=\max_\pi c_\pi.
\]

Define the **permutation inversion asymmetry**

\[
\boxed{\chi(c)=\max_{\pi\in S_n}
\frac{|c_\pi-c_{\pi^{-1}}|}
{2h-c_\pi-c_{\pi^{-1}}}.} \tag{1}
\]

Set a ratio with denominator zero equal to zero. Its numerator is then zero because both costs equal `h`. Thus `0 <= chi <= 1`.

For an isometry `Y:C^2 -> C^n`, retain the exact plane coefficients from campaign 2:

\[
\mathcal A(T)=\sum_{i<j}(h-c_{(ij)})|(YTY^*)_{ij}|^2,
\quad
g=h-F(I-2YY^*),
\quad
E=\frac14\ell^T\mathcal A^+\ell.
\]

The original full-plane obligation is `g >= E`, including the established kernel compatibility condition. The candidate stronger obligation is

\[
\boxed{g\ge0,\qquad E\le\chi(c)^2g.} \tag{2}
\]

When `g>0`, write `rho=E/g`; then (2) says `rho <= chi^2`. The separate requirement `g>=0` matters at `chi=0`, especially in dimensions above four. Ratio experiments only concern points with positive, numerically resolved `g`.

## 2. A proved covariance law and the missing implication

Split a real cost into inversion-even and inversion-odd parts:

\[
e_\pi=\frac{c_\pi+c_{\pi^{-1}}}{2},\qquad
o_\pi=\frac{c_\pi-c_{\pi^{-1}}}{2},\qquad
c^{(t)}=e+to.
\]

For every `|t| <= 1/chi`, the identity remains a permutation maximizer with the **same** height `h`. Indeed, putting `p_pi=h-e_pi>=0`, all permutation inequalities are exactly

\[
t o_\pi\le p_\pi,
\]

and including the inverse permutation gives `|t o_pi|<=p_pi`. If `chi>0`, `1/chi` is the largest allowed positive scaling. If `chi=0`, then `o=0`.

For the linear squared-minor functional associated with these costs,

\[
\boxed{\mathcal A(c^{(t)})=\mathcal A(c),\quad
g(c^{(t)})=g(c),\quad
\ell(c^{(t)})=t\ell(c),\quad E(c^{(t)})=t^2E(c).} \tag{3}
\]

The first equality follows because transpositions are their own inverses. The third follows from the oriented three-cycle formula for `ell`. For the second, transposition of a unitary interchanges the cost with its inversion. At the Hermitian reflection `R=I-2YY*`, transposition is entrywise conjugation, and every squared minor is unchanged. Thus the inversion-odd part vanishes at the reflection and at the identity.

If the plane support inequality were available for `c^(1/chi)`, (3) would prove (2). **That is the missing step.** The rescaled cost generally does not come from complex spectra.

The algebra track makes the obstruction explicit on an `A_4` conjugation-fixed slice. With shifted class coordinates `(x,y,k)`, the projected spectral nonic restricts to

\[
\pm\frac{x(3y-4x)^2(4k^2+xy-x^2)^3}{32}.
\]

On the generic quadratic branch `4k^2=x(x-y)`, inversion-odd scaling is `k -> tk` and stays on the spectral closure only for `t=+1` or `t=-1`. The full slice analysis is in `algebra_a4_spectral_support.md`. This prevents treating (3) as a proof of (2).

## 3. Classes where the refinement follows

The covariance argument proves (2) for any class of squared-minor costs that has both properties:

1. The class is closed under `c -> e+to` for the allowed interval.
2. Every cost in that interval obeys its permutation support bound on the selected plane.

For example, costs of the assignment form

\[
c_\pi=\sum_i M_{i,\pi(i)},\qquad
F(U)=\sum_{i,j}M_{ij}|U_{ij}|^2,
\]

have these properties. Inversion replaces `M` by `M^T`, so the scaled costs remain assignment costs. The squared-entry matrix is doubly stochastic; its permutation convex decomposition proves each support inequality. This also covers any actual spectral instance whose determinant support reduces to an assignment cost.

The argument applies to a plane supported on at most three coordinates, using the established simultaneous minor probability law in order three. It does not extend automatically to a general plane using four or more labels.

## 4. An exact sharp family with complex spectral data

Choose `u,v>=0`, `u+v>0`, and distinct positive real numbers `t_1,...,t_4`. Put

\[
a=(1,0,0,0),\qquad
q=(0,-u,-v,-u),\qquad
b_j=\frac1{q_j+it_j},\qquad
\eta=\frac1{\prod_jb_j}.
\]

All spectral entries are finite. The `b` spectrum is complex and can be chosen noncollinear. The determinant lemma gives, for every unitary,

\[
\eta\det(D_a+UD_bU^*)
=1+\sum_j(q_j+it_j)|U_{1j}|^2.
\]

Consequently

\[
c_\pi=1+q_{\pi(1)},\quad h=1,\quad
h-F(U)=u|U_{12}|^2+v|U_{13}|^2+u|U_{14}|^2.
\]

For a permutation moving label one, its image and inverse image lie in `{2,3,4}`. The corresponding deficits are `u` or `v`, and both values can occur in one inverse pair. Therefore

\[
\chi=\frac{|u-v|}{u+v}. \tag{4}
\]

Take the plane of vectors in the first three coordinates with coordinate sum zero. Use the raw frame

\[
K=\begin{pmatrix}1&0\\-1&1\\0&-1\\0&0\end{pmatrix},
\quad G=K^*K=\begin{pmatrix}2&-1\\-1&2\end{pmatrix},
\quad Y=KG^{-1/2}.
\]

Use Hermitian raw coordinates `S=[[s,x+iy],[x-iy,t]]` and `T=G^(1/2)SG^(1/2)`. Then `YTY*=KSK*`. Direct substitution gives

\[
\mathcal A(T)=u(s-x)^2+vx^2+(u+v)y^2,
\qquad
\ell(T)=\frac{4(v-u)}3y,
\qquad
g=\frac49(u+v).
\]

Only the `y` coefficient contributes to the least energy, hence

\[
E=\frac{4(u-v)^2}{9(u+v)},\qquad
\boxed{\rho=\frac Eg=\left(\frac{u-v}{u+v}\right)^2=\chi^2.} \tag{5}
\]

This remains valid when either weight is zero: the extra kernel directions still annihilate `ell`. Taking `u=1-chi`, `v=1+chi` attains every `chi` in `[0,1]`.

For completeness, with `d=det S` and `D=det(I+T^2)`, the whole-plane numerator has the exact sum of squares

\[
(h-F(V(T)))D
=4\left[
u(s-x)^2+vx^2
+(u+v)\left(y-\frac{v-u}{u+v}d\right)^2
+\frac{4uv}{u+v}d^2\right].
\]

This proves sharpness of coefficient one in (2). It is a solvable assignment-cost family and does not establish the conjectured inequality for generic spectra.


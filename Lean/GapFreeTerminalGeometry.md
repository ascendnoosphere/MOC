# Terminal geometry without fixing the determinant gap

A strict witness is called contact-maximal here when no strict witness
for its fixed mixer has more contacts. “Contact” means a maximizing
permutation label for the given real support direction.

## Exact profile isolation

[`GapFreeContactFibre.lean`](MOC/GapFreeContactFibre.lean) fixes only
the complex differences from an active pivot. If a positive-dimensional
prime branch through a strict witness preserved those differences, a
finite affine curve in that branch would preserve them too. The existing
varying-gap continuation covers a nonconstant determinant gap; the
fixed-gap transfer covers the constant case. Either gives a strict witness
with more contacts. The evaluation prime is therefore minimal over the
difference-fibre ideal. A polynomial separates the witness from the
other minimal components, so the exact fibre is locally a singleton.
The complex determinant gap is not among the imposed equations.
For the earlier contact strategy, see [Zheng, preprint DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923).

This does not imply a nonsingular Jacobian at the original witness:
an isolated fibre may have multiplicity.

## Zero products and cuts

[`ZeroAwareContactCut.lean`](MOC/ZeroAwareContactCut.lean) refines
the balanced-cut test. Relative to any reference assignment, a proper
cut must be crossed by a **nonzero** active product, or it must cut
**every** zero factor of some zero active product. Merely having a
crossing nonzero factor in a zero product is not enough to stop the
transfer. If one vanishing factor stays inside either block, that product
stays zero along the opposite translation. For a nonzero product, a
crossing factor makes its degree positive. The resulting all-order
incidence condition says that preserving all nonzero contact edges and
any one zero edge per zero contact leaves only the common translation.

For zero-free data, [proportional incidence rigidity](MOC/ProportionalContactRigidity.lean)
allows a separate first-order form on each row of the contact graph.
An exact normalized affine motion fixes the old products. Isolation
forces every matching product to stay fixed in that normalization.
Switching the assignments of two columns and comparing the two
coefficients of a quadratic in the motion parameter gives additive
separation of the row and column rates, and vanishing mixed
differences. Unless a spectrum is constant, the rates are all equal.
Only common scaling and translation remain. In particular, a covering
set of contact edges has at least $3n-2$ distinct edges: it imposes
one linear equation per edge on $3n$ rates, and the kernel is exactly
the two trivial directions.
[An extension on paper](ProportionalContactRigidityWithZeros.md)
gives the same bound for simple spectra in orders at least four
with vanishing sums, counting only one selected zero edge per zero
contact. The zero-free bound is the Lean result.

## Disjoint cycles at an exposed support

[`CollisionSplitSupport.lean`](MOC/CollisionSplitSupport.lean) splits
the relative permutation of two endpoints on any invariant set. If the
two endpoint products are on the same nonzero ray of the support line
through zero, their rotated product is negative real. The complementary
split values multiply to the same negative real. Since each has
nonpositive real part, each must have zero real part. Independently
choosing the relative cycles then gives at least $2^k$ contact labels for
$k$ nontrivial relative cycles. All those labels preserve every
cut invariant under the relative permutation. At a contact-maximal
witness any proper such cut therefore forces at least one further
contact outside the cube.

For a collision of complex endpoint products, write $p$ for their
common rotated value and $u,v$ for the split products. Then $uv=p^2$.
If $H=\operatorname{Re}p$ and $D(z)=H-\operatorname{Re}z$, the exact identity is
$$
D(v)|u|^2 + D(u)|p|^2 = H|u-p|^2.
$$
If $u\ne p$, a negative upper height is impossible, and at positive
height at least one of the intermediate products is strictly off the
support line. At a nonzero pivot and simple spectra, choosing a single
transposition cycle always gives $u\ne p$. This tests collisions without
assuming that the other matching products are distinct or nonzero.

## Application to the positive-height order-four branch

For the [six-label $T_{85}$ pattern](ZhengT85Independent.md) of
[Zheng, Section 5](https://doi.org/10.13140/RG.2.2.36790.25923), the
nonzero-height branch has $P_0=P_7$ and positive upper height. Thus at
least one of labels 1 and 6 is [inactive in Lean](MOC/ZhengRectangleContact.lean): they are the two complementary
splits of label 7. This does not rule out a different eighth contact.

On paper there is a direct projective chart for the collision. Write $c=-b$
and temporarily use row-to-column permutation labels. The equality
$P_0=P_7$ pairs two ordered quadruples
$
(a_1,a_2,c_1,c_2),\qquad(a_3,a_4,c_4,c_3).
$
In fact the two cross ratios
$
\frac{(a_1-c_1)(a_2-c_2)}{(a_1-c_2)(a_2-c_1)}
\quad\hbox{and}\quad
\frac{(a_3-c_4)(a_4-c_3)}{(a_3-c_3)(a_4-c_4)}
$
are equal by canceling the four factors on each side of the collision.
The marked points are distinct at any strict order-four witness, so
the unique Möbius map sending the first three entries of the first
quadruple to the corresponding three of the second sends the fourth
as well. The matching profile is unchanged up to a nonzero common
factor under a common projective change of chart.

If that map has two fixed points, and its fixed points are not among
the marked points, put them at $0,\infty$. Then
$
a=(x,y,\lambda x,\lambda y),\qquad c=(u,v,\lambda v,\lambda u).
$
Writing $g_j=P_j-P_0$, direct factorization gives
$
\frac{g_5}{g_9}=-\frac{\lambda u-v}{u-\lambda v},\qquad
\frac{g_9}{g_{14}}=
\frac{y(x-u)(x-v)}{x(y-u)(y-v)}.
$
These ratios are real on the exposed face. The denominators do not
vanish here: $g_{14}$ is a nontrivial transposition difference, and
$g_9g_{18}=g_5g_{14}$ by the checked collision identity. Hence these
give two concrete real one-variable tests rather than another basis
for the full contact cone.

For the two-fixed-point chart, put $r=(\lambda u-v)/(u-\lambda v)$
and $q=(\lambda-1)/(\lambda+1)$. In the generic case $\lambda\ne-1$
the ratios give $v/u=(\lambda-r)/(1-r\lambda)$ and
$$
R_B=\frac{(u-\lambda u)(v-\lambda v)}
          {(u-\lambda v)(v-\lambda u)}
    =-\frac{(1-r)^2-(1+r)^2q^2}{4r}.
$$
Here $r$ is real, nonzero, and not $-1$ (which would make $u=v$).
Thus $R_B$ is real exactly when $\operatorname{Im}(q^2)=0$,
equivalently when $\lambda$ is real or has unit modulus. By the
four-point circle criterion and [Zheng's one-circle result, Appendix C](https://doi.org/10.13140/RG.2.2.36790.25923),
this excludes both of those families on paper, subject to the chart
hypotheses. It does not treat $\lambda=-1$ or a fixed point among the
marks. The orientation-sensitive [alternating moment formula](AlternatingGapMoments.md)
also records the nonzero circle discriminants outside those families.

For the parabolic map, provided its fixed point is not marked, the
common affine chart is $a=(x,y,x+t,y+t)$ and
$c=(u,v,v+t,u+t)$ with $t\ne0$. Now
$g_5/g_9=(t+u-v)/(t-u+v)$ is real, forcing $(u-v)/t$ real by the
inverse real fractional linear map. Hence $c$ is collinear in that
chart. This branch is covered on paper by the one-generalized-circle
case in [Zheng, Appendix C](https://doi.org/10.13140/RG.2.2.36790.25923);
that one-circle theorem is not being assumed as a Lean lemma here.
The remaining generic chart still needs a support comparison under
the extra contact equations. No numerical search, permutation
enumeration, or arithmetic certificate is used in these reductions.

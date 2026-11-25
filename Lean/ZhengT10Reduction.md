# Group III: an exact reduction for T10

This is a paper reduction, not an order-four proof. Use the zero-based
row-to-column labels in [Zheng, Appendices E and G](https://doi.org/10.13140/RG.2.2.36790.25923).
Let $P_i$ denote the matching products and $\Gamma_i$ their
upper-support gaps. In T10, swap rows 1 and 2 and columns 1 and 3:
the contacts $0,1,3,5,7,8$ become $0,1,2,3,19,20$. All labels
below refer to the relabeled profile. Repeated eigenvalues or a
vanishing cross factor already have order-four inclusion proofs.
We only consider simple, disjoint spectra below.

## Projective coordinates

Write the second spectrum with its sign reversed. Comparison of
$(P_3-P_2)/(P_1-P_0)$ gives a real cross ratio on first-spectrum
point $A_1$ and second-spectrum points $C_1,C_2,C_3$. Use a common
projective transform to put $A_1=\infty$, $C_1=1$, $C_2=0$,
$C_3=t$, with $t\in\mathbb R\setminus\{0,1\}$. Use incidence
factor 1 at infinity. The homogeneous bracket scaling is a common
nonzero factor on the matching products and their real signed
determinant evaluation. Adjust the support direction by its inverse.
The finite-coordinate version of this covariance is checked in
[ProjectiveTransport.lean](MOC/ProjectiveTransport.lean).

Let the first list be $(x,\infty,z,a)$ and the signed second list
$(w,1,0,t)$. Put $D=P_0-P_2$, $R_i=(P_0-P_i)/D$ and
$l=R_1$. Then
$$
D=(x-w)(a-t),\qquad P_0/D=z,\qquad
a=t(l-z)/(l-t).
$$
Here $l$ is real and $l\ne0,t$. The second inequality follows since
$l=t$ would give $z=t$; the first follows from the nonzero one-swap
difference $P_0-P_1$. All matching ratios defining the contacts are
real. If $z$ is real, the six spectators in the two lists are real
projective points and the support height is zero. Move infinity to
a finite point by a common real projective map avoiding poles on
both lists, and apply
[four_real_spectators_zero_height_support](MOC/ZhengStabilizerSupport.lean).
For this theorem the projected factor of the two outliers vanishes:
the full pivot product projects to zero, and its other three
factors are real and nonzero.

Take $z$ nonreal. Replace the two spectra and the support multiplier
by their conjugates if necessary, and positively rescale the multiplier,
so that $\Gamma_i=\operatorname{Im}R_i$. Indeed $\eta D$ is nonzero
pure imaginary, and the original gaps are
$-\operatorname{Im}(\eta D)\operatorname{Im}R_i$. Conjugation
preserves the projected permutation values and the value at a
fixed mixer via the real signed-weight identity of
[Merikoski and Virtanen](https://doi.org/10.1016/0024-3795(89)90709-X).

Put $q=R_{19}$, $r=R_{20}$, $\lambda=l/t$, $s=1-t$, and
$c=1-\lambda s$. Set $T=(x-t)/(x-w)$. The two extra contacts give
$$
T=\frac{(z-q)(a-t)}{z(a-1)},\qquad
w=z-\frac{(z-r)z(a-1)}{(z-q)a},\qquad
x=\frac{Tw-t}{T-1}.
$$
For example $P_{19}/D=Tz(a-1)/(a-t)$ and
$P_{20}/D=T(z-w)a/(a-t)$. The chart denominators here do not
vanish at a simple, disjoint starting profile with nonreal $z$;
in particular $T-1=(w-t)/(x-w)\ne0$. Conversely these formulas
preserve all six contacts with $t,l,q,r$ fixed real and $z$
varying, at every regular chart point. The old four normalized
differences are $0,l,1,1+l-l/t$.

## Exact minor comparison and the remaining defect

Write $S_{ij}$ for the singleton assignment indicator, and
$M(I\to J)$ for the two-subset image indicator. The corresponding
linear evaluations on a unitary are squared minors, by the signed
subset-image law of Merikoski and Virtanen cited above. Use
$A=01$, $B=02$, $C=03$; complements are relative to all four
labels. The following nine indicators vanish on the six contacts:
$$
(S_{01},S_{02},S_{13},S_{30},
M(A\to12),M(A\to23),M(B\to12),M(B\to13),M(C\to12)).
$$
They span the whole zero-at-these-contacts subspace. Here are
details avoiding a facet classification. The full subset-image
span has dimension at most 14: the singleton span has dimension
at most 10 by row and column sums. For a pair, the difference
of complementary target indicators is the size of the
intersection with the target minus one, hence a singleton
combination. Their sum is an assignment indicator for the
three pair partitions and contributes at most four further
dimensions. The six contact evaluations are independent.
On the fibre with row 0 fixed, the singleton matrix span in
order three has dimension five by Birkhoff's theorem and its
only relation among six evaluations is the alternating sum.
Thus its four listed evaluations are independent. On the other
two contacts the indicators $S_{03}$ and $M(A\to03)$ are
independent and both vanish on the first four: the first
selects both contacts 19 and 20 and the second selects only 19.
This bounds the dimension of the constrained subspace by eight.

Write $c_0,\ldots,c_8$ for the nine marker coefficients in the
displayed order. Their evaluations at labels
$4,6,8,12,13,18,21,22$ are
$$
c_2,\quad c_0+c_6,\quad c_0+c_4,\quad c_1+c_6,\quad
c_1+c_8,\quad c_7,\quad c_3,\quad c_5.
$$
These eight equations have a solution for arbitrary values,
with $c_1$ free, proving spanning. Evaluation of the markers at
label 14 gives $c_1+c_4=\Gamma_{14}$ and evaluation at 7
gives $c_0+c_7+c_8=\Gamma_7$. Consequently the exact gap
expansion has the coefficients
$$
(\Gamma_6-\Gamma_{12}+u,\ u,\ \Gamma_4,\ \Gamma_{21},
\Gamma_{14}-u,\ \Gamma_{22},\ \Gamma_{12}-u,\ \Gamma_{18},
\Gamma_{13}-u)
$$
for arbitrary real $u$. These identities also apply after
spectral deformation, since projected matching products belong
to the subset-image span by direct expansion.

Let $E=\Gamma_{18}-\Gamma_7$. If $E\le0$, choose
$u=\max(0,\Gamma_{12}-\Gamma_6)$. It is bounded by
$\Gamma_{12},\Gamma_{13},\Gamma_{14}$ respectively using
$\Gamma_6\ge0$, $E\le0$, and $\Gamma_8\ge0$. Thus the
expansion uses only nonnegative squared minors, which proves
the support bound in this branch.

If $E>0$, choose $u=\Gamma_{13}$ and set
$$
h=-S_{01}+S_{13}+M(A\to12)+M(B\to12)+M(B\to13).
$$
Then the gap is $E h$ plus seven nonnegative terms:
$$
\Gamma_{13} S_{02}+(\Gamma_4-E)S_{13}+\Gamma_{21}S_{30}
+(\Gamma_{14}-\Gamma_{13}-E)M(A\to12)
+\Gamma_{22}M(A\to23)+\Gamma_6M(B\to12)
+(\Gamma_{18}-E)M(B\to13).
$$
Nonnegativity of the three coefficients with $-E$ follows
from the values at labels 10, 8, and 7. The same $h$ as in
[T15](ZhengT15Support.md) has the alternate expression
$S_{02}+S_{30}+M(A\to03)-M(B\to23)$. To verify it, first use
$S_{01}+S_{02}=M(A\to12)+M(B\to12)+M(C\to12)$.
Then let $p,r$ be the row preimages of columns 0 and 3,
respectively. The sum $M(B\to13)+M(B\to23)$ is the indicator
of $r\in\{0,2\},p\in\{1,3\}$, while
$M(A\to03)+M(C\to12)$ is the indicator of
$1\in\{p,r\},3\notin\{p,r\}$. Their difference is
$1_{p=3}-1_{r=1}=S_{30}-S_{13}$. Therefore the
[checked paired-cofactor inequality](MOC/ZhengT15Gram.lean),
together with the Hodge calculation in the T15 note,
proves the T10 bound whenever
$$
                        \Gamma_6\Gamma_{22}\ge E^2 .
$$
This sufficient spectral inequality is **not established** in
general. Realification is available in
[FourMinorTransport.lean](MOC/FourMinorTransport.lean) if this
orthogonal comparison applies.

## Harmonic reduction to smaller boundary problems

The following finite formulas suffice to prove the compact
reduction. Put $B_0=(1-w)/(x-w)$. Direct factor cancellation gives
$$
\begin{aligned}
 R_4&=[l-(l-t+1)z]/(t-z),\\
 R_6&=z B_0,& R_7&=l+(z-l)B_0,\\
 R_{18}&=q+\lambda T,& R_{22}&=r+(z-r)/a .
\end{aligned}
$$
In particular, $\Gamma_4$ has at most a pole at $t$ and tends to
zero at infinity. The imaginary part of $R_{18}$ has possible
poles only at $0,c$, since
$T=(z-q)(t-z)/(z(c-z))$. Neither pole is $t$:
$c-t=(1-t)(1-l/t)\ne0$. Since
$0<E\le\min(\Gamma_4,\Gamma_{18})$ in the signed branch, the
negative part of the determinant gap of a fixed unitary is
bounded near every finite point and tends to zero at infinity.
Indeed the only signed term is $E h$, and the minor evaluation
of $h$ is constant along the curve.

Thus a strict witness in this chart can be moved to a regular
boundary point at which the determinant gap is still negative.
Here is the compact argument. Fix the mixer and the real
parameters $t,l,q,r$. In the open locus where $E>0$, the
determinant gap is negative and all nonpersistent gaps are
positive, it is harmonic. If any other gap is already zero,
we start at the desired boundary. Otherwise take the open
component of the initial point. At regular boundary points a
negative determinant gap can persist only at an additional
contact: the $E=0$ comparison holds, and at real $z$ all
projected rational functions are zero off their poles. Poles,
coincidences, and zeros of chart denominators are a finite
set, since their rational conditions are not identities at the
initial point. They cannot carry a negative minimum. To see
this, truncate at large radius with lower bound $-\epsilon$
on the outer circle, add $\epsilon$ and the barriers
$\delta\log(C_0/|z-z_j|)$ at each exceptional point, and
remove small disks around them. Here $C_0$ is larger than the
diameter of the truncation disk and $\delta>0$. The lower
bound above and the diverging barriers give nonnegative
values on the new boundaries. The minimum principle then
applies. Let $\delta\downarrow0$ and then $\epsilon\downarrow0$.
This gives a contradiction if there is no regular additional
contact with a still-negative objective.

For $E>0$, $h$ is positive at every noncontact except
$6,7,8,10,13,21,22$. This last incidence assertion does not
require the contact-cone classification: from the first
expression for $h$, group by the row-0 image. For image 0
the only noncontacts are 4 and 5, where $S_{13}=1$.
For image 1, the negative singleton is cancelled by exactly
one or two of the other terms; among labels 6 to 11, exactly
9 and 11 contribute two (and the other four contribute one).
For image 2, only 13 contributes none. For image 3, only
19,20,21,22 contribute none. Since the other coefficients
are nonnegative, these are the only possible additional
contacts in the strict branch.

If 22 is a contact in the nonreal chart, then $r=l$ by the
formula for $R_{22}$. In fact $E=0$ in this situation.
For an explicit check put $R=c-q$; then
$w=zR/(z-q)$ and
$1/(x-w)=(U-1)/(w-t)=-(z-q)/(z(c-z))$, where $U=T$.
It follows that
$$
\Gamma_6=(1-c)\operatorname{Im}[w/(x-w)].
$$
Also $\lambda T+lB_0=\lambda+(1-c)w/(x-w)$, and hence
$E=(1-c)\operatorname{Im}[w/(x-w)]-\Gamma_6=0$.

The same chart describes the other boundary labels. To record
their exact reduction, use composition of permutation images
right to left. Let $L$ apply the transposition $(1\,2)$ to
column labels, $R$ apply $(2\,3)$ to row labels, and
$J(p)=(1\,3)p^{-1}(1\,3)$. These operations preserve the base
four contacts $0,1,2,3$. The extra labels are transformed as follows:
- With 6, $LJR$ sends the three extra labels $19,20,6$ to
  $19,7,22$, so the boundary includes the normalized T11 pattern.
- With 8, $LJR$ sends $19,20,8$ to $19,7,8$, which includes T3.
- With 10, $LJ$ sends $19,20,10$ to $18,6,11$, which includes the
  T5 pattern in its four-contact chart.
- With 13, $J$ sends $19,20,13$ to $19,12,22$, which includes T11.
- With 21, $LR$ sends $19,20,21$ to $19,23,22$, which includes T11.

The normalized T11 pattern above is $\{0,1,2,3,19,22\}$; it is
obtained from Zheng's representative by swapping rows 1 and 2
and columns 1 and 3. The T5 four-contact chart is
$\{0,1,2,3,6,11\}$, obtained by column relabeling $(0,1,3,2)$
and row relabeling $(0,2,3,1)$ in one-line notation.

**Unresolved:** [T11](ZhengT11Chart.md) and T5 are not proved by this note.
The boundary 7 is not identified with any of the preceding
patterns, and its spectral cofactor inequality remains open.
In the boundary-7 chart one can set
$b=(z-l)B_0\in\mathbb R$ and obtain
$$
\Gamma_6=\frac{-b l\,\operatorname{Im}z}{|z-l|^2},\qquad
\Gamma_{22}=\frac{(l/t-1)(l-r)\,\operatorname{Im}z}{|z-l|^2},
\qquad
E=\operatorname{Im}\left[-\frac{(l-r)(1-t)}{w-t}\right].
$$
The last identity follows by comparing the swaps $7\to18$ and
$1\to20$, both exchanging rows 0 and 2: their difference ratio
is $(1-t)/(w-t)$. These identities state the remaining sufficient
inequality without claiming it. The complete T10 support
comparison is not proved here.

# T40 and the dependencies of T85

This note uses the permutation numbers of Zheng's order-four
preprint, [DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923).
The determinant weights and subset-image evaluation are those of
Merikoski and Virtanen, [DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X).
A contact is a permutation attaining the upper support in the
chosen direction, and $\Gamma_j$ denotes its nonnegative gap.

## T81 is not needed for T85

Use the [checked transfer to a noncentral contact](MOC/ZhengT81Bypass.lean), which combines the eight-contact bound and the
[marked row and column](ZhengT85Independent.md) from the positive-height
T85 analysis. There are six contacts in the block group. Its other
two labels, 16 and 23, have the same strictly positive gap. At least
two crossing contacts must therefore lie on the marked row or column.

The two marked cells are exchanged by inversion of the permutations,
which preserves T85 and corresponds to interchanging the spectra and
adjointing the relative unitary. Thus use the orientation with mark
$\pi_{17}=(3,4,2,1)$ in one-based row-to-column notation. The block
flips form $F=\{1,(13),(24),(13)(24)\}$. The row and column of the mark
are $\pi_{17}F$ and $F\pi_{17}$: flip either of the two slots, or the
corresponding two values. The noncentral cells are precisely
$6,11,12$ and $1,4,15$, respectively. This uses only the two block
flips, not a search over the permutations.

At least one crossing contact must be noncentral. By Zheng's Table
3, labels 1 and 6 invoke T40, while 4, 11, 12 and 15 invoke T55. The
only arm of Table 3 that invokes T81 is the central label 17, so it
is unnecessary. In fact, if all four T55 arm labels are inactive,
1 and 6 cannot both be active by the checked collision relation.
The two required crossing contacts must then be the center and one
of 1 or 6, and there are exactly eight contacts in total. Lean
checks this dichotomy in `narrow_t85_cases_at_eight` and the
change of orientation in `t85_of_one_orientation_arm_cases`.
This isolates the two small T40 overlaps needed for this approach.
It does not prove their inequality.

The T55 overlaps also collapse to one seven-label pattern. In Table 3,
the four T55 relabelings for extra contact 4, 11, 12 or 15 omit,
respectively, T85 label 14, 18, 9 or 5 from the displayed image.
Undoing the indicated relabeling sends each omitted label to 20,
whose zero-based tuple is `3102`. Thus the unresolved T55 input for
T85 is T55 with label 20 also active, not all of standalone T55.


## T40 at zero support height

The four nonpivot labels 5, 9, 14 and 18 suffice. The two disjoint
swaps 5 and 14, together with pivot 0, force label 16 to be a contact
when the support line passes through zero. The rotated pivot is
nonzero in a strict counterexample: a vanishing pair sum already
implies the order-four inclusion. Projecting the linear identity
from the [T85 rectangle](MOC/ZhengRectangleContact.lean) now gives
$\Gamma_7+\Gamma_{23}=0$. Thus both gaps are zero and the paired
T85 certificate applies to every unitary. Lean verifies this in
[ZhengT40Support.lean](MOC/ZhengT40Support.lean); label 1 is not needed.

For strictly negative upper height, Drury's published external-vertices
theorem, [DOI 10.13001/1081-3810.1131](https://doi.org/10.13001/1081-3810.1131),
applies in order four. Reverse and rescale the support functional so
that the matching points have a positive lower bound; the source
proves the same lower bound for the actual determinant. This
external theorem is not a Lean proof of the strictly negative
branch here.

The [direct T55 proof](ZhengT55ZeroHeight.md) also closes its zero-height branch on paper.

## The exact linear comparison for T40

Use the six T40 zero gaps $0,1,5,9,14,18$ and the coordinates
\[
(a,b,c,d,e,f,s,t)=(\Gamma_3,\Gamma_4,\Gamma_8,\Gamma_{12},
\Gamma_{15},\Gamma_{20},\Gamma_7,\Gamma_{23}).
\]
The other independent inequalities in this chart are
\[
 c+d\ge a+b,\quad f+d\ge a,\quad t+d\ge a,\quad
 e+c\ge b,\quad t+c\ge b .
\]
For a way to reproduce the linear relations, put $h$ for the lower
projected pivot. In the Appendix A bracket basis the lower-projected
matching coordinates are
\[
\begin{split}
(&a+b-c-d+s,\ c+e,\ d-a,\ -e,\ -s,\ d+f,\ t-a-b-e-f,\\
 &a-d-f,\ c+d-a-b-s,\ e+f-t,\ -f,\ b-c-e,\ c-b,\ h+t).
\end{split}
\]
This is obtained by straightening crossing brackets via
$[ik][jl]=[ij][kl]+[il][jk]$ for $i<j<k<l$ and eliminating the six
prescribed pivot/contact equations. The gaps in increasing order
are then
\[
(0,0,a+b,a,b,0,c+d-a-b,s,c,0,f+b+s,f+d-a,d,
 e+a+s,0,e,t+s,t+d-a,0,e+c-b,f,f+e,t+c-b,t).
\]

There is an elementary decomposition of this entire linear cone.
Set $\delta_a=(a-d)_+$ and $\delta_b=(b-c)_+$, at most one of which
is nonzero by $c+d\ge a+b$. Subtract $\delta_a$ times the ray with
$a=c=f=t=1$ and $\delta_b$ times the ray with $b=d=e=t=1$.
What remains is a nonnegative combination of eight subset-image
indicators: the rays with $a=d=1$, $b=c=1$, and each of the six free
single coordinates $c,d,e,f,s,t$. Explicitly their coefficients are
\[
a-\delta_a,\quad b-\delta_b,\quad c-b+\delta_b-\delta_a,\quad
d-a+\delta_a-\delta_b,\quad e-\delta_b,\quad f-\delta_a,\quad
s,\quad t-\delta_a-\delta_b .
\]
In the order just given, the corresponding source-to-target pairs
are $01\to02$, $02\to01$, $03\to13$, $02\to12$, $02\to23$,
$01\to13$, $03\to12$, $01\to23$, using zero-based labels.
Thus the genuine T40 inequality holds whenever $a\le d$ and $b\le c$,
without any further condition on the mixer. Transposing interchanges
the two remaining rays.

The mixed ray $a=c=f=t=1$ cannot simply be declared nonnegative on
orthogonal mixers. Its signed evaluation in terms of squared
two-minors $q(I\to J)$ is
\[
q(01\to02)+q(01\to13)+q(03\to13)-q(02\to12)+q(01\to23).
\]
Indeed its vector is the sum of the ordinary rays for $a=d=1,c,f,t$
minus the ordinary $d$ ray. For an explicit symbolic obstruction
use the self-dual and anti-self-dual rotations $L,R\in SO(3)$ on
two-forms, with pair coordinates $01,02,03$ and complements set by
the Hodge star. All pairs $(L,R)$ occur from real oriented
orthogonal $4\times4$ matrices by the quaternion parametrization.
The displayed objective equals
\[
\tfrac12(L_{10}^2+R_{10}^2)+
\tfrac14\big((L_{12}-R_{12})^2-(L_{21}-R_{21})^2+(L_{00}-R_{00})^2\big).
\]
Take $L=M(1,1)$ and $R=M(u,u)$ for $\sqrt2-1<u<1$, where
\[
M(v,w)=\begin{pmatrix}
v &-\sqrt{1-v^2}\,w &\sqrt{1-v^2}\sqrt{1-w^2}\\
0 &\sqrt{1-w^2}&w\\
-\sqrt{1-v^2}&-vw&v\sqrt{1-w^2}
\end{pmatrix}.
\]
The first two rows have unit norm and are orthogonal, and their
cross product is the third row. Substitution gives
$(1-u)^2(2-(1+u)^2)/4<0$. This violates the linear relaxation,
not MOC. Repairing T40 at strictly positive height therefore
requires the actual nonlinear spectral relations, not merely
the six contact gaps and nonnegativity.

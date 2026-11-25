# The positive-height T55 overlap in T85

This note uses the row-to-column lexicographic labels of
[Zheng, §5 and Table 3](https://doi.org/10.13140/RG.2.2.36790.25923).
Write $P_i$ for a matching product and
$\Gamma_i=H-\operatorname{Re}(\eta P_i)$ for its upper-support gap.
The overlap has the seven contacts $1,2,3,6,11,12,20$. Swapping
columns 2 and 3, with indices starting at 0, takes these to
$0,4,5,7,9,14,18$: T85 and arm 4. In the T85 orientation used here,
the canonical T55 centre 23 is T85 label 17; the six other arm labels
$0,7,9,18,21,2$ become $1,6,11,12,15,4$, respectively.
The five boundary comparisons are in
[ZhengT85ArmBounds.md](ZhengT85ArmBounds.md).

These four arm reductions preserve the negative mark, not only the
six base labels. In T85 coordinates let $h=(01)(23)$, $v=(02)(13)$,
and let $p$ be label 17. The block group has six contact labels,
with the missing coset $v\{1,h\}$. Conjugation by $h$ and the
map $q\mapsto q^{-1}h$ each preserve the block group and its
missing coset. They fix $p$, since $p^2=h$.
Conjugation by $h$ exchanges arms $4,15$ and arms $11,12$;
$q\mapsto q^{-1}h$ takes arm 11 to arm 4. These are direct
substitutions on the marked row and column. Inversion switches the
two spectra and adjoints the relative unitary; multiplication by
$h$ is an index relabeling. If the other mark was negative,
first use inversion to bring it to label 17. Thus whenever the
T85 reduction uses one of the four T55 arms, the chart below
applies with the negative mark at canonical label 23.

## Signed two-minor formula

The paired or nonnegative-residual cases of
[the T85 reduction](ZhengT85Independent.md) already give the support
inequality. In the positive-height unpaired case the T85 collision
$P_0=P_7$ becomes $P_1=P_6$ in T55 labels. The negative-residual
orientation of T85 uses just one marked row and column. If there are
at least eight contacts and arm 4 is used to identify the T55 overlap,
choose its relabeling as in Table 3, with the mark at T85 label 17.
Equivalently, the following formula is for the T55 chart with mark at
23. When that mark's residual is nonnegative and the opposite mark's
residual is also nonnegative, the nonnegative-residual certificate
applies directly.

Put $A=\{0,1\}$, $B=\{0,2\}$, $C=\{0,3\}$.
For any two sets $I,J$ of size two, write $I\to J$ for the
indicator that the permutation sends $I$ onto $J$. Complements of
both sets give the same indicator. The block assignment sends $B$
to either $C$ or $C^c$. The crossing indicator $X$ is the
complement of this event. The defect is $E=(A\to A^c)$; it takes
value one on the two noncontacts in the block group. The marked row
is $e=(B\to B^c)$, and the marked column is $h=(C\to C)$.
If the common noncontact block gap is $d$, the coefficient of the
signed marked star is $\beta=d-\Gamma_{23}$.

The two-set preimage of $C$ is either $B,B^c$ in the block group,
or one of $A,A^c,C,C^c$ in the crossing group. Thus
$X=a+b+h+g$, where $a=(A\to C)$, $b=(A\to C^c)$,
and $g=(C\to C^c)$. The other marked-row cells have gaps
$\Gamma_{18},\Gamma_9,\Gamma_7$ in these three columns respectively.
For a marked-column cell, the possible images of $B$ are
$A,A^c,B,B^c$, and the other three cells have gaps
$0,\Gamma_{21},\Gamma_0$, respectively. These identifications use
only the row and column of the mark, not the other crossing cells.

The checked marked-star identity
$\Gamma_{23}E+\beta(E+X-e-h)$ plus the unmarked arm terms
therefore equals the full gap function. Writing $c=E,\ d_0=(B\to B)$
and $f=(B\to A^c)$, this gives
$$
 \Gamma=(\Gamma_{18}+\beta)a+(\Gamma_9+\beta)b+
  (\Gamma_{23}+\beta)c+\Gamma_0d_0-\beta e+
  \Gamma_{21}f+(\Gamma_7+\beta)g .                 \tag{1}
$$
The only block gaps with value $d$ are 17 and 22 in canonical
T55 coordinates, so $\Gamma_{17}=\Gamma_{23}+\beta$.
The two crossed cells 4 and 8 with $E=0$ and the zero-gap
unmarked column arm have gaps $\Gamma_{18}+\beta$ and
$\Gamma_9+\beta$, respectively; the corresponding cell 10 has
gap $\Gamma_7+\beta$. In particular $\beta=\Gamma_{10}-\Gamma_7$.
Alternatively these three evaluations follow at once by applying
(1) to $(0,3,1,2)$, $(1,2,0,3)$, and $(1,3,0,2)$.
The decomposition is the one checked by
`gap_eq_marked_star_sum` in the
[T85 marked-star code](MOC/ZhengPairedContacts.lean).

Use the [signed-weight minor identity](MOC/Weights.lean) of
[Merikoski and Virtanen](https://doi.org/10.1016/0024-3795(89)90709-X).
For a fixed mixer $U$, each indicator $I\to J$ evaluates to
$M(I\to J)=|\det U_{I,J}|^2$. The determinant gap $L$ is
therefore (1) with all seven indicators replaced by their squared
minors. This applies to complex unitary mixers. All coefficients
except $-\beta$ are nonnegative for $\beta>0$ on the feasible
region. In particular
$$
                   L\ge -\beta\,M(B\to B^c).       \tag{2}
$$
For $\beta=0$ the same formula gives nonnegative gap. For
$\beta<0$ in the absence of any negative marked residual, use
the T85 nonnegative-residual certificate, rather than assuming
the six other coefficients in (1) are automatically nonnegative.

## Exact projective chart

In a strict witness the spectra are simple and no signed cross
pair coincides, by the established order-four cases for repeated
eigenvalues and vanishing pair sums. Use a common projective map
on the two signed spectra $a$ and $c=-b$ to write
$$
 c=(\infty,t,0,1),\qquad a=(x,y,z,w).
$$
Use homogeneous coordinates $(v,1)$ for a finite value $v$,
$(1,0)$ for infinity, and the matching bracket
$a_0 c_1-a_1 c_0$ for two homogeneous vectors. In the formulas below
replace the infinity bracket by $1$, rather than $-1$. This is
one common factor $-1$ for every matching product and its
signed-weight evaluation. Under any invertible two-by-two
projective map, the product of the determinants of the brackets is
scaled by its determinant to the fourth power, divided by the
product of all row and column normalizing factors. Every
normalizing factor is nonzero, including at the entry sent to
infinity. Signed-weight linearity therefore preserves the gap
and its height after changing $\eta$ by the inverse common
factor. Conversely, at any chart point that has simple, disjoint
spectra, a pole away from the two finite projective lists gives
ordinary finite spectra again. Compare
[the Lean finite-chart version](MOC/ProjectiveTransport.lean).

Set $\alpha=(w-1)/w,\ \gamma=(z-1)/z$, and $D=P_3-P_2$.
Here $D\ne0$: the two labels differ by one swap, and the
other bracket factors are nonzero. The products needed to compute
the chart are
$$
\begin{array}{lll}
P_1=w(y-t)(z-1), &P_2=y(z-t)(w-1), &P_3=y(z-1)(w-t),\\
P_6=(x-t)z(w-1), &P_{11}=(x-t)z(y-1),&
P_{12}=x(z-t)(w-1),\\
P_{20}=w(x-1)(y-t).&&
\end{array}
$$
With $\eta D=i\delta$, $\delta\ne0$ real, put
$$
r=\frac{P_{20}-P_1}{P_6-P_{12}},\qquad
k=\frac{P_{12}-P_2}{D},\qquad j=\frac{P_{12}-P_1}{D}.
$$
All three ratios are real by the contact equations. The factorization
$$
r=\frac{w(y-t)(x-z)}{t(w-1)(x-z)}
  =\frac{y-t}{t\alpha}
$$
makes $r\ne0$. The collision $P_1=P_6$ gives
$x=t(1+r\gamma)$, and the displayed definition of $r$ gives
$y=t(1+r\alpha)$. For $k>0$, use the disjoint-swap rectangle
through labels $2,3,12,13$. Its product relation is
$P_{13}P_2=P_3P_{12}$. Substituting
$\eta P_3=\eta P_2+i\delta$ and
$\eta P_{12}=\eta P_2+ik\delta$ gives
$\Gamma_{13}=Hk\delta^2/|\eta P_2|^2$.
Since $H>0$, $k\ge0$; the one-swap difference
$P_{12}-P_2\ne0$ gives strictness.

The chart equations can be recovered without solving a polynomial
system. [`cleared_normalization`](MOC/ZhengT55Chart.lean) checks the
complex algebra below after multiplying the matching products by
`(1−α)(1−γ)`; it does not use projected examples or numeric tests. Put
$$
 A_0=k+(k-1)r\alpha,\quad
 m=j-k+1,\quad N=A_0-j(1+r\alpha),\quad
 Q=(k-1)r\alpha^2+[2k-(k-1)r]\alpha+k(1/r-1).
$$
Substitute $x=t(1+r\gamma)$, $y=t(1+r\alpha)$,
$z=(1-\gamma)^{-1}$, and $w=(1-\alpha)^{-1}$.
First use $D=y(1-t)zw(\gamma-\alpha)$ to obtain
$$
 k=\frac{r\alpha(1-t+t\gamma)}{(1+r\alpha)(1-t)},\quad
 \frac{P_{12}}D=\frac{k(1+r\gamma)}{r(\gamma-\alpha)},\quad
 \frac{P_1}D=\frac{r\alpha\gamma}{(1+r\alpha)(1-t)(\gamma-\alpha)}.
$$
The first equality gives $t/(1-t)=A_0/(r\alpha\gamma)$.
Insert this in the last equality and subtract it from the middle
one to get $N(\gamma-\alpha)=-Q$. Thus
$$
 \gamma=\alpha-Q/N,\qquad t=A_0/(A_0+r\alpha\gamma).    \tag{3}
$$
The nonvanishing of $N$ in the branch used below follows from
$m>0$ and $\operatorname{Im}\alpha\ne0$.
For the converse, start with (3), define $x,y,z,w$ as above, and
reverse these equations wherever the spectra are simple and
disjoint. The seven contact differences from $P_1$, in label
order $1,2,3,6,11,12,20$ and divided by $D$, are
$$
                 0,\ j-k,\ j-k+1,\ 0,\ -rm,\ j,\ -rj.   \tag{4}
$$
For label 11 factor
$(P_{11}-P_6)/(P_1-P_3)=z(x-t)/(t(z-1))=r$.
The other values follow from $D,k,j,r$.
The normalized projected gaps in (4) vanish for every chart point.

## Sign constraints and recoverable boundary formulas

Write $R_i=(P_i-P_1)/D$. Then
$\Gamma_i=\delta\operatorname{Im}R_i$ and
$H=-\delta\operatorname{Im}(P_1/D)$.
The following exact identities suffice for the signs and limits:
$$
 R_8=-jr\alpha-k,\qquad
 R_4=-\frac{jr\alpha+k}{A_0},\qquad
 R_7-R_{10}=jr+\frac{k}{\alpha},\qquad
 R_{21}=-jr+kr-r-1+\frac{r+1}{1+r\alpha}.              \tag{5}
$$
They can be reproduced by expanding the three finite factors from
the row-to-column tuple, canceling $D=y(1-t)zw(\gamma-\alpha)$,
and substituting $t/(1-t)=A_0/(r\alpha\gamma)$ and
$j=P_{12}/D-P_1/D$. For $R_{21}$, the tuple is
$(3,1,2,0)$; canceling the common factor $y-t$ first gives
the indicated single simple fraction. None of these reductions
requires dividing by $N$ or $k-1$. One may clear the
nonzero denominators to check them directly.

Consequently
$$
 \beta=\frac{k\delta\operatorname{Im}\alpha}{|\alpha|^2},
 \qquad
 \Gamma_{21}=-\frac{r(r+1)\delta\operatorname{Im}\alpha}
 {|1+r\alpha|^2}.
$$
On $\beta>0$, $\alpha$ is nonreal and
$\delta\operatorname{Im}\alpha>0$.
Since $\Gamma_{21}\ge0,\ r\ne0$, we have $-1\le r<0$.
Let $s=-r>0$, and put $\zeta=1/\alpha$. The conditions
$\Gamma_9=\Gamma_8-\beta\ge0$ and
$\Gamma_{18}=\Gamma_4-\beta\ge0$ read
$$
 d_9=sj-k|\zeta|^2\ge0,\qquad
 d_{18}=sm-|k\zeta-(k-1)s|^2\ge0.                    \tag{6}
$$
For the second equality, the imaginary part of $R_4$ is
$-k r m\operatorname{Im}\alpha/|A_0|^2$, by multiplying
numerator and denominator in (5) by the conjugate denominator.
Here $A_0\ne0$, since $k>0$ and $\alpha$ is nonreal.
Thus $j,m>0$, and $N=(k-j)-mr\alpha\ne0$.
Also
$$
 d_{18}-d_9=-s(k-1)\bigl(k|\zeta-s|^2/s+1-s\bigr).
$$
The polynomial identity is checked by
[`disk_defect_difference`](MOC/ZhengT55Chart.lean). The bracket
is strictly positive. Thus at a feasible boundary
$\Gamma_9=0$ implies $k\le1$, and $\Gamma_{18}=0$ implies
$k\ge1$. When $k=1$ both designate the same circle in (6).
The arm $\Gamma_{21}$ is not an exit along
the curve: if $s=1$ it vanishes identically, while if
$0<s<1$ it is strictly positive throughout $\beta>0$.

## Reduction to the five boundaries

Suppose the positive-height overlap has a strict witness.
Fix its $U,r,k,j,\delta$, and vary only $\alpha$ in (3).
For each regular point, choose $\eta=i\delta/D$. It need not
have unit modulus; multiplying it by a positive real number
does not change feasibility or the sign of the determinant gap.
By (4) the seven projected contacts persist. The T85 block-defect identities and `single_block_defect_rectangle`
apply to arbitrary spectra satisfying the contact equalities: their
proof uses only matching-product factorizations and projection. The
marked-star algebra therefore gives (1) even before any gap signs
are imposed. The same factorizations hold in the homogeneous
chart by the projective common-factor argument above.
The normalized $R_i$, $P_1/D$, and the signed-weight
combination defining $L$ are rational functions of $\alpha$;
their imaginary parts times $\delta$ are harmonic off their poles.

Discard the finitely many poles, points with coincident spectra
or a zero bracket, and zeros of $D$ or of a chart denominator.
These are finite: each is given by a rational numerator or
denominator not identically zero, since the initial point is
regular. Work in the half-plane
$\delta\operatorname{Im}\alpha>0$. In (1), when $\beta>0$,
feasibility is equivalent to nonnegativity of the six arm gaps
$$
           \Gamma_0,\ \Gamma_7,\ \Gamma_9,\
           \Gamma_{18},\ \Gamma_{21},\ \Gamma_{23}.       \tag{7}
$$
Necessity is immediate. Sufficiency follows from the checked
marked-star crossing formula: on the marked row and column these
are the gaps, together with the persistent zero arm; off both,
the gaps are the sum of the two arms and $\beta+dE$; on the
block group only $d=\Gamma_{23}+\beta$ occurs. Identically zero
functions in (7) impose no open-domain restriction.

Assume the five boundary comparisons hold at every regular point
of their respective boundaries. If the initial point lies on
one of those boundaries the desired contradiction is immediate.
Otherwise take the connected open component containing it on
which $H>0,\beta>0$, all nonidentically zero gaps in (7) are
positive, and $L<0$. This definition does not cut out the
$s=1$ branch, because $\Gamma_{21}$ is then identically zero.
At any regular finite boundary point, the limiting value of $L$
is nonnegative: this follows from $L=0$, a boundary comparison
for (7), the already established zero-height comparison, or (1)
at $\beta=0$. A real point without a pole has $L=0$, since the
normalized rational functions have real coefficients.
Only finitely many irregular finite boundary points remain.

For clarity, no continuity claim at a pole is needed. By (2)
and (6), $L$ is bounded below on the component, since
$|\alpha|\ge\sqrt{k/(sj)}$ and
$0<\beta\le k|\delta|/|\alpha|$. This last bound tends to zero
at infinity. Fix $\epsilon>0$ and choose a truncation circle
of radius $R$ containing the initial point on which
$L\ge-\epsilon$ inside the component. For every irregular
point $p$ in the closed disk, add the harmonic barrier
$\lambda\log(C/|\alpha-p|)$ to $L+\epsilon$, with
$C>2R$ and $\lambda>0$. These barriers are nonnegative in
the disk and diverge at their own points. Excise disjoint
sufficiently small closed disks at the irregular points. The
bounded-below estimate makes $L+\epsilon$ plus the barriers
nonnegative on the new circular boundaries. It is also
nonnegative at the regular boundary and the truncation circle.
The harmonic minimum principle on the remaining bounded open
component gives the same inequality at the initial point.
Let $\lambda$ tend to zero with $R$ fixed, then
$\epsilon$ tend to zero. This contradicts $L<0$.
Thus the five boundary comparisons for
$\Gamma_0,\Gamma_7,\Gamma_9,\Gamma_{18},\Gamma_{23}$ close the
whole oriented positive-height overlap. They cover $s=1$ without
a separate $\Gamma_{21}$ comparison.

# The T15 support comparison

This closes $T_{15}$ of [Zheng, Appendix E and Appendix G](https://doi.org/10.13140/RG.2.2.36790.25923)
without the facet classification or any enumeration of spectra or
mixers. The needed paired-cofactor inequality is checked in
[ZhengT15Gram.lean](MOC/ZhengT15Gram.lean); the chart, marker
identification and exterior-square reduction below are paper proofs.

Use zero-based row-to-column assignments and signed second
spectrum $C=-b$. Relabel by
$\sigma\mapsto b_0\circ\sigma\circ c_0$ with $b_0=(0,1,3,2)$
and $c_0=(0,2,1,3)$ in one-line notation. The six contacts of T15,
$1,2,3,4,6,7$, become $0,1,2,3,8,10$.
Write $P_i$ for their matching products and $\Gamma_i$ for the
upper-support gaps with pivot $P_0$. Repeated spectra or a zero
cross factor already have order-four common-weight certificates
([repeated spectrum](MOC/TwoExceptions.lean),
[zero cross pair](MOC/FourCoincidence.lean)), so assume all eight
spectral points are distinct.

## The exact chart

The quotient $(P_3-P_2)/(P_1-P_0)$ is real. Cancelling the
same row-swap factor gives the cross ratio of $A_1,C_1,C_2,C_3$.
Normalize to $A_1=\infty,\ C_2=0,\ C_1=1,\ C_3=t$, where
$t\in\mathbb R\setminus\{0,1\}$. Use the infinity incidence factor
$1$. This convention scales every matching product and the
signed-weight determinant by the same nonzero factor, by the
homogeneous bracket identity; change the support direction
inversely. The [finite-chart version](MOC/ProjectiveTransport.lean)
of this covariance is checked in Lean.

Write $A_0=x,A_2=z,A_3=a,C_0=w$ and
$$
 D=P_0-P_2=(x-w)(a-t),\qquad
 l=(P_0-P_1)/D=t(a-z)/(a-t),\qquad P_0/D=z .
$$
Here $D\ne0$, $l\in\mathbb R$, and $l\ne t$, since otherwise
$z=t$. Thus $a=t(l-z)/(l-t)$. Define the real contact ratio
$m=(P_2-P_8)/D$. The one-swap difference defining it is nonzero.
Directly,
$$
 m=\frac{(w-1)(x-z)}{x-w},\qquad
 w=\frac{(m+1)x-z}{x+m-z}.
$$
The denominator in the formula for $w$ cannot vanish. Its
vanishing would give $x=z-m$ and $m(z-m-1)=0$, hence $x=1$,
a prohibited cross factor. Also $z\ne m+1$, since this gives
$w=z$. For the last contact, $P_{10}=(x-1)(z-w)a$; substitution
gives $P_{10}/D=(z-m-1)a/(a-t)$. Therefore
$$
 (P_0-P_{10})/D=\frac{(t-l-m-1)z+(m+1)l}{t-z}\in\mathbb R .
$$
The real fractional-linear numerator and denominator here have
determinant $(t-l)(t-m-1)$, up to sign. Thus either $z$ is real,
or $m=t-1$.

If $z$ is real, all six spectators $A_1,A_2,A_3,C_1,C_2,C_3$
are real projective points. Move the point at infinity to a
finite point by a real projective map with no pole on either
spectrum, transporting the support direction as before.
The height is zero, since $\eta D$ is purely imaginary and
$P_0/D=z$. In the finite chart the product of the other three
spectator differences at $P_0$ is nonzero real, so the
projected value of the outlier-pair factor itself is zero.
The [checked real-spectator support theorem](MOC/ZhengStabilizerSupport.lean)
now gives the comparison, with no signs required of the real
spectators.

Henceforth take $m=t-1$, so $w=(t x-z)/(x+t-1-z)$.
Define $R_i=(P_0-P_i)/D$. We can use
$\Gamma_i=\operatorname{Im}R_i$ without loss: beginning with
$\eta D=i\delta$, one has $\Gamma_i=-\delta\operatorname{Im}R_i$;
conjugate the chart and direction if necessary, then rescale by
a positive number. This does not change the support problem.
Set $s=1-t$ and $u_0=1+(t-1)l/t$. The ratios needed below are
$$
\begin{array}{ll}
R_4=\dfrac{l-(l-t+1)z}{t-z},&
R_6=s\,\dfrac{z}{x-z},\\[2pt]
R_7=l+s\,\dfrac{z-l}{x-z},&
R_9=t+s(l/t)\,\dfrac{z-t}{x-z},\\[2pt]
R_{11}=s(l/t)\,\dfrac{z}{x-z},&
R_{14}=t+\dfrac{t-z}{x-1},\\[2pt]
R_{16}=u_0-\dfrac{z-u_0}{x-1},&
R_{20}=l-s\,\dfrac{z-l}{x-1},\\[2pt]
R_{22}=u_0-s\,\dfrac{z-u_0}{x-1}.&
\end{array}                                                    \tag{1}
$$
To recover any entry, put $W=t x-z$ and $V=x+t-1-z$.
For a matching in which row 1 receives column 0, multiply the
other three factors by $V$. Otherwise use the ordinary finite
factors except at column 0, where a row value $h$ contributes
$Vh-W$. The row 1 factor is always $1$. The same scaling gives
$D=(x-1)(x-z)(a-t)$, since $Vx-W=(x-1)(x-z)$.
Subtract the numerator for the indicated label from that for 0,
and cancel this denominator before substituting
$a=t(l-z)/(l-t)$. This proves (1) by polynomial identities with
nonzero chart denominators, not by checking spectral examples.

In particular, with $\Delta=\Gamma_9-\Gamma_7$, (1) gives
$$
 \Delta=(l/t-1)\Gamma_6,\qquad
 \Gamma_{22}=(1-t)\Gamma_{16},\qquad
 \Gamma_{20}=\Gamma_{14}-t\Gamma_{16}.                         \tag{2}
$$

## A linear marker identity without classifying the cone

For two sets write $M(I\to J)$ for the permutation indicator
of $\sigma(I)=J$, and $S_{ij}=M(\{i\}\to\{j\})$. These symbols
also denote their evaluations as squared minors. Use the three
pair representatives $A=01,B=02,C_*=03$; a superscript $c$
means the complementary set. In this section $C_*$ is a set,
not the second spectrum.

The space of subset-image profiles has dimension at most 14.
In fact the singleton span has dimension at most $1+9$ by
its row and column sums. For two pairs $I,J$, the difference
$M(I\to J)-M(I\to J^c)$ is
$\sum_{i\in I,j\in J}S_{ij}-1$ by intersection size.
Their sum is a permutation-matrix entry for the induced
action on the three unordered pair partitions. The nine such
entries contribute at most four further dimensions modulo
constants, by their row and column sums. All actual matching
profiles belong to this span, by expanding the matching product
and grouping terms by the image subset. The real constant and
projected gaps belong to it too.

The six contact equations on this span are independent.
Restricting singleton indicators to row 0 fixed gives the span
of the $3\times3$ permutation matrices, of dimension 5 by
Birkhoff's theorem. The unique dependence on the six
permutation evaluations has the alternating signs: every
assignment then occurs exactly once in each parity. Thus the
four evaluations at $0,1,2,3$ are independent on singletons.
The two profiles $S_{01}$ and $M(A\to\{1,2\})$ vanish on
these four contacts and distinguish the other two, $8,10$.
The remaining profile subspace therefore has dimension at most 8.

The following ten markers vanish at all six contacts:
$$
 S_{02},\ S_{03},\ S_{10},\ S_{30},\
 M(A\to C_*),\ M(A\to A^c),\
 M(B\to C_*^c),\ M(B\to B^c),\ M(B\to A^c),\
 M(C_*\to A^c).
$$
In this order denote their coefficients by $c_0,\dots,c_9$
in this calculation only. Their evaluations at labels
$4,6,7,9,12,13,16,18$ are respectively
$$
 c_4,\ c_2+c_6,\ c_2+c_7,\ c_3+c_7,\
 c_0+c_2+c_6+c_9,\ c_0+c_2+c_8,\ c_0+c_5,\
 c_1+c_2+c_4+c_7+c_9 .
$$
These eight equations can be solved sequentially, with
$c_2,c_9$ free. Thus the markers span the eight-dimensional
subspace without using a list of facets. In terms of two
free scalars $d=c_2$, $v=c_9$, their coefficients for the actual
gap profile in this order are
$$
\begin{split}
(&\Gamma_{14}-v,\ \Gamma_{20}-v,\ d,\ d+\Delta,\ \Gamma_4,\
  \Gamma_{16}-\Gamma_{14}+v,\\
 &\Gamma_6-d,\ \Gamma_7-d,\ \Gamma_{13}-\Gamma_{14}+v-d,\ v).
\end{split}                                                     \tag{3}
$$
Indeed the marker values at labels 14 and 20 are $c_0+c_9$ and
$c_1+c_9$ respectively, so the formula recovers the eight previous
evaluations. Four additional marker evaluations give
$$
\begin{aligned}
\Gamma_{11}&=\Gamma_6+\Delta,&
\Gamma_{15}&=\Gamma_{13}+\Delta,\\
\Gamma_{19}&=\Gamma_4+\Gamma_{13}+\Gamma_{20}-\Gamma_{14},&
\Gamma_{21}&=\Gamma_{15}+\Gamma_{20}-\Gamma_{14}.
\end{aligned}                                                    \tag{4}
$$
Also $\Gamma_{22}=\Gamma_{16}+\Gamma_{20}-\Gamma_{14}$ from
its two marker incidences, in agreement with (2).
All these evaluations concern the specified local markers;
no statement about the remaining permutation labels is needed
to validate (3).

Set $E=\Gamma_4-\Gamma_{19}$. If $E\le0$, choose
$$
 d=\max(0,-\Delta),\qquad
 v=\max(0,\Gamma_{14}-\Gamma_{16},d+\Gamma_{14}-\Gamma_{13}).
$$
Then $d\le\min(\Gamma_6,\Gamma_7)$ by the gaps at 6, 7, 9, 11.
Also $d\le\Gamma_{13}$ by the gaps at 13 and 15. This gives
$v\le\Gamma_{14}$. For the remaining upper bound
$v\le\Gamma_{20}$, its middle argument is bounded by
$\Gamma_{20}$ via $\Gamma_{22}\ge0$. Its third argument is
bounded by $\Gamma_{20}$ via both
$\Gamma_{13}+\Gamma_{20}\ge\Gamma_{14}$, from $E\le0$, and
$\Gamma_{15}+\Gamma_{20}\ge\Gamma_{14}$, from $\Gamma_{21}\ge0$.
Thus all coefficients in (3) are nonnegative and the result
is a positive squared-minor comparison for any unitary mixer.

## The signed branch

Suppose $E>0$. Equations (2) and (4) give
$$
 \Gamma_{21}=\Delta-E,\qquad
 \Gamma_{13}=t\Gamma_{16}-E,\qquad
 \Delta=(l/t-1)\Gamma_6,\qquad
 \Gamma_{22}=(1-t)\Gamma_{16}.
$$
Since the gaps are nonnegative, $0<t<1$ and $l>t$.
Equation (1) gives
$\Gamma_4=(1-t)(l-t)\operatorname{Im}z/|t-z|^2$.
Since $\Gamma_4\ge E>0$, $\operatorname{Im}z>0$.
The two gaps $\Gamma_{7},\Gamma_{20}$ place
$y=(x-1)/(z-l)$ in a strip:
$$
 0\le\operatorname{Im} y\le
       \operatorname{Im}[(z-1)/(z-l)]
       =\frac{(1-l)\operatorname{Im}z}{|z-l|^2}.
$$
Indeed their nonnegativity amounts respectively to
$\operatorname{Im}(1/(y-(z-1)/(z-l)))\ge0$ and
$\operatorname{Im}(1/y)\le0$. The denominators are nonzero
because $x\ne z,1$. Consequently $l\le1$, and hence
$$
     \Gamma_6\Gamma_{22}
       \ \ge\ \frac{t}{l-t} E \cdot\frac{1-t}{t}E
       \ \ge\ E^2 .                                           \tag{5}
$$

Take $d=0$ and $v=\Gamma_{14}-\Gamma_{13}$ in (3).
Write
$$
 h=-S_{03}+S_{30}+M(A\to C_*)+M(A\to A^c)+M(C_*\to A^c).
$$
The objective is $E h$ plus the seven nonnegative terms
$$
 \Gamma_{13}S_{02}+(\Delta-E)S_{30}+\Gamma_{19}M(A\to C_*)
 +\Gamma_{22}M(A\to A^c)+\Gamma_{20}M(C_*\to A^c)
 +\Gamma_6 M(B\to C_*^c)+\Gamma_7 M(B\to B^c).
$$
The image of row 0 belongs to $A^c$ iff exactly one of the
pairs containing row 0 maps onto $A^c$. Thus
$S_{02}+S_{03}=M(A\to A^c)+M(B\to A^c)+M(C_*\to A^c)$, and
$$
             h=S_{02}+S_{30}+M(A\to C_*)-M(B\to A^c).          \tag{6}
$$

## The paired-cofactor inequality

By the [checked realification theorem](MOC/FourMinorTransport.lean),
it suffices to evaluate on real orthogonal mixers. Multiplying a
row by $-1$ makes orientation positive and leaves all squared
minors unchanged. Write $L,R\in SO(3)$ for its two actions on
the Hodge summands of $\bigwedge^2\mathbb R^4$, indexed by
$A,B,C_*$. In the bases $(e_I\pm *e_I)/\sqrt2$, the minor
$M(I\to J)$ is $(L_{IJ}+R_{IJ})^2/4$, and going to one
complement changes the relative sign. A possible orientation
sign from $*e_I$ disappears after squaring.

For fixed $i,j$, sum the nine two-minors whose row set contains
$i$ and column set contains $j$. By Cauchy--Binet and the row
and column norms the sum is $1+2S_{ij}$. Equivalently, each
permutation contributes 3 if $\sigma(i)=j$ and 1 otherwise;
the [signed subset-image law](MOC/Weights.lean) of
[Merikoski and Virtanen](https://doi.org/10.1016/0024-3795(89)90709-X)
gives the same evaluation. Put $\rho_i(I)=1$ if $i\in I$
and $-1$ otherwise, for $I=A,B,C_*$. Expansion then gives
$4S_{ij}=1+\sum_{I,J}\rho_i(I)\rho_j(J)L_{IJ}R_{IJ}$.

Let
$$
 X=\begin{pmatrix}u&a\\ c&p\end{pmatrix}
      =L_{\{A,B\},\{A,C_*\}},\qquad
 Y=\begin{pmatrix}v&b\\ d&q\end{pmatrix}
      =R_{\{A,B\},\{A,C_*\}}.
$$
Then $L_{C_*B}=-\det X$, $R_{C_*B}=-\det Y$ by cofactors.
The squared Frobenius norm of a two-by-two corner of a
three-dimensional rotation equals one plus its determinant
squared: by the row and column norms it is $1+$ the square
of the omitted entry, and the omitted entry is the signed
cofactor. Using this in (6) gives
$$
 4h=(u-v)^2+(p-q)^2+2(a^2+b^2)-(\det X-\det Y)^2.
$$
For example the two singleton terms contribute
$2+2L_{C_*B}R_{C_*B}-
2(L_{AA}R_{AA}+L_{AC_*}R_{AC_*}+L_{BA}R_{BA}+L_{BC_*}R_{BC_*})$;
substituting the two minors in (6) yields the displayed identity.
The two other markers needed are
$4M(A\to A^c)=(u-v)^2$ and $4M(B\to C_*^c)=(p-q)^2$.

The determinant difference is
$\bar p(u-v)+\bar u(p-q)-ac+bd$, where bars indicate
averages of the two entries. Let
$m=\max(|\bar p|,|\bar u|)$ and $n^2=(c^2+d^2)/2$.
The squared norms of row $B$ and column $A$ give
$m^2+n^2\le1$. Cauchy--Schwarz gives
$$
 |\det X-\det Y|\le m(|u-v|+|p-q|)+n\sqrt{2(a^2+b^2)}.
$$
One more Cauchy--Schwarz shows
$4h\ge-2|u-v||p-q|$. By (5) and Young's inequality,
$E h+\Gamma_{22}M(A\to A^c)+\Gamma_6M(B\to C_*^c)\ge0$.
The remaining terms are all nonnegative. This completes both
branches, for orthogonal and therefore for all unitary mixers.

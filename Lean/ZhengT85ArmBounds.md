# Five positive-height boundaries of the T55 overlap

Use the canonical T55+20 numbering in [the continuation proof](ZhengT55PositiveOverlap.md)
and the T85 gap coordinates of [Zheng, Section 5 and Appendix D](https://doi.org/10.13140/RG.2.2.36790.25923).
Left composition with $(23)$ on zero-based values takes canonical
labels $0,7,9,18,23$ to T85 labels $1,6,11,12,17$.
The seven starting contacts go to T85 plus arm 4. Thus the boundary
conditions, in that order, are
$\alpha_7=0,\alpha_4=0,\alpha_3=0,\alpha_6=0,\alpha_1=0$,
each together with $\alpha_5=0$. All ordinary ray coefficients
are nonnegative and the mixed coefficient is positive.
Normalize the latter to one.
The computations below use real oriented orthogonal mixers. Changing
one row sign preserves all squared minors, so they also cover real
orthogonal mixers of determinant minus one. The checked
[two-table decomposition](MOC/FourMinorTransport.lean) then extends
each boundary inequality to all complex unitaries, since the signed
profile is a linear combination of squared minors.

The Hessian determinant in each chart is computed on the cubic by
the exact polynomial Schur calculation in the
[center-and-split note](ZhengT40PositiveOverlap.md).
Actual projected points belong to the secant cone, so the determinant
is zero by the geometric rank bound
([Howard–Millson–Snowden–Vakil, DOI 10.1112/plms/pds016](https://doi.org/10.1112/plms/pds016);
[Zheng, Corollary C.5](https://doi.org/10.13140/RG.2.2.36790.25923)).
The resulting scalar equations, not the Hessian evaluation or the
geometric input, are the hypotheses of the Lean comparison theorems.

## Three product comparisons

Use the same rotations and minor normalization as in the
[center-and-split proof](ZhengT40PositiveOverlap.md#weighted-comparison-on-rotations).
Write $A=\alpha_4$, $B=\alpha_7$, $T=\alpha_1$. The mixed ray and these
three ordinary terms have signed evaluation, multiplied by four,
\[
 (1+T)d^2+2(p_0^2+q_0^2)+(1+A)a^2+B c^2-b^2,
\]
where $d=\Delta_{00}$, $a=\Delta_{12}$, $b=\Delta_{21}$,
$c=L_{21}+R_{21}$, $p_0=L_{10}$, and $q_0=R_{10}$.
Indeed the mixed-ray identity is
$f_{35}+f_{11}=f_1+f_5+f_{12}+f_{33}$; $f_{45}$ is
$02\to03$, the complementary event to $f_{11}$.
All the other terms are squared minors with nonnegative coefficients
([Merikoski and Virtanen, DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X)).

If $AT\ge1$, the weighted cofactor comparison below proves the
desired nonnegativity. Conjugated transposition exchanges $A,B$ while
fixing $T$ and the mixed coefficient, so $BT\ge1$ also suffices.

For $AB\ge1$, use the averages $w,B_1,\ell$, and the scalars $B_0,e$,
from the [rotation proof](ZhengT40PositiveOverlap.md#weighted-comparison-on-rotations).
The forward cofactor relation takes the form
\[
 b-w B_1 a=-wd+L_{02}p_0-R_{02}q_0-ea .
\]
The squared dual norm for inputs $(d,\sqrt2p_0,\sqrt2q_0,a)$
is at most one by $e^2\le B_0$.
Consequently $(b-w B_1a)^2\le d^2+2(p_0^2+q_0^2)+a^2$.
Expand the square and use $|w|\le1$, $|b|\le2$, and $2B_1=c$.
The loss above this baseline is at most $2|ac|$, which is at most
$Aa^2+Bc^2$ when $AB\ge1$. Lean checks the two cofactor comparisons
in [ZhengT40RotationBound.lean](MOC/ZhengT40RotationBound.lean).

More generally, any of $A(B+T),B(A+T),T(A+B)$ at least one suffices.
For example, if $A(B+T)\ge1$, assign fractions $B/(B+T)$ and $T/(B+T)$
of both the mixed ray and the $A$ term to the $AB$ and $AT$ comparisons,
respectively. In each part the relevant product is at least the square
of the mixed coefficient. If one fraction is zero, omit that part.
The other two vertex sums follow by the same allocation of the shared
coefficient. This argument uses only linearity of the objective.

## The adjacent T55 boundary with a split and a vanishing row arm

Take $\alpha_7=\alpha_5=0$, but do not assume the center is active.
As before normalize $\beta=1$ and use lower-projecting height $h$.
Write $T=\alpha_1$, $X=\alpha_2$, $Y=\alpha_3+\alpha_6$,
$R=\alpha_3\alpha_6$, $A=\alpha_4$, and $B=Y+1+R$.
This is the overlap with T55 arm 4 and split 1. The real lift is
$$
(-A,\ A+X+1,\ -1,\ -X,\ 0,\ Y+1,\ T-X-Y-1,\ -\alpha_3,\ A,\
 X+\alpha_3-T,\ -\alpha_3-1,\ -X-A-1,\ A+1,\ T+1+h).
$$
The height coefficient is $Q=A(X-T)-(X+1)(Y+1)$, and
$C_0=-(X+1)B<0$. Thus $Q\ne0$ on the cubic.
The same four Schur pivots and the same determinant recurrence as
above give $Q^2\det J=-4F_b^2$ on $h=-C_0/Q$, with
$$
F_b=(X+1)B^2(T+1)
   \{(T-X)A^2+(X+1)(T-1)A-(X+1)\}.
$$
In particular the bracket is zero for actual spectral data by the
secant rank bound. It is also equal to
$(AT-1)(A+X+1)-X A(A+1)$. All the coefficients $A,X,T$
are nonnegative, so $AT\ge1$. This argument is independent of
other contacts.

In the self-dual and anti-self-dual components $L,R\in SO(3)$ of the
compound mixer, use target rows and source columns and the partition
order $01\mid23$, $02\mid13$, $03\mid12$.
Write $a=\Delta_{12}$, $b=\Delta_{21}$, $d=\Delta_{00}$, where
$\Delta=L-R$, and put $w=(L_{12}+R_{12})/2$, $\ell=(L_{00}+R_{00})/2$,
$p=L_{10}$, $q=R_{10}$, $z=L_{02}$, $Z=R_{02}$.
The forward cofactor identity is
$$
b=-w d-\ell a+zp-Zq.
$$
The target Gram bound comes from Cauchy--Schwarz with weighted
coordinates $(\sqrt{1+T}\,d,\sqrt{1+A}\,a,\sqrt2\,p,\sqrt2\,q)$.
In fact the squared dual norm is
$$
\frac{w^2}{1+T}+\frac{\ell^2}{1+A}+\frac{z^2+Z^2}{2}\le1.
$$
Each of $w^2,\ell^2$ separately is at most
$1-(z^2+Z^2)/2$, by the two column-2 and the two row-0 norm identities,
respectively. Also $1/(1+T)+1/(1+A)\le1$ is exactly $AT\ge1$.
Therefore $b^2\le(1+T)d^2+(1+A)a^2+2(p^2+q^2)$.
Here $T$ contributes the ordinary minor $01\to23$ and $A$ the ordinary
minor $03\to13$. The remaining ordinary terms are nonnegative.
This proves the actual support inequality on this positive boundary.

## The $\Gamma_7$ boundary

Apply the conjugated transpose $\sigma\mapsto(02)(13)\sigma^{-1}(02)(13)$.
The raw conditions $\alpha_4=\alpha_5=0$ become
$\alpha_7=\alpha_3=0$. Set
\[
p=\alpha_2,\quad q=\alpha_5,\quad Y=\alpha_6,\quad V=Y+1,\quad
A=\alpha_4,\quad T=\alpha_1,\quad X=p+q,\quad P=pq,\quad
K=V(P+X+1),\quad \tau=AT.
\]
The cubic has $C_0=PA-K$ and $Q=A(X-T)-(X+1)V$.
On its zero locus with $Q\ne0$ the exact secant determinant is
\[
Q^2\det J=-4(T+1)^2 S^2,\qquad
S=ZA^2+AK[(X+1)V+P(3V-2)+\tau(P-V)]+K^2(1-\tau),
\]
where $Z=X(X+1)V^2-P(X+V+1)V-P^2(3V-1)$.
The lift is the T85 lift with $\alpha_7=\alpha_3=0$ and $\beta=1$.
The successive Schur pivot triples (row, column, value in the
current matrix) are $(3,8,1),(7,3,1),(5,10,1),(9,5,1),(1,7,-1),(6,1,-1)$.
The signed product is $-1$. Apply the same height-coefficient recurrence
to the resulting eight-by-eight matrix and then set $h=-C_0/Q$.

Suppose $\tau<1$, because otherwise the defect comparison applies.
If $Q=C_0=0$, then $P>0$, $A=K/P$ and
$\tau=V[X(X+1)/P-1]>1$ by $X^2\ge4P$. Thus $Q\ne0$ and $S=0$.
The coefficient of $AK$ is
$V(X+1-\tau)+P(3V-2+\tau)>0$. Hence $S=0$ implies $A>0$,
$Z<0$ and $P>0$. For fixed $\tau$ the function $S/A$ then strictly
decreases on positive $A$.

Exchange $p,q$ if needed to take $p=\min(p,q)$, and set $A_*=1+1/p$.
At $\tau=0$, $S$ is the center-branch polynomial with $r=0,s=Y$.
Its positive root exceeds $1+1/p+1/q$ by the
[center threshold](ZhengT40PositiveOverlap.md), so $S(A_*,0)>0$.
At $\tau=1$, with $E=p(2p+1)(p+1)$, the coefficients of
$pS(A_*,1)/A_*$ in decreasing powers of $Y$ are
\[
\begin{aligned}
 &E+q^2(3p^3+4p^2+2p+1)+q(4p^3+6p^2+3p+1),\\
 &2E+q^2(2p^3+3p^2+3p+2)+q(6p^3+9p^2+5p+2),\\
 &E+q^2(p+1)+q(2p^3+3p^2+2p+1).
\end{aligned}
\]
They are strictly positive. By affinity in $\tau$,
$S(A_*,\tau)>0$; strict decrease of $S/A$ gives $A>A_*$.
This is precisely the weighted rotation threshold. The extra ordinary
$\alpha_1$ term is nonnegative. Lean checks the endpoint identity,
interpolation and sign conclusion in
[ZhengT40Threshold.lean](MOC/ZhengT40Threshold.lean).

## Both crossed T55 arms

In the T85 numbering of [Zheng, Section 5 and Appendix A](https://doi.org/10.13140/RG.2.2.36790.25923),
these are $\alpha_5=\alpha_3=0$ or $\alpha_5=\alpha_6=0$. Normalize
$\beta=1$ and put $(p,Y,A,B,T)=(\alpha_2,\alpha_3+\alpha_6,\alpha_4,\alpha_7,\alpha_1)$.
All five scalars are nonnegative. In the cubic $C=C_0+hQ$,
\[
-C_0=(p+1)(Y+1)+TAB>0,\qquad
Q=(A-Y)(p-B)-(p+Y+1)-T(A+B).
\]
Thus $Q\ne0$ on the cubic. Let $J$ be the Hessian at the normalized lift,
with the height argument set to $-C_0/Q$. Both charts give
\[
Q^2\det J=-4(T+1)^2\,G^2,\qquad G=\sum_{0\le i,j\le2} g_{ij}p^iY^j.
\]
Use $U=AB$, $V=1-AT-BT$, and $\Theta=U+AT+BT-1$.
The coefficient formulas are:
\[
\begin{aligned}
g_{00}&=-(A+1)(B+1)(1-U-AT-BT+2UT),\\
g_{10}/(B+1)&=-A^2(1-B)(1-T)-2A-2UT+2\Theta,\\
g_{20}/(B+1)&=-A^2(1-BT)-A-UT+\Theta,\\
g_{21}&=U-UT-2V-2(A^2+A+B)+(T-1)(A^2B+B^2(1-A)),\\
g_{11}&=(1-T)\bigl(U(U+A+B+1)-2(A^2+B^2)\bigr)-4V-4(A+B),\\
g_{22}&=-A^2-B^2-A-B-V+U-UT.
\end{aligned}
\]
The three unlisted $g_{ij}$ are obtained from $g_{ji}$ by interchanging
$A$ and $B$. For a symbolic derivation, in the Appendix A Hessian
substitute
\[
(-A-B,p+A+1,-1,-p,B,Y+B+1,T-p-Y-1,-r,A,-T+p+r,-r-B-1,-p-A-1,A+B+1,T+1+h).
\]
Use $r=0$ in the $\alpha_3=0$ chart and $r=Y$ in the $\alpha_6=0$
chart. Apply the Schur recurrence of the
[center-and-split calculation](ZhengT40PositiveOverlap.md#secant-condition-at-the-center-and-split-t40-overlap).
The pivots in the former case are $(6,12),(11,6),(1,9),(8,1)$;
in the latter they are $(6,12),(11,6),(9,10),(9,9)$.
Their values are $1,1,-1,-1$ in either case, and their signed product
is one. The height polynomial has degree at most three. Multiplying by
$Q^3$ after $h=-C_0/Q$, collecting first in $(p,Y)$, gives
$-4Q(T+1)^2(\sum g_{ij}p^iY^j)^2$. This is an identity of polynomials.
The geometric rank input is the same
[secant contraction, DOI 10.1112/plms/pds016](https://doi.org/10.1112/plms/pds016),
so an actual profile must have $G=0$.

Suppose all three vertex sums $A(B+T),B(A+T),T(A+B)$ are smaller
than one. Then $V>0$, $\Theta\le\min(AB,AT,BT)$, and $AB\le A+B$
because at least one of $A,B$ is at most one. The coefficients have
the following signs.

- $g_{00}<0$. If one of $A,B,T$ is at least $1/2$, call it $A$ by
  symmetry of the factor. That factor is
  $1-A(B+T)+BT(2A-1)>0$. If all three are smaller than $1/2$,
  the three pair products sum to less than $3/4$.
- $g_{20}\le0$ since $BT<1$ and $\Theta\le A\min(B,T)\le A$.
- $g_{10}\le0$. If $B,T\le1$, the first term is nonpositive and
  $\Theta\le A$. If $B>1$, then $T<1$, $AB<1$ and
  $A^2(B-1)(1-T)\le A(1-T)$, while $\Theta\le AT$.
  The case $T>1$ interchanges $B,T$.
- $g_{21}\le0$. Write $M=A^2B+B^2(1-A)$. For $T\le1$,
  $M\ge0$: if $A>1$, then $B<1/A$ and $A^2>B(A-1)$.
  For $T>1$, $(T-1)M\le T(A^2B+B^2)\le A^2+B$.
  In either case the upper bound is nonpositive by $U\le A+B$.
- $g_{11}\le0$. For $T\le1$ the first term is bounded above by
  $U(U+A+B+1)\le3(A+B)$, using $U<1$ and $U\le A+B$.
  For $T>1$ the same term is at most
  $2T(A^2+B^2)\le2(A+B)$.
- $g_{22}\le0$ follows from $U\le A^2+B^2$ and $V>0$.
  The swapped coefficients have the same signs.

Consequently $G<0$ for all $p,Y\ge0$, contradicting $G=0$.
At least one vertex sum is therefore at least one, and the weighted
rotation comparison above proves nonnegativity in both crossed-arm cases.

## The center boundary

The remaining boundary is $\alpha_1=\alpha_5=0$.
The [center-boundary calculation](ZhengT55CenterBoundary.md)
proves the exact spectral compensation needed there.

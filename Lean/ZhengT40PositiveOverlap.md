# Positive-height T40 overlaps in T85

The center-and-split cases in the eight-contact reduction of
[Zheng, Section 5](https://doi.org/10.13140/RG.2.2.36790.25923)
have nonnegative determinant gaps. This covers both T40 overlaps
needed by [the T85 dependency repair](ZhengT40AndT85Dependencies.md),
not every profile with the six standalone T40 contacts.

## Secant condition at the center-and-split T40 overlap

Use Zheng's bracket basis and lower projection convention
([§5.3 and Appendix C](https://doi.org/10.13140/RG.2.2.36790.25923)).
The contacts include the six T85 labels together with 17 and 1, so
$\alpha_1=\alpha_7=0$. Divide the profile by $\beta>0$ to set
$\beta=1$; the actual upper height is the negative of the final
argument of the lift. Put
$$
(p,q,r,s,A)=(\alpha_2,\alpha_5,\alpha_3,\alpha_6,\alpha_4),
\quad X=p+q,\quad Y=r+s,\quad P=pq,\quad R=rs,\quad B=Y+1+R,
\quad G=(X+1)B,\quad K=G+P(Y+1).
$$
The real lift is
$$
(-A,\ A+X+1,\ -1,\ -p,\ 0,\ Y+1,\ -X-Y-1,\ -r,\ A,\
 p+r,\ -r-1,\ -p-A-1,\ A+1,\ 1+h).
$$
For the cubic $C$ in Appendix A,
$$
C=C_0+hQ,\quad C_0=P(A-Y-1)-G,\qquad
Q=X(A-Y-1)-(Y+1).
$$
Let $J=\nabla^2 C$ evaluated at this lift. At $h=-C_0/Q$,
$$
Q^2\det J=-4F(A)^2
$$
where
$$
\begin{aligned}
F(A)&=A^2\{X(X+1)B^2-P(X+Y+2)B-P^2(4R+3Y+2)\}\\
 &\quad+A\,K\{G+P(4R+3Y+1)\}+K^2 .
\end{aligned}
$$
Here is one way to reproduce the symbolic determinant identity without
a matrix or spectrum search. Form the Hessian of the displayed cubic
before substitution. All subsequent indices are zero-based in the
current matrix. Successively use the pivots
$(6,12),(11,6),(9,10),(9,9)$, whose values are respectively
$1,1,-1,-1$. At each step with pivot $J_{ij}=v$, remove row $i$ and
column $j$ and replace the remaining $J_{ab}$ by
$J_{ab}-J_{aj}J_{ib}/v$. The four pivot signs multiply to $+1$,
so the resulting $10\times10$ determinant equals the starting one.
The resulting matrix has the form $M_0+hM_1$. Writing
$\det(M_0+hM_1)=D_0+h D_1+h^2D_2+h^3D_3$, the coefficients can be
formed by the ordinary multilinear determinant recurrence
$$
D_{i,\emptyset}(t)=1\quad\text{at the empty matrix},\qquad
D_{i,S}(t)=\sum_{j\in S}(-1)^{|\{j'\in S:j'<j\}|}
 (M_{0,ij}+tM_{1,ij})D_{i+1,S\setminus\{j\}}(t).
$$
Combining the four coefficients gives the exact polynomial identity
$$
Q^3D_0-C_0Q^2D_1+C_0^2QD_2-C_0^3D_3=-4QF(A)^2 .
$$
The expression on the left is symmetric separately in $(p,q)$ and
$(r,s)$; it simplifies using $p+q=X,pq=P,r+s=Y,rs=R$. These are
polynomial identities, with no testing on numerical spectra or mixers.
The Hessian expression is an algebraic calculation on paper, not yet
a Lean theorem.

For actual spectra, use the checked cubic polarization in
[FourMatchingPolarization.lean](MOC/FourMatchingPolarization.lean).
A rotated bracket lift $x=u+iv$ has zero cubic gradient. The
gradient is quadratic with real coefficients, so taking its imaginary
part gives $J(u)v=0$. If $v=0$ and $u\ne0$, homogeneity instead gives
$J(u)u=2\nabla C(u)=0$; if $u=0$, $J(u)$ itself is zero.
Thus $\det J=0$ by elementary polarization. The same source checks
$C(u)=0$. This uses only the determinant-zero consequence of the
stronger secant rank theorem in
[Zheng, Corollary C.5](https://doi.org/10.13140/RG.2.2.36790.25923)
and [Howard–Millson–Snowden–Vakil, DOI 10.1112/plms/pds016](https://doi.org/10.1112/plms/pds016).

All five ordinary coefficients are nonnegative. If $P=0$, then $C_0=-G<0$,
so $Q\ne0$ on the cubic and $F$ cannot vanish: its quadratic and linear
terms are nonnegative and $K^2>0$. Hence $P>0$. Since $P\le X^2/4$,
$$
A_C=Y+1+G/P>Y+1+(Y+1)/X=A_Q .
$$
Thus $C_0$ and $Q$ cannot both be zero. The exact identity
$$
P^2 F(A_C)=B K^2\bigl(X(X+1)B-P(Y+1)\bigr)>0
$$
now implies $A>A_C$: the constant and linear coefficients of $F$
are strictly positive. For $A>0$ to be a root, its quadratic
coefficient must be negative, in which case $F(A)/A$ is strictly
decreasing. In particular
$$
A>Y+1+\frac{(X+1)(Y+1+R)}{pq}
 > 1+\frac1p+\frac1q .
$$
This is the compensation input for the weighted orthogonal Gram
inequality. [ZhengT40Threshold.lean](MOC/ZhengT40Threshold.lean)
checks the sign argument, including the exclusions when a coefficient
vanishes or when $Q=0$.

For the other split, use $p\mapsto Dp^{-1}D$ on row-to-column
assignments, with $D=(02)(13)$. It fixes the T85 set and the marked
label 17, swaps 1 with 6 and swaps the pairs of ordinary arms
$4\leftrightarrow11$, $15\leftrightarrow12$. In mark-at-identity
coordinates this is conjugated transpose exchanging the pair
partitions $01\mid23$ and $02\mid13$ and fixing $03\mid12$.
Consequently it leaves the defect event and the mixed coefficient
unchanged while exchanging the two arms. The determinant value
transforms by swapping the spectra and relabeling and transposing the
mixer, so it is enough to bound the split-1 case.

## Weighted comparison on rotations

For $O\in SO(4)$, the exterior square preserves the self-dual and
anti-self-dual three-dimensional spaces. Its restrictions are rotations
$L,R$: they are orthogonal, and their determinants are $+1$ by
connectedness of $SO(4)$. In the two bases use
$(e_{01}\pm *e_{01},e_{02}\pm *e_{02},e_{03}\pm *e_{03})/\sqrt{2}$.
Each matrix entry of the exterior square is a two-minor of $O$.
An entry between the selected two-set representatives is
$(L_{ji}+R_{ji})/2$; replacing one set by its complement changes the
relative plus to a minus, up to an overall sign. The signed
permutation evaluation of an indicator $\mathbf1_{\sigma(I)=J}$ is
the squared two-minor
([Merikoski and Virtanen, DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X)).

In the split-1 orientation, the exact linear decomposition from
[the T40 gap chart](ZhengT40AndT85Dependencies.md) reads
$$
(1+s)M(01\to02)+(1+r)M(01\to13)+(1+A)M(03\to13)
+M(01\to23)+q M(02\to01)+p M(02\to23)-M(02\to12),
$$
where $M(I\to J)$ denotes a squared minor. In fact, in the T40 linear
chart one has
$(a,b,c,d,e,f,s_{\rm chart},t)=(1+s,q,1+A+q,s,p,1+r,0,1)$.
The mixed coefficient is one and the other nonzero coefficients are
$s,q,A,p,r$.

With $m=\min(p,q)$ and $\Delta_{ij}=L_{ij}-R_{ij}$, four times this
objective is at least
$$
\Delta_{00}^2+2(L_{10}^2+R_{10}^2)+(1+A)\Delta_{12}^2
 +2m(L_{01}^2+R_{01}^2)-\Delta_{21}^2 .
$$
For the potentially harmful term, the following holds for any
$L,R\in SO(3)$, any $m>0$, and any $T\ge 2+1/m$:
$$
\Delta_{21}^2\le
\Delta_{00}^2+2(L_{10}^2+R_{10}^2)+T\Delta_{12}^2+
2m(L_{01}^2+R_{01}^2).
$$
Here is the weighted Cauchy--Schwarz proof. [ZhengT40RotationBound.lean](MOC/ZhengT40RotationBound.lean)
checks the matrix cofactor inputs, the inequality, and the full signed
comparison conditional on the secant polynomial.

Use $d,a,b$ for the three differences at $00,12,21$ and
$\ell,w,B_1$ for the three averages. Write $v=L_{22}$, $v'=R_{22}$,
$j=L_{11}$, $j'=R_{11}$. The cofactor relation
$L_{12}L_{21}=-L_{00}+L_{11}L_{22}$ and its counterpart give
$$
w B_1=-\ell+e,\qquad
e=(jv+j'v')/2-ab/4 .
$$
Set $B_0=(v^2+v'^2)/2+a^2/4$. The column-2 norms give
$B_0=1-w^2-(L_{02}^2+R_{02}^2)/2$. Cauchy--Schwarz and the
column-1 norms give $e^2\le B_0$, since
$(j^2+j'^2)/2+b^2/4\le1$.

The cofactor rules for entries 21 and 12 give, for any real $\theta$,
$$
\begin{aligned}
(1-\theta\ell)b={}&(-w+\theta B_1)d+L_{02}L_{10}-R_{02}R_{10}\\
 &+(-\ell+\theta)a-\theta L_{20}L_{01}+\theta R_{20}R_{01}.
\end{aligned}
$$
Take the squared norm $N$ of the coefficient vector when the six
inputs are $d,\sqrt2L_{10},\sqrt2R_{10},\sqrt T a,
\sqrt{2m}L_{01},\sqrt{2m}R_{01}$. Then
$$
(1-\theta\ell)^2-N=B_0-\ell^2/T
 +2\theta[-(2-1/T)\ell+e]
 +\theta^2\!\left(\ell^2-B_1^2-1/T-\frac{L_{20}^2+R_{20}^2}{2m}\right).
$$
Take $\theta=-\ell/T$. Use $2\theta e\ge-B_0-\theta^2$,
$B_1^2\le1$, and $L_{20}^2,R_{20}^2\le1$.
The resulting lower bound is
$$
\frac{\ell^2}{T^2}(3T-4-1/T-1/m)\ge0.
$$
Since $1-\theta\ell=1+\ell^2/T>0$, applying Cauchy--Schwarz
and dividing by $(1-\theta\ell)^2$ proves the comparison.

The spectral threshold gives $A>1+1/p+1/q\ge1+1/m$. Thus
$T=1+A$ meets the bound and the displayed minor sum is nonnegative
for every real orthogonal mixer (row signs do not change squared
minors). The [order-four minor transport theorem](MOC/FourMinorTransport.lean)
expresses the whole squared-minor table of each complex unitary as a
convex mixture of two real orthogonal tables. It extends this
inequality to all complex unitary mixers. The Hessian kernel argument and symbolic determinant identity above
remain paper arguments, not kernel-checked. No numerical positivity test or finite mixer search
is used.


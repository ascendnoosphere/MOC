# Standalone T40: exact boundary comparisons

Use the six T40 contacts and normalized mixed-ray chart of
[ZhengT40AndT85Dependencies](ZhengT40AndT85Dependencies.md), from
[Zheng, DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923).
We take $a-d=1$, other mixed orientation by transposition. Put
$c=b+1+C$, $f=1+F$, $t=1+D$ and take $b,d,e,s,C,F,D\ge0$.
The additional possible contact conditions are
\[
 b=0,\ C=0,\ s=0,\ F=0,\ d=0,\ e=0,\ D=0.
\]
The $s=0$ chart is covered by the [T85 support proof](ZhengT85Independent.md).
Conjugation by $(01)(23)$ preserves the T40 contacts and exchanges
$b,e$ and $d,F$, leaving $C,D,s$ unchanged. In particular the mixed
coefficient stays one: $\Gamma_{20}-\Gamma_{11}=\Gamma_3-\Gamma_{12}$.
The proof below closes $b=0$ and $e=0$; it is not a proof of all T40.

The [boundary-budget note](ZhengT40BoundaryBudget.md) records the conditional budget at \(C=0\) and the symbolic mixed quaternion term. It does not close an additional boundary.

## The two side boundaries

By the conjugation it suffices to set $e=0$. Write
\[
W=bd+bs+b+ds+d+s+1,\qquad \lambda=CD.
\]
For the matching cubic $K=C_0+hQ$, substitution of the chart gives
$C_0=-(F+1)W<0$. On the cubic, $Q\ne0$. In the fourteen bracket
coordinates used in the [T40 secant argument](ZhengT40PositiveOverlap.md),
the chart at $e=0$ is
\[
(s-C,\ b+1+C,\ -1,\ 0,\ -s,\ d+F+1,\ D-b-d-F-1,\ -F,\ C-s,\
 F-D,\ -F-1,\ -1-C,\ 1+C,\ h+D+1).
\]
Let $J$ be the Hessian of the matching cubic at the lift. At
$h=-C_0/Q$ its exact factor is
\[
 Q^2\det J=-4\bigl((F+1)^2 W\,\mathcal P\bigr)^2 ,
\]
where
\[
\begin{aligned}
 \mathcal P={}&(D+1)(d+1)[(1-\lambda)(1+C+b)+C^2b]\\
 &+s\{(d+1)[C(1-\lambda)+CD^2+D^2+D+1]
         +b[(d+1)(C-D)^2+\lambda+C+D+1]\}.
\end{aligned}
\]
One symbolic derivation forms the Hessian before the substitution and
uses Schur pivots $(6,12),(11,6),(5,10),(9,5)$ with values $1,1,-1,-1$,
indexed from zero in the successive matrices. Their signed product
is one. If the remaining determinant is $\sum_{i=0}^3 d_i h^i$,
ordinary multilinearity gives
\[
 \sum_{i=0}^3 d_i (-C_0)^i Q^{3-i}
   =-4Q(F+1)^4 W^2 \mathcal P^2 .
\]
The grouping of the factor into constant and linear parts in $s$
is displayed above. This calculation is a polynomial identity,
not a test at sampled parameters, and is not yet formalized in Lean.

For an actual rotated profile, $\det J=0$ by the
[matching cubic gradient argument](ZhengT40PositiveOverlap.md);
the stronger rank statement is in Zheng, Corollary C.5 and follows
from the secant contraction of
[Howard–Millson–Snowden–Vakil, DOI 10.1112/plms/pds016](https://doi.org/10.1112/plms/pds016).
Thus $\mathcal P=0$. If $\lambda<1$, its first line is strictly positive
and its second nonnegative, a contradiction. This scalar sign step
is checked in [ZhengT40Standalone.lean](MOC/ZhengT40Standalone.lean).
Therefore $CD\ge1$.

Under the self-dual rotation comparison, the two available coefficients
on $\Delta_{12}^2$ and $\Delta_{00}^2$ are $1+C$ and $1+D$.
Both mixed pair coefficients on $(L_{10}\pm R_{10})^2$ are at least one.
The [Lean defect rotation inequality](MOC/ZhengT40RotationBound.lean)
therefore controls the sole negative term $-\Delta_{21}^2$ using
$CD\ge1$. The other squared-minor terms are nonnegative.
The evaluation of subset-image markers as squared minors is due to
[Merikoski and Virtanen, DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X).
The checked [order-four two-table decomposition](MOC/FourMinorTransport.lean)
transfers the bound to every complex unitary, by linearity of the exact
signed expression.

# Positive-height T55+20 at the canonical contact 23

Use Zheng's permutation labels, bracket basis, cubic and lower real
projection convention ([§5.3 and Appendices A, C and E, DOI
10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923)).
Normalize the positive mixed coefficient to one. In the original
T85 chart the canonical T55 contacts 20 and 23 give
$\alpha_5=\alpha_1=0$, respectively. Put
$$
(p,q,r,s,A)=(\alpha_2,\alpha_7,\alpha_3,\alpha_6,\alpha_4),
\quad X=r+s,\quad Y=rs,\quad B=1+X+Y,\quad b=p+1.
$$
All five coefficients are nonnegative. The real lift is
$$
(-A-q,\ p+A+1,\ -1,\ -p,\ q,\ r+s+q+1,\ -p-r-s-1,\
-r,\ A,\ p+r,\ -r-q-1,\ -p-A-1,\ A+q+1,\ 1+h).
$$
The cubic $C$ at this lift is $C_0+hQ$, where
$$
C_0=qY-bB,\qquad Q=A(p-q)-b(X+1)+qX .
$$
In the positive upper-height case the lower-projecting height is
$h<0$.

## Exact secant condition

Let $J=\nabla^2C$ at this lift. On $h=-C_0/Q$, with $Q\ne0$,
$$
Q^2\det J=-4F^2,
\qquad F=f_0+A f_1+A^2 f_2.
$$
The following coefficient table defines $F$: row $i$ gives the
coefficients of $1,q,q^2$ in $f_i$.
$$
\begin{array}{c|ll}
i & [q^0]f_i & [q^1]f_i\\
0 & b^2B^2 & bB(bX+(3p+1)Y+b)\\
1 & b^2B^2 & -XpbB\\
2 & pbB^2 & B(-bX-(2p+1)Y+p^2-1)
\end{array}
$$
The last column is
$$
\begin{aligned}
[q^2]f_0&=b^2(X^2+X)-bXY-(3p+2)Y^2-(p+1)(p+2)Y,\\
[q^2]f_1&=bX^2+pXY-pbX-Y^2-2bY-b^2,\\
[q^2]f_2&=B(Y-b).
\end{aligned}
$$
A reproduction by symbolic identities uses the constant Schur
pivots $(6,12),(11,6),(9,10),(9,9)$, with values $1,1,-1,-1$,
where indices are zero-based in the successive matrices. After
removing row $i$ and column $j$ at unit pivot $J_{ij}$, replace
each remaining entry by $J_{uv}-J_{uj}J_{iv}/J_{ij}$.
The combined signs and pivot values are $+1$, and the remaining
matrix is $M_0+hM_1$. Compute its determinant coefficients $d_i$
with the row-expansion identity
$$
E(i,S)=\sum_{j\in S}(-1)^{|\{j'\in S:j'<j\}|}
(M_{0,ij}+hM_{1,ij})E(i+1,S\setminus\{j\}),
\qquad E(10,\varnothing)=1 .
$$
The degree in $h$ is at most three, and making the substitution
gives the polynomial identity
$$
Q^3d_0-C_0Q^2d_1+C_0^2Qd_2-C_0^3d_3=-4QF^2.
$$
These are symbolic determinant operations, not tests on spectra
or mixers. For actual spectra, $\det J=0$ by Zheng's Corollary C.5
and the secant-variety description of
[Howard–Millson–Snowden–Vakil, DOI 10.1112/plms/pds016](https://doi.org/10.1112/plms/pds016).
The determinant identity itself is not a Lean result here.

## Two exact positive boxes

A violating rotation would require $Aq<1$ and at least one of
$(q-1)r,(q-1)s<1$, by the two rotation budgets described below.
We can assume the first of these latter inequalities: $F$ is
symmetric in $r,s$. In this region, $C_0<0$. Indeed, if $q\le b$
then $C_0\le -b(X+1)$. If $q>b$, then $(q-b)r\le(q-1)r<1$,
and $C_0=(q-b)rs-b(X+1)<0$ as well (including $s=0$).
Hence $C=0$ forces $Q\ne0$. It suffices to prove $F>0$ in the
two boxes, contradicting the secant condition. If $q=0$ then
$F=bB^2[b(1+A)+pA^2]>0$, so take $q>0$.

Set $\theta=Aq$ and
$$
C_0'=q^2 f_0,\quad C_1'=q^2 f_0+q f_1/2,\quad
C_2'=q^2 f_0+q f_1+f_2 .
$$
These are the exact degree-two Bernstein controls:
$$
q^2F=(1-\theta)^2C_0'+2\theta(1-\theta)C_1'+\theta^2 C_2' .
$$
The checked symbolic sign certificate is
[ZhengT55Boundary23.lean](MOC/ZhengT55Boundary23.lean). The
coefficient decompositions used there are as follows:

* If $0<q\le b$, set
  $d_{i\ell}=\sum_{j\le\ell}\binom{4-j}{\ell-j}b^j[q^j]C_i'$.
  Then $b^4 C_i'=\sum_{\ell=0}^4d_{i\ell}q^\ell(b-q)^{4-\ell}$.
  Substituting $X=r+s,Y=rs$ in the displayed $f_i$ gives
  nonnegative $d_{i\ell}$. The coefficient $d_{04}$ is
  strictly positive, so $C_0'>0$, including $q=b$.
* If $q>b$, write $q=b+t$, $u=q-1=p+t$, and
  $D_{i0}=u^2[r^0]C_i'$,
  $D_{i1}=D_{i0}+u[r^1]C_i'/2$,
  $D_{i2}=D_{i0}+u[r^1]C_i'+[r^2]C_i'$, first viewing $q$ as
  independent of $r$, then substituting $q=b+t$.
  Thus at $\rho=ur$,
  $u^2C_i'=(1-\rho)^2D_{i0}+2\rho(1-\rho)D_{i1}+\rho^2D_{i2}$.
  The nine $D_{ij}$ are sums of monomials with nonnegative factors
  in $p,s,t$; the constant-in-$s$ contribution to $D_{00}$
  is $b^2u^2q^2(q+1)>0$.
  For $\rho<1$ this makes $C_0'>0$.

Thus $F>0$ for $\theta<1$ in both boxes. The sign certificate uses
symbolic polynomial identities and positivity of their displayed
factors, with no arithmetic instances or permutation search.

## Support consequence

At the Γ23 boundary the exact signed two-minor objective in the
canonical T55 chart is
$$
qM_g+(A+1)M_G+(s+1)M_A+(r+1)M_\infty+pM_0+M_B-M_a .
$$
The marker directions, in the common projective chart with rows
$(x,y,z,w)$ and columns $(\infty,t,0,1)$, are respectively
$$
\begin{array}{c|rrrrrrr}
 &M_g&M_G&M_A&M_\infty&M_0&M_B&M_a\\ \hline
 \text{source}&yw&xw&zw&xy&yw&zw&xz\\
 \text{target}&t1&t0&t0&t0&\infty t&\infty t&t1.
\end{array}
$$
Each marker evaluates to a squared minor by
[Merikoski–Virtanen, DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X).
The elementary cofactor comparison supplies nonnegativity if
$Aq\ge1$; the conjugated weighted T40 comparison does so if
$q\ge1+1/\min(r,s)$, where this second alternative is used only
when $r,s>0$. For the latter comparison use the T85 chart involution
$\sigma\mapsto D\sigma^{-1}D$, $D=(0\,2)(1\,3)$. It fixes the
center label 17 and the mixed coefficient, exchanges labels 1 and 6,
4 and 11, and 15 and 12. Thus the transformed coefficients obey
$\alpha_4'=q$, $\alpha_2'=s$, $\alpha_5'=r$, and
the already proved [weighted rotation inequality](MOC/ZhengT40RotationBound.lean)
applies after discarding the nonnegative split term. The sign
exclusion proves that at least one of
the two comparisons applies. This closes the canonical Γ23
boundary, not the other possible T55+20 endpoints.

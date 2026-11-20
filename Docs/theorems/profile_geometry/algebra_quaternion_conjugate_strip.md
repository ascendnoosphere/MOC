# A two-parameter, four-distinct-eigenvalue quaternion MOC family

## Scope

This is a restricted MOC theorem for one isoclinic quaternion factor, not for
all of O(4) or U(4). The spectra are genuinely complex, all four eigenvalues
are distinct, and no quaternion coordinate is required to vanish. The
certificate proves every support direction simultaneously by placing the
determinant in an explicit quadrilateral inside the permutation polygon.
No historical-priority claim is made.

The one-parameter subfamily delta=0 and the sharp directional bound in the
last section were obtained in the preceding calculation; the strip below
removes the equality constraint on the sum of the two real eigenvalues.

## Theorem

Let t>0, s=1+t^2, and
\[
|\delta|\le\min(t^2,1),\qquad k=2s+\delta,
\]
\[
m=\frac{k-\sqrt{k^2-4s}}2,\qquad
n=\frac{k+\sqrt{k^2-4s}}2.
\]
Put
\[
a=(1+it,1-it,-m,-n),\qquad b=\bar a.
\]
For every real unit quaternion q=(c,u,v,w), set
\[
U(q)=\begin{pmatrix}
c&u&v&w\\
-u&c&w&-v\\
-v&-w&c&u\\
-w&v&-u&c
\end{pmatrix}.
\]
Then
\[
\boxed{\det(D_a+U(q)D_bU(q)^T)
\in\operatorname{conv}\left\{\prod_{i=1}^4(a_i+b_{\pi(i)}):\pi\in S_4\right\}.}
\tag{1}
\]

Here mn=s and m+n=k. The assumptions imply k>=s+1>2 sqrt(s),
so 0<m<n and all four eigenvalues are distinct.

## 1. An explicit inner quadrilateral

Write z_pi for the permutation product, and set
\[
x=k-2>0,\quad d=n-m>0,\quad K=2\delta^2-sx^2,
\]
\[
M=4sk^2,\qquad L=\max(4sx,-K),\qquad
H_*=\frac{8sktd}{2s+k}.
\tag{2}
\]
All of M,L,H_* are positive. Inverse products satisfy
\(z_{\pi^{-1}}=\bar z_\pi\). Direct multiplication gives
\[
z_{(12)(34)}=M,\qquad z_{(13)}=-4sx,\qquad
\Re z_{(1324)}=K,
\]
\[
z_{(123)}=-4s\delta+4istd,\qquad
z_{(134)}=2k\delta+2iktd.
\tag{3}
\]
For example, with P=1-m+it and Q=1-n+it,
\[
|P|^2=mx,\quad |Q|^2=nx,\quad P\bar Q=-\delta-itd,
\]
which gives the transposition and four-cycle formulas.

The inverse-product relation puts K in the permutation polygon. Also
\[
\frac{k}{2s+k}z_{(123)}+
\frac{2s}{2s+k}z_{(134)}=iH_*.
\]
Taking the conjugate gives -iH_*. Consequently
\[
\operatorname{conv}\{M,-L,iH_*,-iH_*\}
\subseteq\operatorname{conv}\{z_\pi\}.
\tag{4}
\]
We need only containment; the inner quadrilateral need not be the entire
permutation polygon.

## 2. Exact determinant and required inequalities

Put p=cuvw and N=c^2+u^2+v^2+w^2. For the unit quaternion,
\[
D:=\det(D_a+U(q)D_bU(q)^T)
=Q_0-8itd(2s+k)p,
\tag{5}
\]
where
\[
\begin{aligned}
Q_0={}&16s c^4+4sk^2u^4+sx^2(v^4+w^4)\\
&+(16s^2+4k^2)c^2u^2-8sx c^2(v^2+w^2)\\
&+4ksx u^2(v^2+w^2)+2K v^2w^2.
\end{aligned}
\tag{6}
\]
One way to verify this quartic expansion is to expand
\(\det((a_i+b_j)U(q)_{ij})\): it equals D because det U(q)=1.
Equations (5)-(6) are homogeneous quartic expressions used below; equality
to the original determinant is asserted for N=1.

Set
\[
\gamma=\frac{(2s+k)^2}{sk}=8+\frac{\delta^2}{sk}.
\]
Then |Im D|/H_*=gamma |p|. Membership in (4), for N=1, is equivalent to
\[
MN^2-Q_0-M\gamma|p|\ge0,\qquad
LN^2+Q_0-L\gamma|p|\ge0.
\tag{7}
\]

## 3. Positive-real facets: exact sum of squares

Choose epsilon in {+1,-1} such that epsilon p=|p|. Define
\[
A=4((2s-1)k^2-4s^2),\quad B=4sk(k+2),
\]
\[
\rho=1+\frac{2\delta^2(k+2)}A,\qquad
G=A+2s(k+2)^2.
\]
The following is an identity:
\[
\begin{aligned}
MN^2-Q_0-M\gamma|p|
={}&A(cu-\varepsilon\rho vw)^2\\
&+B[(cv-\varepsilon uw)^2+(cw-\varepsilon uv)^2]\\
&+(M-16s)c^4+(M-sx^2)(v^4+w^4)\\
&+4s(k+2)x c^2(v^2+w^2)\\
&+(G-A\rho^2)v^2w^2.
\end{aligned}
\tag{8}
\]
For the interference coefficient, explicitly,
\[
2A\rho+4B=4k(2s+k)^2=M\gamma.
\]

Since k>=2 sqrt(s), we have A>=16s(s-1)>0. The parameter restriction gives
\[
\delta^2\le1\le\frac{s(k+2)}4,\qquad
\delta^4\le s-1\le\frac{sA}4.
\]
Thus
\[
G-A\rho^2=2s(k+2)^2-4\delta^2(k+2)
-\frac{4\delta^4(k+2)^2}A\ge0.
\]
All remaining coefficients in (8) are nonnegative because s>1 and k>2.
This proves the first inequality in (7).

## 4. Negative-real facets: AM-GM with a strict margin

All mixed-square coefficients of LN^2+Q_0 are nonnegative. The only ones
requiring a check are 2L-8sx and 2L+2K; both are nonnegative by (2).
The pure fourth-power coefficients on c^4,u^4,v^4,w^4 are
\[
A_0=L+16s,\qquad B_0=L+4sk^2,\qquad C_0=L+sx^2,\quad C_0.
\]
We claim
\[
A_0B_0C_0^2\ge20L^4.
\tag{9}
\]
Indeed ell=L/s satisfies 0<ell<=max(4x,x^2), and
\[
\frac{A_0B_0C_0^2}{L^4}=
\left(1+\frac{16}{\ell}\right)
\left(1+\frac{4(x+2)^2}{\ell}\right)
\left(1+\frac{x^2}{\ell}\right)^2
\]
is decreasing in ell. For x>=4, use ell=x^2 to bound the product below by
1 times 5 times 4=20. For 0<x<=4, use ell=4x to obtain
\[
\frac{(x+1)(x+4)^4}{16x^2}\ge20.
\]
For x>=1/4 this follows from (x+4)^2>=16x; for x<1/4, it follows already
from (x+4)^4>=256.

Also delta^2<=s-1 and k>=s+1, so
\[
\gamma\le8+\frac{s-1}{s(s+1)}\le\frac{33}4
<4\,20^{1/4}.
\]
AM-GM and (9) give
\[
A_0c^4+B_0u^4+C_0v^4+C_0w^4
\ge4(A_0B_0C_0^2)^{1/4}|p|
\ge4\,20^{1/4}L|p|\ge L\gamma|p|.
\]
The nonnegative mixed terms complete the second inequality in (7), proving
(1).

## 5. Explicit additional example

Take t=3/4, s=25/16, delta=1/2. Then m=1/2, n=25/8. Scaling both spectra
by 8 gives
\[
\boxed{a=(8+6i,8-6i,-4,-25),\qquad b=\bar a.}
\]
The theorem applies for every U(q). The earlier delta=0 example was
(8+6i,8-6i,-5,-20). Simultaneous complex scaling of the spectra scales every
determinant and permutation product by the same fourth power, preserving
convex-hull membership.

## 6. A sharp general conjugate-spectrum directional bound

For arbitrary a in C^4 and b=bar a, let
\[
h=\max_{\pi\in S_4}|\Im z_\pi|.
\]
For every quaternion U(q) above,
\[
\boxed{|\Im\det(D_a+U(q)D_{\bar a}U(q)^T)|\le h/2.}
\tag{10}
\]
In the permutation expansion, the terms with even quaternion exponents
are involution products or sums of inverse four-cycle products, hence real.
Only the product cuvw contributes to the imaginary part. Its coefficient
is the signed sum
\[
T=-(z_{(123)}-z_{(132)})+(z_{(124)}-z_{(142)})
 -(z_{(134)}-z_{(143)})+(z_{(234)}-z_{(243)}).
\]
Each difference is purely imaginary with modulus at most 2h. Hence |T|<=8h.
Since |cuvw|<=1/16, (10) follows. For
\[
a=(8+6i,8-6i,-5,-20),\quad b=\bar a,
\]
direct multiplication gives h=36000 and T=-288000i. At c=u=v=w=1/2,
|Im D|=18000=h/2, so the constant is sharp.

This bound does not extend unchanged to arbitrary real orthogonal matrices:
for the same spectra an even three-cycle permutation matrix is in SO(4) and
attains imaginary part 36000. Thus neither (10) nor the strip theorem proves
the still-unresolved all-O(4) case. The local unitary realification theorem
reduces unrestricted MOC4 to that all-O(4) case, not to a single quaternion
factor.

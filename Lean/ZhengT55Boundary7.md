# Standalone T55: quadratic reduction at contact 7

This is an exact paper reduction, not a proof of the support inequality for
T55+7. It uses the lexicographic row-to-column labels of
[Zheng, Appendices E and G](https://doi.org/10.13140/RG.2.2.36790.25923).
Use the strictly positive-height, simple, noncollision branch of
[Standalone T55](StandaloneT55.md). The other height and collision branches
are dealt with by the references there. No new Lean verification is claimed.

Consider a strict witness with the six contacts \(1,2,3,6,11,12\) and
the additional contact \(7\). Use \(D=P_3-P_2\), \(\eta D=i\delta\),
\(u=P_6/D\), \(v=u+l\), \(\tau=v-k\), and \(H=-\delta\Im u>0\) from
the standalone reduction. In that chart \(k>0,\ l\ne0,\ r\ne0\),
\(m=l+\lambda-k+1\ne0\), and \(G_{17}=-H rml/|u|^2>0\).
We can assume \(\lambda\ne0\), since
\(\lambda=0\) is the [T55+20 case](ZhengT55PositiveOverlap.md).

Set
\[
\nu=(P_7-P_6)/D,\qquad c=\lambda+\nu,\qquad
s=l-k,\qquad W=\nu s+\lambda l,\qquad d=k-c,\qquad
D_1=du-W.
\]
The ratio \(\nu\) is real by the contact conditions. Both \(\nu\) and \(c\)
are nonzero: \(P_7-P_6\) and \(P_7-P_1\) are single-swap differences on
simple noncollision data.

In the chart with column spectra \((\infty,t,0,1)\) and row spectra
\((x,y,z_{\rm spec},w)\), labels \(6,7\) are \(1023,1032\), respectively.
Their products are
\[
P_6=(x-t)z_{\rm spec}(w-1),\qquad P_7=(x-t)(z_{\rm spec}-1)w.
\]
Thus \(\gamma/\alpha=(u+\nu)/u\), where
\(\alpha=(w-1)/w,\ \gamma=(z_{\rm spec}-1)/z_{\rm spec}\).
With \(\rho=r\gamma\), the existing chart gives
\[
r\alpha=\frac{u(\rho\tau-k)}{(u-\lambda)v},\qquad
r\alpha=\frac{\rho u}{u+\nu}.
\]
Equating yields \(\rho[(u+\nu)\tau-(u-\lambda)v]=k(u+\nu)\).
The bracket is \(-D_1\). As \(u\) is nonreal, \(u+\nu\ne0\);
consequently \(D_1\ne0\), and
\[
\rho=-\frac{k(u+\nu)}{D_1},\qquad
\alpha=-\frac{ku}{rD_1}.
\]
In particular, the standalone signed-star identity gives the strict
condition
\[
0<\Delta=\frac{k\delta\Im\alpha}{|\alpha|^2}
       =-\frac{rWH}{|u|^2},
\qquad
\frac{\Delta}{G_{17}}=\frac{W}{ml}.
\]
For the second equality, \(\Im(u\overline{D_1})=-W\Im u\).
In particular \(W\ne0\), so the exceptional locus \(W=0\) cannot contain
a strict witness.

The chart equation before clearing denominators is
\(r\alpha X(1-\gamma)=Y(rv-Xu)(\gamma-\alpha)\), with
\(X=1+\rho,\ Y=X\tau/v\). Substitute
\(\gamma-\alpha=\alpha\nu/u\) to obtain
\(uv(r-\rho)=\nu(u+s)(rv-Xu)\).
Here \(D_1(rv-Xu)=v(rD_1+cu)\) by the expression for \(\rho\).
It follows that the nonreal \(u\) satisfies the real polynomial equation
\[
 u\bigl[rD_1+k(u+\nu)\bigr]
 -\nu(u+s)\bigl[rD_1+cu\bigr]=0. \tag{1}
\]

## Consequences

Write (1) as \(Au^2+Bu+C=0\). Its coefficients are
\[
 A=rd(1-\nu)+k-\nu c,\qquad
 B=k\nu+rW(\nu-1)-\nu s(rd+c),\qquad
 C=\nu s r W.
\]

- **If \(l\ne k\):** \(C\ne0\), so the polynomial is not identically
  zero. A nonreal root requires \(A\ne0\) and \(B^2-4AC<0\). For fixed
  real \((\lambda,l,k,r,\nu)\), the roots form a conjugate pair; the
  height \(H=-\delta\Im u>0\) selects one. The rational formulas above
  fix \(\rho,\alpha\); the rest of the chart then fixes the spectral
  profile. This rules out all nonnegative-discriminant parameter data
  without evaluating the determinant at any mixer.
- **If \(l=k\):** \(C=0\), and the nonreal nonzero \(u\) forces
  \(A=B=0\). Now \(W=\lambda k\), \(m=1+\lambda\), and the signs
  \(\lambda/m<0\), \(-rml>0\) imply \(-1<\lambda<0\), \(r<0\).
  The equation \(B=0\) becomes \(r\lambda(1-\nu)=\nu\).
  Using this equality in \(A=0\) gives
  \(0=\lambda A=c[k-\nu(1+\lambda)]\), and \(c\ne0\). Therefore
  \[
    \nu=\frac{k}{1+\lambda}\in(0,1),\qquad
    r=\frac{\nu}{\lambda(1-\nu)},\qquad 0<k<1+\lambda.
  \]
  The upper bound on \(\nu\) follows from \(r\lambda>0\).
  These are necessary parameter restrictions, not sufficient
  conditions for all gaps to be nonnegative.

The signed-star inequality is still required in the negative-discriminant
branch and on the exceptional \(l=k\) locus. This reduction does not
settle contacts \(9,18,21,23\) or standalone T55.

# Reflection tests at a real stationary order-four mixer

These are paper proofs of necessary tests, not a bound for a dense maximizer.
They supplement the [stationary pivot reduction](StationaryPivotReduction.md).
All identities below use the additive spectral model, not a relaxation of
the set of permutation profiles.

Let \(A=\operatorname{diag}(a)\), \(C=U\operatorname{diag}(b)U^T\),
where \(U\) is real orthogonal. Put \(S=A+C\), suppose \(S\)
is invertible, and write \(M=S^{-1}\), \(\lambda=\eta\det S\),
\(F=\operatorname{Re}\lambda\). For any nonzero complex \(x\) set
\(H_x=I-2xx^*/(x^*x)\), and let
\[
 Q(x)=(x^*x)^2\operatorname{Re}\{\eta[\det(A+H_xCH_x)-\det S]\}.
\]
At a global support maximizer, \(Q(x)\le0\) for all \(x\).
Reflections at coordinates and at columns of \(U\) preserve the
objective: they only change row signs or commute with \(C\).

## Exact rank-two formula

Write \(n=x^*x\), \(u=x^*Mx\), \(p=x^*MCx\), \(p'=x^*CMx\),
\(w=x^*CMC x\), \(b_x=x^*Cx\). Then
\[
 \frac{Q(x)}4
 =\operatorname{Re}\!\left[\lambda\left\{
 u(b_x-w)-\frac n2(p+p')+pp'\right\}\right].
 \tag{1}
\]
Indeed
\[
 H_xCH_x-C=-\frac2n\{x x^*C+(Cx)x^*\}+\frac{4b_x}{n^2}xx^*
\]
with the explicit factorization
\[
 L=[x,Cx],\qquad R=\begin{bmatrix}x^*\\x^*C\end{bmatrix},\qquad
 T=\begin{pmatrix}4b_x/n^2&-2/n\\-2/n&0\end{pmatrix},\qquad
 H_xCH_x-C=LTR .
\]
The two-sided factorization does not use \(C=C^*\).
Apply \(\det(S+LTR)=\det S\det(I_2+TRML)\), which follows
from \(\det(I+XY)=\det(I+YX)\). Here
\(RML=\begin{pmatrix}u&p\\p'&w\end{pmatrix}\);
its trace contribution after multiplication by \(T\) is
\(4b_xu/n^2-2(p+p')/n\), and the determinant contribution is
\(-4(uw-pp')/n^2\). This proves (1).

For real \(x\), symmetry gives \(p=p'\). Since \(M(A+C)=I\)
and \(C-CMC=CMA\), (1) reduces to
\[
 Q(x)/4=\operatorname{Re}\!\left[
 \lambda\left\{(x^TMx)(x^TCMAx)-(x^TMCx)(x^TMAx)\right\}\right].
 \tag{2}
\]

## The two tests on a pivot plane

Fix \(y=e_i\), \(z=Ue_j\), \(t=y^Tz=U_{ij}\), assume
\(|t|<1\), and set
\[
 B_0=a_i+b_j,\quad u_0=y^TMy,\quad v_0=z^TMz,\quad
 w_0=y^TMz,\quad \Delta=t-B_0 w_0 .
\]
The identity \(A M U+M U\operatorname{diag}(b)=U+[A,M]U\)
gives \(\Delta=-([A,M]U)_{ij}\).
For real skew \(K\), differentiating the determinant along
\(e^{\theta K}U\) gives
\(\operatorname{Re}[\lambda\operatorname{tr}([C,M]K)]\).
Thus real stationarity says \(\operatorname{Re}(\lambda[A,M])=0\),
since \(A,C,M\) are symmetric and \([C,M]=-[A,M]\).
In particular \(\operatorname{Re}(\lambda\Delta)=0\).

Apply (1) at \(x=y+iz\). The scalars \(n,u,p,p',b_x-w\)
are respectively
\[
 2,\quad u_0+v_0,\quad P-i\Delta,\quad P+i\Delta,\quad
 a_i+b_j-a_i^2u_0-b_j^2v_0,\qquad
 P=1-a_i u_0+b_jv_0 .
\]
These follow from \(Ay=a_i y\), \(Cz=b_j z\),
\(CMA=C-CMC=A-AMA\), and \(SM=MS=I\).
After collecting the two pure-square terms, this gives
\[
 Q(y+iz)/4
 =\operatorname{Re}\left[\lambda\left\{\Delta^2-
     (1-B_0u_0)(1-B_0v_0)\right\}\right].                       \tag{3}
\]
For \(x=y\pm z\), the corresponding scalars in (1) are
\(n=2(1\pm t)\), \(u=u_0+v_0\pm2w_0\),
\(p=p'=1\pm t-a_i u_0+b_jv_0\pm(b_j-a_i)w_0\), and
\(b_x-w=B_0-a_i^2u_0-b_j^2v_0\pm2a_i b_jw_0\).
The mixed term uses \(y^T CMAz=a_i b_jw_0\), obtained by
writing \(MAz=z-b_jMz\). Collecting shows that
\(Q(y+z)/4\) has right side (3) minus
\(2(1+t)\operatorname{Re}(\lambda\Delta)\), while \(Q(y-z)/4\)
has right side (3) plus \(2(1-t)\operatorname{Re}(\lambda\Delta)\).
**At stationarity all three homogeneous defects agree.**

The two real reflections send column \(j\) to \(-e_i\) and \(+e_i\),
respectively. If their common defect is zero at a maximum, the
maximizer has a sparse representative and the stationary pivot
theorem closes the comparison. If the support value strictly
exceeds all permutation scores, then both reflected scores are
strictly smaller: each is an anchored order-three support
problem. Equivalently every scalar on the right of (3) is strictly
negative. Since
\(\lambda\Delta=i\mu_{ij}\) for a real \(\mu_{ij}\), this reads
\[
 \operatorname{Re}[\lambda(1-B_0u_0)(1-B_0v_0)]
 +\frac{F}{|\lambda|^2}\mu_{ij}^2>0.                           \tag{4}
\]
Here \((\mu_{ij})\) equals \(-K_0U\) for the single real skew
matrix \(K_0=-i\lambda[A,M]\); the scalars are not independent.

These formulas do not imply that (4) is impossible. In particular
the complex test \(y+iz\) gives no extra inequality over the two
real reflections on this pivot plane, and for positive \(F\) the
skew-square term in (4) cannot be omitted to strengthen the
necessary condition. The geometric octad example is separate:
it rules out inferring extra reflection zeros from a quartic sign
and the eight phase directions alone, but supplies no additive
spectral lift or violating maximizer.

## Real rank-one phase and a quantitative pair bound


For complex diagonal \(A,B\) and real orthogonal \(U\), put
\(B'=UBU^T\), \(C=A+B'\) and assume that \(M=C^{-1}\) exists.
Let \(f(V)=\det(A+VBV^{-1})\). For a real unit vector \(u\) set \(P=uu^T\) and \(V=(I+zP)U\).
Then
\[
(A(I+zP)+(I+zP)B')=(I+z H)C,
\qquad H=P+[A,P]M.
\]
Writing \(H=u u^T(I-AM)+Au u^T M\), the two-column determinant lemma gives
\(\det(I+zH)=1+z+z^2 q(u)\). To see the coefficient explicitly, let
\(b=u^TMu,\ c=u^TMAu,\ d=u^TAMAu,\ m=u^TAu\).
The two-by-two determinant is \(q(u)=c(1-c)-b(m-d)\).
By \(B'u=Cu-Au\), this coefficient is also
\[
q(u)=-\langle u\wedge Au,(\wedge^2M)(u\wedge B'u)\rangle,
\]
where the pairing is complex bilinear. Divide by \(\det(I+zP)=1+z\).
At \(z=e^{it}-1\), this yields the exact identity
\[
f(V)=\det C\,[1+2(\cos t-1)q(u)] .
\]
If \(U\) maximizes \(\Re(\eta f)\) on the unitary group,
\(\Re(\eta\det C\,q(u))\ge0\) for all real \(u\); use the homogeneous wedge formula for nonunit vectors.

For \(u=xe_i+yv_j\) with \(v_j=Ue_j\), put
\[
k=a_i+b_j,\quad s=e_i^Tv_j,\quad
\mu=e_i^TMe_i,\quad\nu=v_j^TMv_j,\quad\rho=e_i^TMv_j.
\]
Then
\[
q(u)=xy[(s-k\rho)(x^2+y^2)+xy T_{ij}],
\qquad
T_{ij}=1+s^2-k(\mu+\nu)+k^2(\mu\nu-\rho^2).
\]
Indeed \(u\wedge Au=y u\wedge(C-kI)v_j\),
\(u\wedge B'u=x u\wedge(C-kI)e_i\), and \(e_i^TCv_j=ks\).
After expanding the two-by-two wedge pairing, the expression inside the prefactor \(xy\) is
\[
(u^TMu)(ks-k^2\rho)
+(u^Tv_j-k u^TMv_j)(u^Te_i-k u^TMe_i).
\]
For \(|s|<1\), the projected coefficient of \(xy(x^2+y^2)\) must vanish by nonnegativity on both sides of \(x=0\); hence \(\Re(\eta\det C T_{ij})\ge0\).
The Householder reflections in the directions \(e_i\pm v_j\) send column \(v_j\) to \(\mp e_i\), and their respective projected losses are
\(\Re(\eta\det C T_{ij})/(1\pm s)^2\).
If \(F=\Re(\eta f(U))\) strictly exceeds the best permutation score \(m_*\), both reflected mixers have projected score at most \(m_*\) by the checked [column reflection reduction](MOC/OrderFourColumnReflections.lean). Thus
\[
\Re(\eta\det C T_{ij})\ge(F-m_*)(1+|s|)^2.
\]
This is a necessary family of paired reflection bounds on a dense candidate at an invertible maximizer. It does not exclude all such candidates. The [symmetric rank-one phase segment](MOC/OrderFourReflectionTest.lean) is checked in Lean. The explicit inverse-matrix coefficient, cross-span expansion, and paired inequality above are paper derivations.

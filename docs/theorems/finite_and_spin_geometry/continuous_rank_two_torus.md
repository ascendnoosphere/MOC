# An exact projective quadratic criterion for complex rank-two phase tori

The statements below hold in every matrix dimension. They analyze an actual determinant support functional at an arbitrary base point. They do not assume that a coefficient law, positive stochastic lift, or global MOC assertion is already available.

## 1. Separate rank-one harmonicity

Let \(A,B\) be normal matrices in a fixed presentation, let \(u,v\) be orthonormal complex vectors, and put

\[
G(\theta_1,\theta_2)
=I+(e^{i\theta_1}-1)uu^*
+(e^{i\theta_2}-1)vv^*.
\]

Fix a support phase \(\eta\), and define

\[
f(\theta_1,\theta_2)
=\Re\{\eta\det(A+GBG^*)\}.
\]

For fixed \(\theta_2\), the first phase is an ordinary rank-one phase update of a new base matrix. Here is the block determinant proof of its harmonicity. In coordinates where that projection selects the first coordinate, write the two matrices in blocks as \(\begin{psmallmatrix}a&r\\s&A_0\end{psmallmatrix}\) and \(\begin{psmallmatrix}b&p\\q&B_0\end{psmallmatrix}\). With \(z=e^{i\theta}\) and \(C=A_0+B_0\), their updated determinant is

\[
(a+b)\det C-(r+zp)\operatorname{adj}(C)(s+z^{-1}q).
\]

This polynomial block identity is valid even for singular \(C\), and only frequencies \(-1,0,1\) occur. The same argument applies to the second phase, because the two projections commute. Therefore \(f\) is a real trigonometric polynomial of bidegree at most \((1,1)\). Normality is not needed for this harmonicity statement.

Assume the base is stationary along these two axes:

\[
f_1(0,0)=f_2(0,0)=0.
\tag{1}
\]

Full stationarity of the unitary support functional is sufficient, but not necessary, for (1).

Every such polynomial has the exact form

\[
\begin{aligned}
f-f_0={}&A(\cos\theta_1-1)+B(\cos\theta_2-1)\\
&+C(\cos\theta_1-1)(\cos\theta_2-1)\\
&+D\sin\theta_1(\cos\theta_2-1)
+E(\cos\theta_1-1)\sin\theta_2\\
&+F\sin\theta_1\sin\theta_2.
\end{aligned}
\tag{2}
\]

To see completeness, start with the nine products of \(1,\cos,\sin\) in the two variables. The two first-derivative conditions eliminate the two independent linear sine coefficients. Subtracting the constant value leaves precisely the six terms in (2).

## 2. The projective quadratic form

Use half-angle variables

\[
x=\tan(\theta_1/2),\qquad y=\tan(\theta_2/2),\qquad
w=(x,y,xy)^T.
\]

Substituting \(\cos\theta=(1-t^2)/(1+t^2)\) and \(\sin\theta=2t/(1+t^2)\) in (2) gives

\[
\boxed{
f(\theta_1,\theta_2)-f_0
=\frac{w^T\mathcal M w}{(1+x^2)(1+y^2)},}
\tag{3}
\]

where

\[
\mathcal M=
\begin{pmatrix}
-2A&2F&-2E\\
2F&-2B&-2D\\
-2E&-2D&4C-2A-2B
\end{pmatrix}.
\tag{4}
\]

Indeed the numerator obtained directly is

\[
-2Ax^2-2By^2+4Fxy-4Ex^2y-4Dxy^2
+(4C-2A-2B)x^2y^2.
\]

All coefficients of \(\mathcal M\) have intrinsic variational meanings. Let every derivative below be evaluated at \((0,0)\). Equation (2) gives

\[
f_{11}=-A,\quad f_{22}=-B,\quad f_{12}=F,
\quad f_{112}=-E,\quad f_{122}=-D.
\]

Also \(f(\pi,\pi)-f_0=4C-2A-2B\). Hence

\[
\boxed{
\mathcal M(u,v)=
\begin{pmatrix}
2f_{11}&2f_{12}&2f_{112}\\
2f_{12}&2f_{22}&2f_{122}\\
2f_{112}&2f_{122}&f(\pi,\pi)-f_0
\end{pmatrix}.}
\tag{5}
\]

The endpoint is the actual double reflection \(G(\pi,\pi)=I-2(uu^*+vv^*)\). In particular, no hypothetical endpoint set replaces the true geometry.

## 3. Global torus nonascent is exactly a three by three PSD test

The main consequence is

\[
\boxed{
f(\theta_1,\theta_2)\le f_0\text{ for all real phases}
\quad\Longleftrightarrow\quad
\mathcal M(u,v)\preceq0.}
\tag{6}
\]

Sufficiency follows immediately from (3), first at finite half-angle coordinates and then everywhere by continuity.

For necessity, the projective directions \([x:y:xy]\) fill a dense subset of the real projective plane. Given a direction \([a:b:c]\) with \(abc\ne0\), take

\[
x=c/b,\qquad y=c/a.
\]

Then

\[
(x,y,xy)=\frac{c}{ab}(a,b,c).
\]

If \(\mathcal M\) had any positive quadratic direction, continuity would give one with all three coordinates nonzero. The displayed substitution would then make the numerator in (3) positive, a contradiction. This proves (6).

This is a legitimate quadratic reduction because the relevant projective image is dense. The coordinates in (3) are constrained as an affine surface, but their homogeneous directions impose no additional quadratic restriction.

Equation (6) also gives an explicit ascent construction. Find \(z=(a,b,c)\) with \(z^T\mathcal Mz>0\), perturb it slightly if a coordinate vanishes, and set

\[
\theta_1=2\arctan(c/b),\qquad
\theta_2=2\arctan(c/a).
\]

Those phases strictly improve the support.

## 4. The exact coherence inequality and degenerate cases

Let

\[
H=\begin{pmatrix}f_{11}&f_{12}\\f_{12}&f_{22}\end{pmatrix},\quad
c=\begin{pmatrix}f_{112}\\f_{122}\end{pmatrix},\quad
\Delta=f(\pi,\pi)-f_0.
\]

When \(H\prec0\), the Schur complement of the upper block in (5) gives the equivalent conditions

\[
H\prec0,
\qquad
\boxed{\Delta\le2c^TH^{-1}c.}
\tag{7}
\]

The right side is nonpositive. Thus the double-reflection loss must be large enough to control the third-derivative coupling, not merely have the correct sign.

For singular \(H\preceq0\), negative semidefiniteness first requires \(c\) to be orthogonal to \(\ker H\); on its range, (7) uses the inverse restricted to that range. This follows by evaluating the quadratic form on \((z,t)\) with \(z\in\ker H\): a nonzero coupling would give both signs as \(t\) varies.

In particular, if \(H=0\), global nonascent is equivalent to

\[
c=0,\qquad \Delta\le0.
\]

A fourth-order endpoint gain can therefore defeat a completely zero Hessian. The exact two-phase surface in `continuous_plateau_transport.md`, \(7+\kappa^2\sin^2(\theta_1/2)\sin^2(\theta_2/2)\) is precisely this case with \(\Delta=\kappa^2>0\).

## 5. Exact verification with genuinely nonzero cubic terms

To check the derivative signs and factors independently, the certificate takes \(\eta=1\) and uses diagonal spectral data

\[
a=(1+i,\,2-i,\,-1+2i,\,-2-3i),
\quad
b=(2+i,\,-1+3i,\,3-2i,\,1-i),
\]

and the orthonormal complex vectors

\[
u=(1,1,1,1)/2,
\qquad v=(1,2i,-2,1-2i)/\sqrt{14}.
\]

Their projectors have Gaussian rational entries. The base is stationary, and an exact discrete Fourier reconstruction gives

\[
f_{112}=218/7,\qquad f_{122}=-1616/49,
\]

\[
\mathcal M=
\begin{pmatrix}
231/4&293/7&436/7\\
293/7&2022/49&-3232/49\\
436/7&-3232/49&4105/98
\end{pmatrix}.
\]

The code reconstructs the whole bidegree-one Fourier polynomial from a unisolvent roots-of-unity grid and verifies (3) at rational half-angle points. The explicit algebra in Section 2 proves the identity generally; this independent calculation checks the nonzero third-derivative normalization on actual determinant data.

## 6. A full real rank-two rotation has a two by two version

Let \(K\) be a real rank-two skew matrix normalized by \(K^3=-K\), and put

\[
g(\theta)=\Re\{\eta\det(A+e^{\theta K}Be^{-\theta K})\}.
\]

Every exterior power of \(e^{\theta K}\) has only the frequencies \(-1,0,1\): its eigenvalues are products of \(e^{i\theta},e^{-i\theta}\), and ones, with neither nonzero phase repeated. The squared-minor determinant expansion consequently has frequencies at most two. Equivalently, diagonalize \(K\) over \(\mathbb C\) and restrict its two-phase torus to opposite phases.

Suppose \(g'(0)=0\). Writing its degree-two trigonometric polynomial and imposing stationarity gives the exact identity

\[
\boxed{
g(\theta)-g(0)
=\frac{t^2}{(1+t^2)^2}
\left[2g''(0)+\frac43g'''(0)t+
(g(\pi)-g(0))t^2\right],
\quad t=\tan(\theta/2).}
\tag{8}
\]

For example, if \(g=c_0+c_1\cos\theta+c_2\cos2\theta+s_1\sin\theta+s_2\sin2\theta\), then \(s_1=-2s_2\). The numerator after the substitution is

\[
t^2[-2(c_1+4c_2)-8s_2t-2c_1t^2],
\]

which is (8), since \(g''=-c_1-4c_2\), \(g'''=-6s_2\), and \(g(\pi)-g(0)=-2c_1\).

The complete fiber is nonascending exactly when

\[
\boxed{
\begin{pmatrix}
2g''(0)&\tfrac23g'''(0)\\
\tfrac23g'''(0)&g(\pi)-g(0)
\end{pmatrix}\preceq0.}
\tag{9}
\]

This simultaneously controls local curvature, cubic coherence, and the actual half-turn endpoint. It works in every dimension and at arbitrary stationary bases.

If \(g''(0)=0\), a nonzero third derivative gives an immediate cubic ascent in one direction. If both derivatives vanish, (8) reduces to

\[
g(\theta)-g(0)=(g(\pi)-g(0))\sin^4(\theta/2).
\]

Thus a null-curvature fiber is either cubic, exactly quartic, or constant; no higher-order uncertainty remains for this one-parameter rank-two motion.

## 8. A useful real-frame simplification

If \(A^T=A\), \(B^T=B\), and \(u,v\) are real, then \(G^T=G\). Transposing the determinant gives

\[
\det(A+GBG^*)=\det(A+G^*BG),
\]

so \(f(-\theta_1,-\theta_2)=f(\theta_1,\theta_2)\). The torus is stationary at zero and every odd total derivative there vanishes. Thus \(f_{112}=f_{122}=0\), and (6) simplifies to the conjunction

\[
H\preceq0,
\qquad f(\pi,\pi)\le f_0.
\tag{11}
\]

For complex phase axes the third derivatives can be nonzero, as Section 5 demonstrates. Consequently dropping them in the unrestricted complex problem would lose genuine information.

## Scope

At a global unitary support maximum, (6) holds for every orthonormal complex pair. No implication from that universal family to the permutation support bound is proved here; ordinary local maximality is not the hypothesis of (6).

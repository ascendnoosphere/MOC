## 1. Configuration and the actual permutation ceiling

Set

\[
a=(i,i,-i,-i),\qquad b=(-3,-1,-2,0),\qquad
O=\frac12\begin{pmatrix}
1&1&1&1\\1&-1&1&-1\\1&1&-1&-1\\1&-1&-1&1
\end{pmatrix},
\]

\[
A=D_a,\qquad B=OD_bO^T=
\begin{pmatrix}
-3/2&-1&-1/2&0\\
-1&-3/2&0&-1/2\\
-1/2&0&-3/2&-1\\
0&-1/2&-1&-3/2
\end{pmatrix}.
\]

Write \(d(G)=\det(A+GBG^*)\) and \(f(G)=\Re d(G)\). Thus the original unitary in the MOC presentation is \(U=GO\). Direct expansion gives \(d(I)=7\). The distinct permutation products are

\[
\{\pm10i,\;6\pm8i,\;8\pm6i\},
\]

so their real support ceiling is \(8\).

## 2. A general first-harmonic identity for a rank-one unitary phase

For arbitrary square matrices \(A,B\), a unit vector \(v\), and

\[
G_\theta=I+(e^{i\theta}-1)vv^*,
\]

the function \(\det(A+G_\theta BG_\theta^*)\) contains only the Fourier frequencies \(-1,0,1\). To prove this, choose an orthonormal basis whose first vector is \(v\), and write

\[
A=\begin{pmatrix}a&r\\s&A_0\end{pmatrix},\quad
B=\begin{pmatrix}b&t\\u&B_0\end{pmatrix},\quad M_0=A_0+B_0.
\]

With \(z=e^{i\theta}\), the block determinant identity, valid even when \(M_0\) is singular, gives

\[
\det(A+G_\theta BG_\theta^*)
=(a+b)\det M_0-(r+zt)\operatorname{adj}(M_0)(s+z^{-1}u).
\tag{1}
\]

Consequently the real support has the form \(c+\alpha\cos\theta+\beta\sin\theta\). If its derivative at zero vanishes, then

\[
f(I)-f(G_\theta)=\sin^2(\theta/2)\,[f(I)-f(G_\pi)].
\tag{2}
\]

This identity concerns a fixed rank-one phase axis at an arbitrary base point. It does not say that optimizing one such axis guarantees improvement.

## 3. A general Householder determinant formula

Suppose \(M=A+B\) is invertible, put \(R=M^{-1}\) and \(D=\det M\), and let \(H_v=I-2vv^*\) for \(\|v\|=1\). Define

\[
x=v^*Rv,\quad y=v^*ARv,\quad z=v^*RAv,\quad q=v^*ARBv.
\]

Then

\[
\boxed{d(H_v)=D\big[(1-2y)(1-2z)+4xq\big].}
\tag{3}
\]

Indeed \(d(H_v)=\det(H_vAH_v+B)\). The difference from \(M\) is

\[
v(-2v^*A+4\alpha v^*)+(Av)(-2v^*),\qquad \alpha=v^*Av.
\]

The two by two determinant lemma reduces its determinant ratio to

\[
(1-2y+4\alpha x)(1-2z)
-(-2v^*ARAv+4\alpha z)(-2x).
\]

After expansion, use \(\alpha-v^*ARAv=v^*ARBv\) to obtain (3). For nonunit \(v\), the homogeneous quartic numerator is

\[
D_h(v)=D\big[(\rho-2y)(\rho-2z)+4xq\big],\qquad \rho=v^*v.
\tag{4}
\]

## 4. An exact complex sum of squares blocks every single rank-one update

For the configuration in Section 1,

\[
14R=\begin{pmatrix}
-6-8i&1+6i&4&-3\\
1+6i&-6-8i&-3&4\\
4&-3&-6+8i&1-6i\\
-3&4&1-6i&-6+8i
\end{pmatrix}.
\]

Substitution into (4) and collection of the bidegree \((2,2)\) monomials gives the polynomial identity

\[
\boxed{7\|v\|^4-\Re D_h(v)
=16|v_1v_3-v_2v_4|^2+12|v_1v_4-v_2v_3|^2.}
\tag{5}
\]

The products inside the absolute values are bilinear in the coordinates of \(v\); they contain no internal conjugation. The right side expands as

\[
\begin{aligned}
&16(|v_1|^2|v_3|^2+|v_2|^2|v_4|^2)
-32\Re(v_1v_3\bar v_2\bar v_4)\\
&\quad+12(|v_1|^2|v_4|^2+|v_2|^2|v_3|^2)
-24\Re(v_1v_4\bar v_2\bar v_3).
\end{aligned}
\]

This gives a direct hand-checkable expansion against the displayed inverse. The identity can also be checked coefficientwise over Gaussian rational arithmetic.

The support is stationary along every unitary direction at this base point. One way to verify the required rank-one derivatives is

\[
D[B,R]=\begin{pmatrix}
0&0&-4i&3i\\0&0&3i&-4i\\
4i&-3i&0&0\\-3i&4i&0&0
\end{pmatrix},
\]

which is Hermitian. Thus
\(\Re\frac{d}{d\theta}d(G_\theta)|_{\theta=0}
=\Re(i v^*D[B,R]v)=0\).

Equations (2) and (5) now prove, for every complex unit vector \(v\) and every real \(\theta\),

\[
\boxed{7-f(G_\theta)=\sin^2(\theta/2)
\big(16|v_1v_3-v_2v_4|^2+12|v_1v_4-v_2v_3|^2\big)\ge0.}
\tag{6}
\]

The point lies strictly below the permutation support ceiling but admits no improving single rank-one unitary update.

## 5. The flat locus is explicit and large enough for transport

The simultaneous equations in (5) have exactly four complex plane components:

\[
\begin{split}
&\operatorname{span}_{\mathbb C}(e_1,e_2),\qquad
\operatorname{span}_{\mathbb C}(e_3,e_4),\\
&\operatorname{span}_{\mathbb C}(e_1+e_2,e_3+e_4),\qquad
\operatorname{span}_{\mathbb C}(e_1-e_2,e_3-e_4).
\end{split}
\tag{7}
\]

For a proof, set \(p=(v_1,v_2)\), \(q=(v_3,v_4)\). If both are nonzero, the equations say

\[
\begin{pmatrix}v_1&-v_2\\-v_2&v_1\end{pmatrix}q=0.
\]

Hence \(v_1^2=v_2^2\), and the signs of \(v_2/v_1\) and \(v_4/v_3\) agree. The zero top or bottom vectors give the first two components.

The first two planes commute with \(A\). The other two allow an exact change in the imaginary part of the determinant while keeping its real support at \(7\). Therefore the one-step obstruction is not an obstruction to support-preserving transport followed by improvement.

## 6. Two orthogonal phases: full factorization and monotone escape

Choose the real orthonormal vectors

\[
u=\frac{(1,1,2,2)^T}{\sqrt{10}},\qquad
v=\frac{(1,-1,-2,2)^T}{\sqrt{10}},
\]

and define

\[
G(\theta_1,\theta_2)=I+(e^{i\theta_1}-1)uu^T
+(e^{i\theta_2}-1)vv^T.
\]

Let \(s_j=\sin^2(\theta_j/2)\) and \(\kappa=24/25\). The exact determinant is

\[
\boxed{d(G(\theta_1,\theta_2))=(7-i\kappa s_1)(1+i\kappa s_2),}
\tag{8}
\]

so

\[
\boxed{f(G(\theta_1,\theta_2))=7+\kappa^2s_1s_2.}
\tag{9}
\]

There is a simple block proof. In the orthonormal basis consisting of the top and bottom plus vectors, followed by the top and bottom minus vectors, \(A\) consists of two copies of \(\operatorname{diag}(i,-i)\), whereas \(B\) consists of

\[
B_+=\begin{pmatrix}-5/2&-1/2\\-1/2&-5/2\end{pmatrix},\qquad
B_-=\begin{pmatrix}-1/2&-1/2\\-1/2&-1/2\end{pmatrix}.
\]

The vector \(u\) acts only on the plus block, with coordinates \((1,2)/\sqrt5\). The vector \(v\) acts only on the minus block, with coordinates \((1,-2)/\sqrt5\). A direct two by two determinant expansion gives \(7-i\kappa s_1\) and \(1+i\kappa s_2\), respectively. Their product proves (8). Independently, (1) bounds the Laurent degree by one in each phase, so exact verification on a four by four roots-of-unity grid also certifies the complete identity.

Both coordinate axes of (9) are flat. After moving to any \(s_1>0\), the second phase increases the support monotonically as \(\theta_2\) runs from zero to \(\pi\). On the diagonal \(\theta_1=\theta_2=\theta\), the increase begins at fourth order:

\[
f-7=\frac{576}{625}\sin^4(\theta/2).
\]

The rational Householder matrices at the endpoint give

\[
d(H_u)=7-\frac{24}{25}i,\qquad
d(H_vH_u)=\frac{4951}{625}+\frac{144}{25}i.
\tag{10}
\]

Because \(u\perp v\), the combined update differs from the identity in rank at most two. In particular, this is an exact finite rank-two escape through a flat rank-one fiber.

More generally put \(u=(c,c,s,s)/\sqrt2\), \(v=(c,-c,-s,s)/\sqrt2\), where \(c^2+s^2=1\). The same block calculation replaces \(\kappa\) by

\[
\kappa=-4cs(c^2-s^2).
\]

Writing \(c=\cos\alpha,s=\sin\alpha\), one has \(|\kappa|=|\sin4\alpha|\le1\). Choosing \(\alpha=3\pi/8\) makes \(\kappa=1\) and the double Householder endpoint reaches the actual permutation vertex \(8+6i\). Thus the factorization accounts for the entire support gap in this example.

## 7. Rank-four coherent rotations and a genuine real rank-two gauge completion

Let \(K_4\) be the real skew matrix with upper triangular entries \((K_4)_{14}=(K_4)_{23}=1\) and all others zero. Then \(K_4^2=-I_4\), and its rank is four. A direct homogeneous polynomial expansion gives

\[
\det\big(A(cI+sK_4)+(cI+sK_4)B\big)
=7c^4+18c^2s^2+7s^4-12ics(c^2+s^2).
\]

For \(c=\cos\phi,s=\sin\phi\), this proves

\[
d(e^{\phi K_4})=7+\sin^2(2\phi)-6i\sin(2\phi).
\tag{11}
\]

Although (11) uses two coupled real plane rotations, there is a rank-two representative of exactly the same determinant trajectory after a change of speed. Let \(Z\) have upper triangular entries \(Z_{12}=1,Z_{34}=-1\), and set

\[
K=\frac12(K_4+Z)
=Y\begin{pmatrix}0&1\\-1&0\end{pmatrix}Y^T,
\qquad
Y=\frac1{\sqrt2}\begin{pmatrix}1&0\\0&1\\-1&0\\0&1\end{pmatrix}.
\]

The matrix \(K\) has rank two and \(K^3=-K\). Direct multiplication gives \([Z,A]=0\) and \([Z,K_4]=0\), so

\[
e^{\theta K}=e^{\theta Z/2}e^{\theta K_4/2}.
\]

The first factor commutes with \(A\), and hence its left conjugation does not affect the determinant. Therefore (11) implies

\[
\boxed{d(e^{\theta K})=7+\sin^2\theta-6i\sin\theta.}
\tag{12}
\]

This single real rank-two rotation improves immediately and monotonically for \(0\le\theta\le\pi/2\), reaching the permutation vertex \(8-6i\). The phenomenon is a precise commutant gauge completion: the components in the stabilizer of \(A\) reduce the generator rank without altering the objective trajectory.

For an independent exact certificate, use the integer generator \(K_0=2K\) and its Cayley transform. Since \(K_0^3=-4K_0\), setting \(\theta=2\arctan(2t)\) turns (12) into

\[
d=\frac{7+72t^2+112t^4-i(24t+96t^3)}{(1+4t^2)^2}.
\]

The code verifies the full polynomial identity after clearing denominators.


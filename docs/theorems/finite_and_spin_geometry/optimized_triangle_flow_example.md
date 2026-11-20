\[
a=(3,0,-1,0),\qquad b=(-2,0,-1,-3),\qquad \eta=1,
\]

and the complex two-plane spanned by the columns of

\[
K=\begin{pmatrix}1&0\\0&1\\0&1-i\\-1-i&1+i\end{pmatrix}.
\]

Put \(G=K^*K=\left(\begin{smallmatrix}3&-2\\-2&5\end{smallmatrix}\right)\), \(Y=KG^{-1/2}\), and \(P=YY^*=KG^{-1}K^*\). Thus \(Y^*Y=I_2\) and \(\det G=11\). All entries of \(P\) are Gaussian rational. The identity permutation attains the support maximum \(h=0\).

Use the notation of `continuous_spectral_rank_two_budget.md`, with indices starting at one. Only two transposition deficits are nonzero:

\[
\delta_{12}=36,\qquad \delta_{23}=3.
\]

The four canonical triangle allocations are

\[
(\chi_{123},\chi_{124},\chi_{134},\chi_{234})=(-5/13,-1,0,1).
\]

Their explicit edge flow has

\[
a_{12}=\frac{2i}{11},\qquad
a_{23}=\frac{21(1-i)}{143}.
\]

The remaining edges have zero weight and are irrelevant to the energy. The reflection endpoint has the exact support loss

\[
g=h-\det\bigl(\operatorname{diag}(a)+(I-2P)\operatorname{diag}(b)(I-2P)\bigr)
=\frac{600}{121}.
\]


## Why the optimized budget survives

Write \(T=G^{1/2}SG^{1/2}\), where

\[
S=\begin{pmatrix}s&x+iy\\x-iy&t\end{pmatrix}.
\]

The change of Hermitian coordinates is invertible and
\(L_{ij}(T)=K_iSK_j^*\). Therefore

\[
L_{12}=x+iy,\qquad L_{23}=(1+i)t,
\]

\[
\mathcal A=36(x^2+y^2)+6t^2,
\qquad \ell=\frac{288}{11}y.
\]

The edge \(23\) contributes nothing to \(\ell\), because

\[
\Re\!\left(\overline{\frac{21(1-i)}{143}}(1+i)t\right)=0.
\]

Deleting that edge flow preserves the entire cubic covector. The remaining flow is the minimum-energy representative:

\[
C_{\min}=\frac1{16}\ell^T\mathcal A^+\ell
=\frac{144}{121},\qquad
\boxed{g-4C_{\min}=\frac{24}{121}>0.}
\]

If \(d=\det T\) and \(D(T)=\det(I+T^2)>0\), the exact whole-plane identity is now

\[
\begin{aligned}
(h-F(V(T)))D(T)
={}&144\left|x+iy-\frac{2i}{11}d\right|^2
 +24t^2+\frac{24}{121}d^2\ge0.
\end{aligned}
\]

The dense Cayley chart and continuity include every \(V\in U(2)\). Thus the optimized certificate proves the complete scalar MOC support inequality on this plane.

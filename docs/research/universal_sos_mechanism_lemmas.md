## 1. Fully proved: the Gram freedom is small and explicit

Write
\[
t=\operatorname{coords}(T),\qquad
c=\operatorname{coords}(C),\quad C=\operatorname{adj}T,\qquad d=\det T.
\]

First consider spectra and a support direction for which the identity permutation maximizes. Then \(G(0)=0\), so every SOS summand has zero constant. The complete basis is \((t,c,d)\), as established in the route document (`organized/research/SINKHORN_SOS_CERTIFICATE_ROUTE.md:60–87`).

Every candidate Gram consequently has the form
\[
X=
\begin{pmatrix}
 A&B&u\\
 B^T&D&e\\
 u^T&e^T&g
\end{pmatrix},
\qquad g=g_{R_0}.
\]
Its homogeneous pieces are
\[
\begin{aligned}
G_2&=t^TAt,\\
G_3&=2t^TBc,\\
G_4&=c^TDc+2d\,u^Tt,\\
G_5&=2d\,e^Tc,\\
G_6&=g d^2.
\end{aligned}
\]

### Exact kernel calculation

I independently computed the multiplication-map ranks using exact rational arithmetic:

| Basis | Degree | Gram coefficients | Image dimension | Kernel dimension |
|---|---:|---:|---:|---:|
| \((t,c,d)\) | 2 | 45 | 45 | 0 |
| | 3 | 81 | 65 | 16 |
| | 4 | 54 | 45 | 9 |
| | 5 | 9 | 9 | 0 |
| | 6 | 1 | 1 | 0 |

Thus **\(A,e,g\) are forced**, and all freedom consists of:

* **16 cubic parameters:** the traceless components of
  \[
  TC=CT=dI;
  \]
* **9 quartic parameters:**
  \[
  \operatorname{adj}C=dT.
  \]

These identities span the kernel. One explanation for the cubic dimension is the complexified generic-matrix decomposition
\[
(\Lambda^1\otimes\Lambda^2)_{\rm left}
 \otimes
(\Lambda^1\otimes\Lambda^2)_{\rm right}.
\]
Multiplication retains the \(8\times8\) component and the determinant component, giving \(64+1=65\); the two mixed components, each dimension eight, are the kernel. The exact symbolic rank calculation independently confirms this count.

For the full basis \((1,t,c,d)\), the kernel dimension is **35**. The additional identities are nine degree-two cofactor identities and one degree-three identity:
\[
1\cdot c_j=\operatorname{cofactor}_j(T),\qquad
1\cdot d=\tfrac13\operatorname{tr}(TC).
\]

**Payoff:** invariant theory produces a finite, explicit completion problem—not a positivity theorem.

## 2. Fully proved: actual support gaps determine the quadratic block

Let
\[
z_\pi=\prod_i(a_i+b_{\pi(i)}),\qquad
\Delta_{ij}=\Re\!\left(\eta(z_{\rm id}-z_{(ij)})\right).
\]
When the identity supports, every \(\Delta_{ij}\ge0\). With \(S=YTY^T\),
\[
\boxed{\quad G_2(T)=4\sum_{i<j}\Delta_{ij}|S_{ij}|^2.\quad}
\]

This follows by expanding \(W=I+2iS-2S^2+\cdots\), or directly from the complementary-minor expansion. It requires no division by spectral sums and therefore includes singular cases.

Consequences:

* The forced block \(A\) is PSD.
* If all six transposition gaps are strictly positive, then \(A\succ0\). Indeed \(S e=0\), so a diagonal \(S\) must vanish.
* Zero transposition gaps identify \(\ker A\) exactly through the displayed sum.

There is also an exact rank-one version. For
\[
L=\lambda vv^*,\quad \|v\|=1,\qquad p_i=|(Yv)_i|^2,
\]
one obtains
\[
\boxed{\quad
G(tL)=4t^2\lambda^2\sum_{i<j}p_ip_j\Delta_{ij}
\quad}
\]
in the identity-support case. The corresponding unitary is a rank-one phase update; its complementary minors give this identity.

This proves positivity along every rank-one ray in that chart. **It does not control the mixed rank-two/rank-three terms.**

## 3. A concrete analytic mechanism: exact Schur completion

Define \(D_0\) uniquely by
\[
G_4=c^TD_0c.
\]
This is possible because \(dT=\operatorname{adj}C\); uniqueness follows because the nine cofactor coordinates are algebraically independent.

For \(u\in\mathbb R^9\), define the symmetric matrix \(L(u)\) by
\[
c^TL(u)c=u^T\operatorname{coords}(\operatorname{adj}C).
\]
Then every admissible quartic block is
\[
D(u)=D_0-2L(u).
\]
Likewise write
\[
B=B_0+K,\qquad K\in\mathcal K_3,
\]
where \(\dim\mathcal K_3=16\).

Hence, when \(A\succ0\), SOS feasibility is **exactly** the existence of \(u,K\) such that
\[
\boxed{
\begin{pmatrix}
D_0-2L(u)-B^TA^{-1}B&
e-B^TA^{-1}u\\
e^T-u^TA^{-1}B&
g-u^TA^{-1}u
\end{pmatrix}\succeq0.}
\]

This isolates the missing universal inequality: actual spectral support data would have to supply these 25 parameters with the required domination.

For singular \(A\), replace \(A^{-1}\) by \(A^+\) and additionally require
\[
\operatorname{range}(B,u)\subseteq\operatorname{range}A.
\]


## 4. Actual-spectral boundary example: \(g_{R_0}=0\) nevertheless has an exact SOS

Consider
\[
a=(1,1,-1,-1),\qquad
b=(i,i,-i,-i),\qquad \eta=1.
\]
The permutation products are \(4\) or \(-4\), so \(h=4\). Every 3-cycle gives \(4\), and therefore
\[
F(R_0)=4,\qquad g_{R_0}=0.
\]

This example has a simple global analytic certificate.

Let \(P=\operatorname{diag}(1,1,0,0)\), and let \(X\) denote the compression of \(WPW^*\) to \(\operatorname{range}P\). The two-principal-angle decomposition of the involutions gives
\[
F(W)=-4\det(2X-I_2).
\]
Since
\[
1+\det(2X-I_2)
=2\bigl(\det X+\det(I_2-X)\bigr),
\]
Cauchy–Binet yields
\[
\boxed{
4-F(W)=8\left(
|\det W[12,12]|^2+
|\det W[12,34]|^2
\right).}
\]

Now use the compound numerators from the route document (`organized/research/SINKHORN_SOS_CERTIFICATE_ROUTE.md:93–134`). In the stated coordinate convention, I computed exactly
\[
\begin{aligned}
\delta_-\,\det W[12,12]&=1+C_{22}+2i\Re T_{13},\\
\delta_-\,\det W[12,34]&=C_{33}-C_{11}+2i\Im C_{13}.
\end{aligned}
\]
Therefore
\[
\boxed{
G(T)=8\left[
(1+C_{22})^2
+4(\Re T_{13})^2
+(C_{33}-C_{11})^2
+4(\Im C_{13})^2
\right].}
\]

This is an exact four-square certificate, with no cubic summands and no sextic term. An additional exact rational sample check gave zero residual.

**Interpretation:** degeneracy of \(g_{R_0}\) can encode a lower-degree minor-square certificate rather than infeasibility. A universal argument must distinguish benign degeneracy of this kind from a genuine completion obstruction. This example does not suggest universality by numerical extrapolation.

## 5. Contact zeros: useful facial reduction, not the missing positivity argument

For every finite contact \(T_0\),
\[
G(T_0)=0,\quad X\succeq0
\quad\Longrightarrow\quad Xq(T_0)=0.
\]
The same reasoning applies to a leading projective evaluation vector at a contact at infinity.

These contact constraints explain why positive definiteness is sought only on a reduced space.

But contact equations alone do not prove that the remaining affine Gram space intersects the PSD cone. Additional contact continua—such as those arising from repeated spectra in the involution example—may force a substantially smaller face than permutation contacts reveal.

The exact recovery code correctly distinguishes coefficient identities and positivity checks from floating feasibility (`organized/research/rational_sinkhorn_certificates.py:72–75`, `organized/research/rational_sinkhorn_certificates.py:140–152`). Those checks remain instance/family certificates, not an existence theorem.


## 1. Proved lemma: flat-pair resonance and transport

Absorb the original unitary into the normal matrix \(B\), and write
\[
F(B)=\Re\{\eta\det(A+B)\},\qquad A=\operatorname{diag}(a_1,a_2,a_3,a_4).
\]
Assume \(\eta\ne0\), \(a_1\ne a_2\), and that \(B\) is an **actual global maximizer** on its unitary orbit.

Partition
\[
A=\begin{pmatrix}A_2&0\\0&A_0\end{pmatrix},\quad
B=\begin{pmatrix}P&Q\\V&S\end{pmatrix},
\]
where \(A_2=\operatorname{diag}(a_1,a_2)\) and \(A_0=\operatorname{diag}(a_3,a_4)\). Suppose
\[
E=A_0+S
\]
is invertible. Define
\[
T=P-QE^{-1}V,\qquad L=QE^{-1},\qquad M=E^{-1}V,
\]
and
\[
c=\frac{a_1+a_2}{2},\quad d=\frac{a_1-a_2}{2},\quad
\gamma=\eta\det E,\quad \tau=\gamma d.
\]

Suppose a nontrivial tangent direction in the two-row \(U(2)\) fiber has zero support curvature. Here “nontrivial” excludes the stabilizer directions that do not move \(A_2\).

### Conclusions

1. The **entire two-row fiber is exactly support-flat**.
2. \(T\) is normal. By support-preserving transport within that fiber, arrange
   \[
   T=\operatorname{diag}(t_1,t_2).
   \]
3. At this transported global maximum, put \(\widehat t_\mu=t_{3-\mu}\), and, for \(\mu=1,2\), \(k=3,4\), define
   \[
   f_{\mu k}=\widehat t_\mu+a_k,
   \]
   \[
   g_{\mu k}=a_1a_2-ca_k+(c-a_k)\widehat t_\mu.
   \]
   Then the following **exact cross-stationarity identities** hold:
   \[
   \boxed{\gamma g_{\mu k}L_{\mu k}
   +\bar\gamma\,\bar g_{\mu k}(M^*)_{\mu k}=0,}
   \tag{1}
   \]
   \[
   \boxed{\tau f_{\mu k}L_{\mu k}
   +\bar\tau\,\bar f_{\mu k}(M^*)_{\mu k}=0.}
   \tag{2}
   \]
4. Consequently,
   \[
   \boxed{\Im\!\left(g_{\mu k}\overline{d f_{\mu k}}\right)\ne0
   \quad\Longrightarrow\quad
   L_{\mu k}=(M^*)_{\mu k}=0.}
   \tag{3}
   \]

In particular, if for one \(\mu\), condition (3) holds for **both** \(k=3,4\), then the transported pair has a common coordinate eigenvector. Thus the maximizer has reached a solved \(1+3\) block face **without losing support**.

This is a conditional face-reduction lemma, not a universal assertion about stationary points.

---

## 2. Derivation

### A. Zero pair curvature gives an exact plateau

Move the two-row rotation from \(B\) onto \(A\). Its upper block becomes
\[
Z=cI+dN,\qquad N=N^*,\quad \operatorname{tr}N=0,\quad N^2=I.
\]
Schur complementation gives
\[
\det(A+B)=\det E\,\det(Z+T).
\]
For \(2\times2\) matrices,
\[
\det(Z+T)=\det Z+\det T+\operatorname{tr}Z\,\operatorname{tr}T-\operatorname{tr}(ZT).
\]
Here \(\det Z=a_1a_2\) and \(\operatorname{tr}Z=2c\) are fixed. Hence the support is an affine height function on the Bloch sphere:
\[
F(N)=C_0-\Re\{\tau\operatorname{tr}(NT)\}.
\tag{4}
\]

At a maximum of a sphere height function, every nonzero tangent curvature is strictly negative unless the height vector vanishes. Therefore one zero nonstabilizer pair curvature forces (4) to be constant.

This uses the exact two-row geometry already established in `organized/extracted/volume_sections/N076.txt:20–48`; it is not a general “Hessian zero implies flatness” argument.

Flatness means
\[
\frac{\tau T+\bar\tau T^*}{2}=\alpha I,\qquad \alpha\in\mathbb R.
\]
Since \(\tau\ne0\), this implies \(T\) is normal. Thus a unitary acting only in the first two coordinates diagonalizes \(T\), while preserving the support exactly.

### B. Actual maximality supplies stationarity along the whole plateau

Let \(C=A+B\). Define the polynomial gradient matrix
\[
\mathcal D=\eta[\operatorname{adj}C,A].
\]
Unitary stationarity is equivalent to \(\mathcal D=\mathcal D^*\). This formulation does not require \(C\) invertible.

Every point of the flat fiber is still a global maximum. Consequently this Hermiticity condition holds for **every** \(N\) in (4), not merely at the original base point. This is the maximizer-specific extra information.

After diagonalizing \(T\), let \(H=Z+T\). The cross blocks of the adjugate satisfy
\[
(\operatorname{adj}C)_{12}=-\det E\,\operatorname{adj}(H)L,
\qquad
(\operatorname{adj}C)_{21}=-\det E\,M\operatorname{adj}(H).
\tag{5}
\]
These remain valid when \(H\) is singular, by polynomial continuation.

Using
\[
\operatorname{adj}(H)=cI+\operatorname{adj}(T)-dN
\]
and \(N^2=I\), expansion of \([\operatorname{adj}C,A]\) gives
\[
\mathcal D_{12}
=\gamma\bigl(G\odot L+dN(F\odot L)\bigr),
\tag{6}
\]
\[
\mathcal D_{21}
=-\gamma\bigl(G^T\odot M+d(F^T\odot M)N\bigr),
\tag{7}
\]
where \(F_{\mu k}=f_{\mu k}\), \(G_{\mu k}=g_{\mu k}\), and \(\odot\) denotes entrywise multiplication.

Now impose \(\mathcal D_{12}=\mathcal D_{21}^*\) for both \(N\) and \(-N\). Separating the constant and linear terms gives (1) and (2).

The determinant of their \(2\times2\) coefficient system is
\[
2i|\gamma|^2\Im\!\left(g_{\mu k}\overline{d f_{\mu k}}\right).
\]
This proves (3).

**Ascent interpretation.** At a stationary point with this flat fiber, failure of (1)–(2) certifies that some point on the support-flat fiber has nonzero feasible gradient. Moving there and then following that gradient gives genuine unitary ascent. Actual maxima therefore cannot evade these identities.

### C. Why vanishing produces a genuine simpler face

If one row \(\mu\) of \(L\) and the corresponding column of \(M\) vanish, then
\[
Q=LE,\quad V=EM,\quad P=T+LEM
\]
show that coordinate \(\mu\) is a common eigenvector of \(A\) and \(B\). This is an actual reducing block, not merely a zero in a relaxed coefficient model.

---

## 3. The resonance has explicit circle geometry

For \(a_k\notin\{a_1,a_2\}\), consider
\[
\Phi_k(t)=
\frac{a_1a_2-ca_k+(c-a_k)t}{d(t+a_k)}.
\]
It satisfies
\[
\Phi_k(-a_1)=1,\qquad
\Phi_k(-a_2)=-1,\qquad
\Phi_k(-a_k)=\infty.
\]
Thus
\[
\Im\!\left(g_{\mu k}\overline{d f_{\mu k}}\right)=0
\]
means precisely that \(\widehat t_\mu\) lies on the generalized circle through
\[
-a_1,\ -a_2,\ -a_k.
\tag{8}
\]

Therefore:

* If either effective eigenvalue lies off both circles corresponding to \(k=3,4\), the flat transport reaches a common eigenvector and hence a solved block face.
* If the four \(a_i\) are distinct and not on one generalized circle, those two circles intersect only at \(-a_1,-a_2\). Away from these endpoints, each row of \(L\) can couple to **at most one** external label.

This is a concrete sparsification of the cross-resolvent couplings, not yet a full classification.

### A further case closed using actual normality

Suppose additionally \(T=tI\), the four \(a_i\) are not on one generalized circle, and \(t\ne-a_1,-a_2\).

By (8), both rows of \(L\) are supported in at most the same single external column. Hence \(\operatorname{rank}L\le1\). Another support-flat \(U(2)\) rotation makes one row of \(L\) zero; \(T=tI\) remains unchanged.

That row of \(B\) then has no off-diagonal entries. **Normality of \(B\)** gives the exact norm identity
\[
\sum_{j\ne\mu}|B_{j\mu}|^2
=\sum_{j\ne\mu}|B_{\mu j}|^2=0.
\]
Thus its column also has no off-diagonal entries. A common eigenvector has been obtained without loss.

So the **scalar-effective-Schur flat branch is closed under these stated nondegeneracy hypotheses**.

---


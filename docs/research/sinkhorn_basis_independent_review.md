## 1. Gap identities and signs

The phase-gauge reduction, bordered determinant, and Cayley multiplication in `organized/research/SINKHORN_GLOBAL_REDUCTION.md:21–101` are correct, conditional on the quoted Sinkhorn theorem.

In particular, direct multiplication gives
\[
(I-iS)(A+WBW^*)(I+iS)
=A+B+i[A-B,S]+S(A+B)S.
\]
Thus the commutator sign and both border signs in equation (6) are correct. No invertibility of \(A+B\) is required.

Here is a universal verification of the compound formulas in `organized/research/try_sinkhorn_sos.py:26–32`. Write
\[
e_2=\operatorname{tr}(\operatorname{adj}T),\qquad \delta=\det T,
\]
\[
d_-=\det(I-iT)=1-e_2+i(\delta-\operatorname{tr}T),\qquad d_+=\overline{d_-},
\]
and
\[
N=(1+e_2-i\delta)I-2\operatorname{adj}T
+i(2T-\operatorname{tr}T\,I).
\]
The adjugate identity gives
\[
N=(I+iT)\operatorname{adj}(I-iT)=d_-V.
\]
With
\[
J=\begin{pmatrix}0&0&1\\0&-1&0\\1&0&0\end{pmatrix},
\]
complementary minors give
\[
d_-C_2(V)=J\overline N J.
\]
The code’s `Nminus=N.conjugate().T` followed by `J*Nminus.T*J` is therefore **correct**: the transpose is essential.

Consequently the five blocks for \(d_-C_k(\operatorname{diag}(1,V))\) are exactly
\[
[d_-],\quad \operatorname{diag}(d_-,N),\quad
\operatorname{diag}(N,J\overline NJ),\quad
\operatorname{diag}(J\overline NJ,d_+),\quad[d_+].
\]
Conjugating by the corresponding compounds of \(H\) gives the script’s numerators. Squared moduli divided by
\[
|d_-|^2=\det(I+T^2)
\]
give the squared minors of \(W\). The complementary-minor expansion then produces precisely \(G\).

These formulas also establish the proposed structural hypotheses:

* Every numerator is linear in \([1,T,\operatorname{adj}T,\det T]\), so \(G\) has degree at most six.
* For rank-one Hermitian \(R\), \(\operatorname{adj}(tR)=0=\det(tR)\). Every numerator is affine in \(t\), hence \(\deg G(tR)\le2\).
* At \(T=0\), \(G_0=0\) when identity is supporting. The first variation vanishes because \(A+B\) and its adjugate are diagonal, while \([A-B,S]\) has zero diagonal. Thus \(G_1=0\), even for singular \(A+B\).
* For invertible \(T\), \(W(tT)\to R_0\), yielding
  \[
  G_6(T)=g_R\det(T)^2,\qquad
  g_R=h-\operatorname{Re}(\eta F(R_0)).
  \]
  Polynomial identity extends this to singular \(T\).

The eight-3-cycle averaging argument proving \(g_R\ge0\) in `organized/research/SINKHORN_GLOBAL_REDUCTION.md:107–115` is also correct.

## 2. Self-contained proof of SOS completeness

Let \(G\) be a real polynomial satisfying the proposed hypotheses and suppose
\[
G=\sum_j f_j^2
\]
with real polynomials \(f_j\).

### Degree and constants

If the largest summand degree were \(d>3\), the degree-\(2d\) component would be a sum of squares of nonzero leading forms and could not vanish identically. Therefore \(\deg f_j\le3\).

Since \(G(0)=0\), every \(f_j(0)=0\). Write
\[
f_j=\ell_j+q_j+c_j
\]
in homogeneous degrees \(1,2,3\). Notice that \(G_1=0\) is redundant for this SOS argument.

### Cubics are multiples of the determinant

Comparing degree six gives
\[
\sum_j c_j(T)^2=g_R\det(T)^2.
\]
On every real Hermitian rank-two matrix, each \(c_j\) therefore vanishes.

Here are the required algebraic details. Complexifying the nine Hermitian coordinates gives an invertible linear parametrization of all complex \(3\times3\) matrices. The determinant hypersurface is irreducible: the rank-at-most-two locus is the image closure of the irreducible parametrization \(XY\), with \(X\) of size \(3\times2\) and \(Y\) of size \(2\times3\); the determinant is square-free at \(\operatorname{diag}(1,1,0)\).

Real Hermitian rank-two points are Zariski dense in that hypersurface. Indeed, on the patch
\[
T=\begin{pmatrix}B&z\\z^*&r\end{pmatrix},\qquad \det B\ne0,
\]
the equation is \(r=z^*B^{-1}z\). A polynomial vanishing throughout this real patch becomes, after clearing denominators, a polynomial identity in eight real parameters; complexification gives the full complex patch.

Thus \(\det T\) divides every \(c_j\). Equal degrees imply
\[
c_j=\alpha_j\det T,\qquad \alpha_j\in\mathbb R.
\]

### Quadratics are combinations of adjugate coordinates

On a rank-one Hermitian \(R\), the cubic parts vanish. Hence
\[
G(tR)=\sum_j\bigl(t\ell_j(R)+t^2q_j(R)\bigr)^2.
\]
Its \(t^4\) coefficient is \(\sum_jq_j(R)^2\), which must vanish. Therefore every \(q_j\) vanishes on the Hermitian rank-one cone.

To identify these quadrics, substitute \(R=vv^*\). Complexifying the real and imaginary parts of \(v\) makes \(v\) and \(\overline v\) independent vectors \(z,w\). Thus the complexified quadratic vanishes on \(zw^T\).

Under \(X_{ij}\mapsto z_iw_j\), quadratic monomials have identical images exactly through column exchanges:
\[
X_{ij}X_{k\ell}-X_{i\ell}X_{kj}.
\]
Therefore the quadratic kernel is spanned by the nine \(2\times2\) minors. On Hermitian matrices their real form is precisely the nine real coordinates of \(\operatorname{adj}T\).

Consequently every \(f_j\) belongs to
\[
\operatorname{span}_{\mathbb R}
[T\text{ coordinates},\operatorname{adj}T\text{ coordinates},\det T].
\]

Writing this vector as \(w(T)\), the representation gives \(G=w^TQw\) with \(Q\succeq0\). Conversely, factoring any real PSD \(Q\) supplies an SOS. This proves the **19×19 equivalence**.

Without \(G(0)=0\), retain each summand’s constant. The same cubic and rank-one arguments work unchanged, proving the **20×20 version**, provided the other structural hypotheses remain.

## 3. Permutation contacts and projective limits

The inverse Cayley sign in `organized/research/try_sinkhorn_sos.py:98–106` is correct:
\[
T_0=-i(V-I)(V+I)^{-1}.
\]
For finite contacts, \(G(T_0)=0\), so every PSD Gram matrix representing \(G\) annihilates \(w(T_0)\).

If \(V\) has eigenvalue \(-1\), let \(P_-\) be its orthogonal spectral projector, \(m=\operatorname{rank}P_-\), and
\[
T_0=-i(V-I)(V+I)^\dagger,\qquad T_t=tP_-+T_0.
\]
Normality ensures \(T_0\) is Hermitian, vanishes on the excluded eigenspace, and has the required Cayley transform on its complement. Thus \(W(T_t)\to P\).

For the permutation matrices, the highest power in \(w(T_t)\) is exactly \(t^m\). If
\[
v_\infty=\lim_{t\to\infty}t^{-m}w(T_t),
\]
then
\[
\frac{\det(I+T_t^2)}{t^{2m}}
\longrightarrow c>0.
\]
At a supporting permutation,
\[
v_\infty^TQv_\infty
=\lim_{t\to\infty}\frac{G(T_t)}{t^{2m}}
=c\,[h-\operatorname{Re}(\eta F(P))]=0.
\]
PSD therefore implies \(Qv_\infty=0\). The script’s leading-coefficient extraction is valid; its constant coordinate correctly becomes zero.

Exact checks covered all 24 permutations: nine have no excluded eigenvalue, twelve have multiplicity one, and three have multiplicity two. All contact-zero assertions for the fourteen listed rays passed.


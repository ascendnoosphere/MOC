## 1. Source verification and global coverage

I used TheoremSearch and checked the original [Idel–Wolf, arXiv:1408.5728v3, §2, Theorem 2](https://arxiv.org/html/1408.5728):

> Every \(U\in U(n)\) admits diagonal unitaries \(L,R\) such that every row and column sum of \(LUR\) is \(1\).

There is **no** entrywise-positivity, nonzero-entry, genericity, or transversality hypothesis. Transversality enters later intersection-counting remarks, not this existence theorem.

Put
\[
F(U)=\det(D_a+UD_bU^*).
\]
Because the diagonal unitaries commute with \(D_a,D_b\),
\[
F(LUR)=F(U).
\]

Let
\[
e=\frac12(1,1,1,1)^T,\qquad
Y=\frac12
\begin{pmatrix}
1&1&1\\
-1&1&-1\\
1&-1&-1\\
-1&-1&1
\end{pmatrix}.
\]
Then \(H=[e\ Y]\in SO(4)\). A unitary \(W\) with row and column sums \(1\) satisfies
\[
H^TWH=1\oplus V,\qquad V\in U(3),
\]
and hence
\[
W=W(V):=ee^T+YVY^T.
\]

Thus
\[
\boxed{\{F(U):U\in U(4)\}=\{F(W(V)):V\in U(3)\}.}
\]

This resolves the **global coverage** issue for this route. No rank-two coverage assertion is needed.

---

## 2. Explicit exterior-square reduction

Write \(y_i=Y^Te_i\in\mathbb R^3\). For a two-element set \(I=\{i,j\}\), \(i<j\), define
\[
p_I=\frac{y_j-y_i}{2},\qquad q_I=y_i\times y_j.
\]
Let \(P,Q\in\mathbb R^{6\times3}\) have rows \(p_I^T,q_I^T\), respectively, with pairs ordered
\[
12,13,14,23,24,34.
\]
These are the coordinate matrices of \(e\wedge e^\perp\) and \(\bigwedge^2e^\perp\). Consequently,
\[
P^TP=Q^TQ=I,\qquad P^TQ=0.
\]

For \(\delta=\det V\), the precise exterior decomposition is
\[
\bigwedge\nolimits^2(1\oplus V)
   =V\oplus\delta\overline V,
\]
where the second summand uses the oriented basis \(23,31,12\). Therefore
\[
\boxed{
\det W(V)[I,J]
=p_I^TVp_J+\delta\,\overline{q_I^TVq_J}.
}
\tag{1}
\]

This identity is valid for every \(V\in U(3)\), including all degeneracies.

### Product-linked support coefficients

For a subset \(I\), write \(a_I=\prod_{i\in I}a_i\), and similarly for \(b\). Set
\[
\alpha_i=a_{[4]\setminus\{i\}},\qquad
\beta_j=b_{[4]\setminus\{j\}}.
\]
Fix any support phase \(|\eta|=1\), and define real coefficients
\[
c_{ij}=\Re\!\left[\eta(\alpha_i b_j+a_i\beta_j)\right],
\qquad
d_{IJ}=\Re(\eta a_{I^c}b_J).
\tag{2}
\]
The determinant expansion and complementary-minor identity give
\[
\Re(\eta F(W))
=\Re\!\left[\eta(a_{[4]}+b_{[4]})\right]
+\sum_{ij}c_{ij}|W_{ij}|^2
+\sum_{I,J}d_{IJ}|\det W[I,J]|^2.
\tag{3}
\]

These are **not arbitrary costs**:

* before taking real parts, \(c=\alpha b^T+a\beta^T\) has complex rank at most two;
* before taking real parts, \(d=(a_{I^c})_I(b_J)_J^T\) has complex rank one;
* all coefficients come from the same \(a,b,\eta\).

For \(S\in SU(3)\), abbreviate
\[
r_{ij}=y_i^TSy_j,\qquad
x_{IJ}=p_I^TSp_J,\qquad
t_{IJ}=q_I^TSq_J.
\]

---

## 3. Exact elimination of the scalar phase

Write
\[
V=\zeta S,\qquad |\zeta|=1,\quad S\in SU(3).
\]
Then \(\det V=\zeta^3\). In (1), the interference term becomes
\[
2\Re\!\left(\overline{\det V}\,x_{IJ}(V)t_{IJ}(V)\right)
=2\Re\!\left(\zeta^{-1}x_{IJ}t_{IJ}\right).
\]
Thus only a **first harmonic** remains.

Define
\[
C_0=\Re\!\left[\eta(a_{[4]}+b_{[4]})\right]
+\frac1{16}\sum_{ij}c_{ij},
\]
\[
\mathcal A(S)
=C_0+\sum_{ij}c_{ij}|r_{ij}|^2
+\sum_{I,J}d_{IJ}\bigl(|x_{IJ}|^2+|t_{IJ}|^2\bigr),
\tag{4}
\]
and
\[
\mathcal B(S)
=\frac12\sum_{ij}c_{ij}r_{ij}
+2\overline{\sum_{I,J}d_{IJ}x_{IJ}t_{IJ}}.
\tag{5}
\]
Then
\[
\boxed{
\Re\!\left[\eta F(W(\zeta S))\right]
=\mathcal A(S)+\Re\bigl(\zeta\mathcal B(S)\bigr).
}
\tag{6}
\]
In particular,
\[
\boxed{
\max_{|\zeta|=1}\Re\!\left[\eta F(W(\zeta S))\right]
=\mathcal A(S)+|\mathcal B(S)|.
}
\tag{7}
\]

The cube-root ambiguity causes no problem: replacing \(S\) by \(\omega S\), \(\omega^3=1\), preserves \(\mathcal A\) and multiplies \(\mathcal B\) by \(\omega\).

Let the **original** permutation height be
\[
h=h_\eta(a,b)
=\max_{\pi\in S_4}\Re\!\left[\eta\prod_{i=1}^4(a_i+b_{\pi(i)})\right].
\tag{8}
\]
Unrestricted MOC4 is therefore equivalent to
\[
\boxed{\mathcal A(S)+|\mathcal B(S)|\le h
\quad\text{for every }S\in SU(3),\ a,b,\eta.}
\tag{9}
\]

No new comparison products have entered.

---

## 4. Hadamard symmetry simplifies the interference coefficient

This is a useful additional computation beyond the exterior decomposition.

Define
\[
\rho(a)=\frac14
\begin{pmatrix}
(a_1-a_3)(a_2-a_4)\\
-(a_1-a_2)(a_3-a_4)\\
-(a_1-a_4)(a_2-a_3)
\end{pmatrix},
\]
\[
\kappa(a)=\frac14
\begin{pmatrix}
a_1a_3-a_2a_4\\
a_1a_2-a_3a_4\\
a_1a_4-a_2a_3
\end{pmatrix}.
\tag{10}
\]
Notice
\[
\mathbf1^T\rho(a)=0.
\tag{11}
\]

For the cross-block
\[
M_a=\sum_I a_{I^c}p_Iq_I^T,
\]
direct expansion gives
\[
\boxed{M_a=\operatorname{diag}\rho(a)+[\kappa(a)]_\times,}
\tag{12}
\]
where \([k]_\times x=k\times x\). The corresponding \(b_J\)-weighted block is
\[
\sum_Jb_Jp_Jq_J^T
=\operatorname{diag}\rho(b)-[\kappa(b)]_\times.
\tag{13}
\]

Thus the symmetric parts are already diagonal; a generic Takagi reduction is unnecessary here.

For \(S\in SU(3)\),
\[
S[k]_\times S^T=[\overline S k]_\times.
\]
The symmetric/skew cross terms have zero trace. Consequently,
\[
\sum_{I,J}a_{I^c}b_Jx_{IJ}t_{IJ}
=
\sum_{u,v}\rho_u(a)\rho_v(b)S_{uv}^{\,2}
-2\kappa(a)^T\overline S\,\kappa(b).
\tag{14}
\]

Set
\[
E=\Re\!\left[\eta\,\rho(a)\rho(b)^T\right],\qquad
K=\Re\!\left[\eta\,\kappa(a)\kappa(b)^T\right],
\]
\[
L=\frac12Y^TcY-4K.
\tag{15}
\]
All three matrices are real. Equations (5) and (14) yield
\[
\boxed{
\mathcal B(S)
=\sum_{u,v}L_{uv}S_{uv}
+2\sum_{u,v}E_{uv}\overline{S_{uv}}^{\,2}.
}
\tag{16}
\]
Moreover,
\[
\operatorname{rank}_{\mathbb R}E\le2,\qquad
E\mathbf1=E^T\mathbf1=0.
\tag{17}
\]

So the residual interference is not a generic quadratic polynomial: it is a linear functional plus an entry-square functional with a zero-sum, rank-at-most-two coefficient matrix.

### Exact matrix-SOS target

Equation (9) is equivalent to
\[
\boxed{
\mathcal M(S):=
\begin{pmatrix}
h-\mathcal A(S)&\mathcal B(S)\\
\overline{\mathcal B(S)}&h-\mathcal A(S)
\end{pmatrix}\succeq0
\quad(S\in SU(3)).
}
\tag{18}
\]
Its entries have real degree at most two in \(S\). Equivalently, one must prove
\[
h-\mathcal A(S)\ge0,\qquad
\bigl(h-\mathcal A(S)\bigr)^2-|\mathcal B(S)|^2\ge0
\tag{19}
\]
on \(S^*S=I,\det S=1\), **with (2), (10), and (15) retained**. The second inequality is quartic.

This is the exact remaining positivity obligation.

---

## 5. A closed positive-law lemma on 24 phase circles

There is a tractable subfamily with a complete answer.

Put
\[
W_\zeta=ee^T+\zeta(I-ee^T),\qquad
H_0=W_{-1}=2ee^T-I,
\]
and
\[
\lambda=\frac{1-\Re\zeta}{2}.
\]
For every grade of squared minors,
\[
\boxed{
R(W_\zeta)=(1-\lambda)R(I)+\lambda R(H_0).
}
\tag{20}
\]

For example, at grade two:

* \(I=J\): the squared minor is \(1-\lambda\);
* \(|I\cap J|=1\): it is \(\lambda/4\);
* \(I\cap J=\varnothing\): it is zero.

At grade one, the diagonal and off-diagonal values are
\[
1-\frac{3\lambda}{4},\qquad \frac{\lambda}{4}.
\]
Grade three follows by complementation.

The profile of \(H_0\) is the uniform average of the permutation profiles of the **eight 3-cycles**. Indeed, each singleton matching has probability \(1/4\), and a two-set is mapped uniformly onto its four overlapping two-sets.

Writing
\[
z_\pi=\prod_i(a_i+b_{\pi(i)}),
\]
we obtain the exact identity
\[
\boxed{
F(W_\zeta)
=(1-\lambda)z_{\mathrm{id}}
+\frac{\lambda}{8}
 \sum_{\sigma\text{ a 3-cycle}}z_\sigma.
}
\tag{21}
\]

Right multiplication by any permutation matrix gives the same conclusion on each circle
\[
W_\zeta P_\pi.
\]
Thus MOC4 holds, with explicit spectrum-independent positive weights, on **24 entire phase circles** in the balanced family.

This proves (9) on those circles. It does not justify extending the conclusion to arbitrary \(S\).

---


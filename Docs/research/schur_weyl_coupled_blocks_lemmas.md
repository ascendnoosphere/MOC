## 1. Exact tensor identity and collective commutation

Let \(\mathcal H=(\mathbb C^2)^{\otimes4}\), with subset basis
\[
|I\rangle=\bigotimes_{i=1}^4
\begin{cases}
(0,1)^T,&i\in I,\\
(1,0)^T,&i\notin I.
\end{cases}
\]
Then
\[
x(a)=\bigotimes_i(a_i,1)^T,\qquad
y(b)^T=\bigotimes_i(1,b_i),
\]
have coordinates
\[
x_I=a_{I^c},\qquad y_J=b_J.
\]
All pairings below are **bilinear transposes**, not Hermitian pairings.

Define
\[
D_U[J,I]=
\begin{cases}
|\det U[I,J]|^2,&|I|=|J|,\\
0,&\text{otherwise}.
\end{cases}
\]
The principal-minor expansion followed by Cauchy–Binet gives
\[
\boxed{\det(D_a+UD_bU^*)=y(b)^TD_Ux(a).}
\tag{1}
\]

Choose \(P_\pi|I\rangle=|\pi(I)\rangle\). Then
\[
\boxed{y^TP_\pi x=\prod_i(a_i+b_{\pi(i)}).}
\tag{2}
\]

### The commutation assertion is true

Let \(L_k\) be the unsigned incidence matrix from \(k\)-subsets to \((k+1)\)-subsets:
\[
L_k[K,I]=\mathbf1_{I\subset K}.
\]
These are the grade components of the collective raising operator.

The squared-minor marginal identity gives
\[
\boxed{D_{k+1}L_k=L_kD_k.}
\tag{3}
\]
Entrywise, for \(|J|=k+1\), \(|I|=k\), this is
\[
\sum_{\substack{K\supset I\\|K|=k+1}}
|\det U[K,J]|^2
=
\sum_{\substack{H\subset J\\|H|=k}}
|\det U[I,H]|^2.
\tag{4}
\]
Both sides equal the appropriate principal minor of the rank-\((k+1)\) projection formed from the columns \(J\). This is the determinantal marginal/Cauchy–Binet identity—not an assumed common-permutation law.

Applying the same identity to \(U^*\) supplies commutation with collective lowering. Grade preservation supplies commutation with the Cartan generator. Hence
\[
\boxed{[D_U,g^{\otimes4}]=0\quad(g\in SL_2(\mathbb C)).}
\tag{5}
\]

Schur–Weyl duality therefore places \(D_U\) in
\[
\mathcal A
=\operatorname{End}_{SL_2}(\mathcal H)
\cong \mathbb C\oplus M_3(\mathbb C)\oplus M_2(\mathbb C).
\]
Indeed,
\[
\mathcal H\cong
V_2\otimes\mathbb C
\;\oplus\;
V_1\otimes\mathbb C^3
\;\oplus\;
V_0\otimes\mathbb C^2,
\]
with dimensions \(5+9+2=16\), and
\[
\dim_{\mathbb C}\mathcal A=1+9+4=14.
\]

**Nothing here implies operator positivity.** Actual permutation unitaries already give \(D_U=P_\pi\), including non-Hermitian cycles and transpositions with negative eigenvalues.

---

## 2. Explicit blocks

Order pairs as \(12,13,14,23,24,34\). Fix
\[
Y=\frac12
\begin{pmatrix}
1&1&1\\
1&-1&-1\\
-1&1&-1\\
-1&-1&1
\end{pmatrix},
\qquad YY^T=I-\frac14J_4.
\]
Let
\[
R_{I,j}=\mathbf1_{j\in I},\qquad
R^TR=2I_4+J_4,
\]
and choose the residual basis
\[
Z=
\begin{pmatrix}
\frac12&\frac1{2\sqrt3}\\
-\frac12&\frac1{2\sqrt3}\\
0&-\frac1{\sqrt3}\\
0&-\frac1{\sqrt3}\\
-\frac12&\frac1{2\sqrt3}\\
\frac12&\frac1{2\sqrt3}
\end{pmatrix}.
\]
Thus
\[
Z^TZ=I_2,\qquad R^TZ=0.
\]

Write
\[
B_U[J,I]=|U[I,J]|^2,\qquad |I|=|J|=1,
\]
so \(B_U=(|U|^{\circ2})^T\), and set
\[
A_3(U)=Y^TB_UY,\qquad A_2(U)=Z^TD_{U,2}Z.
\]
The exact grade decompositions are
\[
\boxed{D_{U,1}=\frac14J_4+YA_3(U)Y^T,}
\tag{6}
\]
\[
\boxed{
D_{U,2}
=\frac16J_6+
\frac12RYA_3(U)Y^TR^T+
ZA_2(U)Z^T.
}
\tag{7}
\]
Grade three is grade one under complementation; grades zero and four are \(1\).

Thus the scalar Schur block is fixed at \(1\), while the remaining data are a **coupled** pair \((A_3(U),A_2(U))\).

---

## 3. Exact spectral coefficients \(C_3,C_2\)

For \(t\in\mathbb C^4\), define
\[
v(t)=Y^Tt,
\qquad
q(t)=Y^T(t_{234},t_{134},t_{124},t_{123})^T,
\]
and
\[
w(t)=\frac1{\sqrt2}Y^T
\bigl(t_i(e_1(t)-t_i)\bigr)_{i=1}^4.
\]
Define also
\[
r(t)=
\begin{pmatrix}
\dfrac{(t_1-t_4)(t_2-t_3)}2\\[2mm]
\dfrac{(t_1-t_3)(t_2-t_4)+(t_1-t_2)(t_3-t_4)}
{2\sqrt3}
\end{pmatrix}.
\]

Then
\[
\boxed{
c_0(a,b)=
\sum_{k=0}^4
\frac{e_{4-k}(a)e_k(b)}{\binom4k},
}
\tag{8}
\]
\[
\boxed{
C_3(a,b)=q(a)v(b)^T-w(a)w(b)^T+v(a)q(b)^T,
}
\tag{9}
\]
\[
\boxed{C_2(a,b)=r(a)r(b)^T.}
\tag{10}
\]
With the convention \(\operatorname{tr}(CA)\), the full determinant is
\[
\boxed{
F_U=c_0+\operatorname{tr}(C_3A_3(U))
             +\operatorname{tr}(C_2A_2(U)).
}
\tag{11}
\]

The minus sign in (9) matters: complementation acts as \(-1\) on the grade-two standard component, but as \(+1\) on \(\ker R^T\).

### Complete preservation of product linkage

These formulas do not allow independent choices of \(C_3,C_2,c_0\). A complete, denominator-free presentation of the inherited product constraints is
\[
\boxed{
x_{[4]}=1,\qquad
x_I=\prod_{i\notin I}x_{[4]\setminus\{i\}},
}
\tag{12}
\]
\[
\boxed{
y_\varnothing=1,\qquad
y_J=\prod_{j\in J}y_{\{j\}}.
}
\tag{13}
\]
Together with the fixed linear projections above, these characterize **exactly** the coefficient tuples coming from the specified affine product vectors. Conversely, recover
\[
a_i=x_{[4]\setminus\{i\}},\qquad b_j=y_{\{j\}}.
\]
No nonvanishing assumption is needed.

Equations (8)–(10) are an explicit eight-complex-parameter parametrization of those linked coefficients. They are **not** a claim that their elimination ideal in coefficient coordinates has been computed.

In particular:

* \(C_2\) has complex rank at most one, but is generally neither Hermitian nor positive.
* \(C_3\) is a sum of three linked outer products.
* Replacing these matrices by unrelated costs discards essential constraints.
* Neither \(y=\bar x\) nor a positive-state interpretation has been introduced.

For support phase \(\eta\), the original obligation is exactly
\[
\Re\!\left[\eta\bigl(
\operatorname{tr}(C_3A_3(U))+
\operatorname{tr}(C_2A_2(U))
\bigr)\right]
\le
\max_{\pi\in S_4}\Re\!\left[\eta\bigl(
\operatorname{tr}(C_3\rho_3(\pi))+
\operatorname{tr}(C_2\rho_2(\pi))
\bigr)\right].
\tag{14}
\]
The same \(\pi\) occurs in both terms on the right.

---


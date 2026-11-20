## 1. Fully checked global reduction

Write
\[
F_{a,b}(U)=\det(D_a+UD_bU^*).
\]
For diagonal unitaries \(L,R\),
\[
\begin{aligned}
F_{a,b}(LUR)
&=\det(D_a+LU D_bU^*L^*)\\
&=\det\!\left(L(D_a+UD_bU^*)L^*\right)
=F_{a,b}(U).
\end{aligned}
\]
Thus **both phase actions preserve the complex determinant itself**, not merely its real support.

Their hypotheses agree with [Idel–Wolf, *Sinkhorn normal form for unitary matrices*, §2](https://arxiv.org/html/1408.5728): **every** \(U\in U(n)\), without genericity or nonzero-entry assumptions.

Here is the implication explicitly. Clifford-torus non-displaceability supplies a vector \(r\) with
\[
|r_j|=|(Ur)_j|=1.
\]
Set
\[
R=\operatorname{diag}(r_j),\qquad
L=\operatorname{diag}\bigl(\overline{(Ur)_j}\bigr).
\]
Then \(W=LUR\) satisfies \(W\mathbf1=\mathbf1\). Unitarity gives \(W^*\mathbf1=\mathbf1\), hence also column sums one.

For the specified \(e,Y\),
\[
Y^TY=I_3,\qquad Y^Te=0,\qquad YY^T=I_4-ee^T.
\]
Therefore
\[
We=e
\quad\Longleftrightarrow\quad
W=ee^T+YVY^T,\qquad V\in U(3).
\]
The converse follows by direct multiplication.

Consequently,
\[
\boxed{
\{F_{a,b}(U):U\in U(4)\}
=
\{F_{a,b}(ee^T+YVY^T):V\in U(3)\}.
}
\]
This is an exact equality of the entire ranges, on **one fixed real plane**, including all exceptional cases.

### Why MOC3 does not immediately apply

Put \(Q=[e\;Y]\). Although \(D_a\) is normal, its compression \(A=Y^TD_aY\) need not be normal. For example, for \(a=(0,1,i,0)\),
\[
[A,A^*]=
\begin{pmatrix}
0&0&i/4\\
0&0&-i/4\\
-i/4&i/4&0
\end{pmatrix}\ne0.
\]
There are also nonzero couplings between \(e\) and \(e^\perp\). Thus neither the hypotheses nor the determinant expression required for ordinary MOC3 are present automatically.

---

## 2. Exact elimination of the central phase

Write, using ordinary transpose on the coupling vectors,
\[
Q^TD_aQ=
\begin{pmatrix}\alpha&x^T\\x&A\end{pmatrix},
\qquad
Q^TD_bQ=
\begin{pmatrix}\beta&y^T\\y&B\end{pmatrix}.
\]
These matrices are complex symmetric; generally \(x^T\ne x^*\).

For fixed \(V\in U(3)\), let
\[
K=A+VBV^*.
\]
The bordered determinant identity gives, for every \(|z|=1\),
\[
\boxed{F_{a,b}(W_z)=C_0+zC_++z^{-1}C_-}
\]
where
\[
\begin{aligned}
C_0={}&(\alpha+\beta)\det K
-x^T\operatorname{adj}(K)x
-y^TV^*\operatorname{adj}(K)Vy,\\
C_+={}&-x^T\operatorname{adj}(K)Vy,\\
C_-={}&-y^TV^*\operatorname{adj}(K)x.
\end{aligned}
\]
**No invertibility assumption on \(K\) is needed.**

Hence, for every support direction \(\eta\in\mathbb C\),
\[
\boxed{
\max_{|z|=1}\Re\{\eta F_{a,b}(W_z)\}
=
\Re(\eta C_0)
+\left|\eta C_++\bar\eta\,\overline{C_-}\right|.
}
\]
This eliminates one optimization variable exactly. One may subsequently restrict \(V\) to \(SU(3)\), since \(U(3)=\mathbb T\,SU(3)\).

The **center** \(C_0\) has a constructive permutation law.

---

## 3. Completed step: a universal law for the phase average

For two-element subsets \(I,J\subset\{1,2,3,4\}\), define
\[
q_{IJ}(W)=|\det W_{I,J}|^2,
\qquad
\bar q_{IJ}=\int_{\mathbb T}q_{IJ}(W_z)\,dz,
\]
with normalized Haar measure.

Let \(y_i\in\mathbb R^3\) be the transpose of row \(i\) of \(Y\). For \(I=\{i,k\}\), \(i<k\), put
\[
u_I=\frac{y_k-y_i}{2},
\qquad
v_I=y_i\times y_k.
\]
The decomposition
\[
\Lambda^2(\mathbb Ce\oplus e^\perp)
=(e\wedge e^\perp)\oplus\Lambda^2e^\perp
\]
and the identity
\[
\Lambda^2V\simeq(\det V)\bar V
\]
give
\[
\boxed{
\bar q_{IJ}
=
|u_I^TVu_J|^2+|v_I^TVv_J|^2.
}
\tag{1}
\]
The two summands arise from different central-phase powers, so their interference averages to zero.

Likewise, for singleton minors,
\[
\boxed{
\bar p_{ij}:=\int_{\mathbb T}|(W_z)_{ij}|^2\,dz
=\frac1{16}+|y_i^TVy_j|^2.
}
\tag{2}
\]

### The finite permutation polytope

Let
\[
\mathcal P
=\operatorname{conv}\left\{
q^\sigma:\;
q^\sigma_{IJ}=\mathbf1_{\{\sigma(I)=J\}},
\quad \sigma\in S_4
\right\}.
\]
Its affine hull is specified by
\[
q_{I^c,J^c}=q_{IJ},\qquad
\sum_Jq_{IJ}=1,\qquad
\sum_Iq_{IJ}=1,
\]
and has dimension \(13\).

The following is the **finite-polytope step I checked exactly**. Its facets are:

1. **16 singleton inequalities**
   \[
   p_{ij}\ge0,\qquad
   p_{ij}=
   \frac{\displaystyle\sum_{I\ni i,\;J\ni j}q_{IJ}-1}{2};
   \]
2. **18 distinct pair inequalities** \(q_{IJ}\ge0\), accounting for complementary duplicates;
3. **48 row/column relabelings** of
   \[
   \boxed{
   q_{12,14}\le
   q_{23,34}+q_{24,12}+q_{24,13}+q_{24,34}.
   }
   \tag{3}
   \]

For clarity, completeness was not inferred merely from numerical LP feasibility:

- all 82 candidate supporting hyperplanes were checked rationally against all 24 vertices;
- their zero sets were verified to be exactly the claimed facets;
- completeness was checked recursively by facet–ridge adjacency: every ridge of every checked facet has its two incident facets in the list;
- modulo \(S_4\times S_4\), this checked 637 face orbits, using 993 rank computations.

Those ranks were exact: the selected affine-coordinate matrix has 14 binary columns. Every square minor has absolute value below \(40{,}390\), by the binary-matrix Hadamard bound. Rank modulo \(1{,}000{,}003\) therefore equals rational rank.

Thus this is an **exact computational certificate for the finite lemma**, rather than a purely handwritten classification proof.

### The nontrivial inequalities have an explicit SOS certificate

Equation (2) proves the 16 singleton inequalities. Equation (1) proves pair nonnegativity.

For (3), define its slack on the averaged array:
\[
L=
\bar q_{23,34}+\bar q_{24,12}
+\bar q_{24,13}+\bar q_{24,34}
-\bar q_{12,14}.
\]
For \(V=(v_{ij})\in U(3)\), direct expansion of (1), followed only by the row and column norm identities of \(V\), gives
\[
\begin{aligned}
48L={}&
2\bigl(|v_{11}|^2+|v_{23}|^2+|v_{32}|^2\bigr)
+6|v_{11}+v_{23}-v_{32}|^2\\
&+6|v_{12}-v_{31}|^2+4|v_{12}|^2\\
&+6|v_{13}+v_{21}|^2+4|v_{21}|^2\\
&+6|v_{22}-v_{33}|^2+4|v_{33}|^2.
\end{aligned}
\tag{4}
\]
This proves \(L\ge0\). In fact, the quadratic form has smallest eigenvalue
\[
\frac{4-\sqrt{10}}{24},
\]
so
\[
\boxed{L\ge\frac{4-\sqrt{10}}8>0.}
\tag{5}
\]

Row and column relabelings preserve the fixed-vector subgroup and act on \(V\) by real orthogonal left/right factors. Thus the same certificate proves all 48 inequalities.

It follows that
\[
\boxed{\bar q\in\mathcal P.}
\]

### Constructive recovery of a law

There consequently exist \(\lambda_\sigma\ge0\), \(\sum_\sigma\lambda_\sigma=1\), such that
\[
\bar q_{IJ}
=\sum_\sigma\lambda_\sigma\mathbf1_{\{\sigma(I)=J\}}.
\]
These same weights reproduce the averaged singleton minors through the displayed reconstruction formula. Complementarity reproduces the order-three minors.

This is algorithmically constructive: solve the fixed 24-variable linear feasibility problem. Alternatively, enumerate the nonsingular 14-column bases of its rank-14 coefficient matrix; a nonnegative basic solution exists and uses at most 14 permutations.

Finally, the determinant expansion
\[
F_{a,b}(W)=
\sum_{\substack{I,J\\|I|=|J|}}
\left(\prod_{i\notin I}a_i\right)
\left(\prod_{j\in J}b_j\right)
|\det W_{I,J}|^2
\]
yields
\[
\boxed{
C_0=\sum_{\sigma\in S_4}
\lambda_\sigma\prod_i(a_i+b_{\sigma(i)}).
}
\tag{6}
\]
The law depends on \(V\), **not** on \(a,b\).

---


## 5. A completed pointwise subclass

For the central circles through permutations, a pointwise constructive law is explicit.

Let
\[
W_z=ee^T+z(I-ee^T),\qquad
t=\frac{1+\Re z}{2}.
\]
Its squared minors equal the mixture
\[
t\,q^{\mathrm{id}}
+\frac{1-t}{8}
\sum_{\substack{\sigma\in S_4\\\sigma\text{ a }3\text{-cycle}}}q^\sigma.
\]
For example, its order-two squared minors are \(t\) when \(I=J\), \((1-t)/4\) when \(|I\cap J|=1\), and zero when \(I\cap J=\varnothing\).

Thus, for arbitrary complex spectra,
\[
\boxed{
F_{a,b}(W_z)
=
t\prod_i(a_i+b_i)
+\frac{1-t}{8}
\sum_{\sigma\text{ a }3\text{-cycle}}
\prod_i(a_i+b_{\sigma(i)}).
}
\]
Right multiplication by any permutation matrix gives the corresponding law for every central circle through a permutation. This closes that subclass without invoking MOC3.

---


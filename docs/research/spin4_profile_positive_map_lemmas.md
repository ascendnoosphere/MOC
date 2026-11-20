## 1. Independent validation of the profile theorem

I read the requested documents, including all of `organized/extracted/volume_sections/N013.txt`. Its central argument is sound.

### Real effect decomposition

Let
\[
E_1,E_2,E_3\in\operatorname{Sym}_3(\mathbb R),\qquad
E_i\succeq0,\quad \operatorname{tr}E_i=1,\quad \sum_iE_i=I.
\]

If all ranks are at least two, their supported symmetric perturbation spaces have total dimension at least \(3+3+3=9\). The constraints
\[
\sum_iH_i=0,\qquad \operatorname{tr}H_i=0
\]
have rank at most eight: six sum equations and only two additional independent trace equations. Thus a nonzero supported perturbation exists.

If additionally every rank is at most two, either:

* some \(E_i\) already has rank one; or
* all ranks are two, and both endpoints of a maximal supported PSD perturbation interval have a rank-one effect.

The interval is bounded because trace-one PSD matrices form a bounded set. At an endpoint, rank must drop; trace one excludes rank zero.

A rank-one effect is a projection \(P\). The other effects are supported on \(P^\perp\), sum to its identity, and have eigenvalue lists
\[
(\theta,1-\theta),\qquad(1-\theta,\theta).
\]
They are therefore a mixture of two orthogonal rank-one projection pairs. Combining the two perturbation endpoints gives **at most four bases**.

This verifies the dimension count and endpoint argument in `organized/extracted/volume_sections/N013.txt:71–104`.

### Why this preserves every grade

After column dephasing, make the first row of \(U\) a real unit vector \(v\). For each other transposed row \(x_i\), set
\[
E_i=\Re(x_ix_i^*).
\]
These are trace-one real PSD effects of rank at most two on \(v^\perp\), summing to its identity.

Their common basis decomposition preserves:

* singleton squares, through \((E_i)_{jj}\);
* two-minor squares containing the fixed row, through
  \[
  |x_{ij}v_k-x_{ik}v_j|^2
  =(v_ke_j-v_je_k)^TE_i(v_ke_j-v_je_k);
  \]
* remaining two-minors by complementary-minor equality;
* three-minors by complementation to singletons;
* grades zero and four automatically.

These are precisely the necessary checks in `organized/extracted/volume_sections/N013.txt:107–178`.

No nonzero-entry assumption is needed: choose arbitrary dephasing at zero entries. Flipping a nonfixed row converts each orthogonal summand to determinant \(+1\), preserving its fixed row and every squared minor.

Consequently,
\[
\boxed{
|\det U[I,J]|^2=\sum_{s=1}^{m}\lambda_s|\det O_s[I,J]|^2,
\quad m\le4,\quad O_s\in SO(4).
}
\]

Finally,
\[
\det(D_a+UD_bU^*)
=\sum_{|I|=|J|}a_{I^c}b_J|\det U[I,J]|^2
\]
transfers the same mixture to determinants for **all** \(a,b\in\mathbb C^4\). Thus the reduction to real orthogonals is proved—not merely suggested.

### Source check

Oszmaniec–Guerini–Wittek–Acín, [arXiv:1609.06139](https://arxiv.org/abs/1609.06139), Lemma 7, states that the extreme trace-one, three-outcome qutrit measurements are orthonormal rank-one projective measurements. The real proof above independently establishes the version actually needed here.

---

## 2. Explicit Spin(4) parametrization

Identify \(\mathbb R^4\) with quaternions in the basis \(1,i,j,k\). For unit quaternions
\[
p=(p_0,p_1,p_2,p_3),\qquad q=(q_0,q_1,q_2,q_3),
\]
define
\[
U(p,q)x=p\,x\,\bar q.
\]
Its matrix is
\[
\boxed{U(p,q)=L(p)R(\bar q)}
\]
where
\[
L(p)=
\begin{pmatrix}
p_0&-p_1&-p_2&-p_3\\
p_1&p_0&-p_3&p_2\\
p_2&p_3&p_0&-p_1\\
p_3&-p_2&p_1&p_0
\end{pmatrix},
\]
\[
R(\bar q)=
\begin{pmatrix}
q_0&q_1&q_2&q_3\\
-q_1&q_0&-q_3&q_2\\
-q_2&q_3&q_0&-q_1\\
-q_3&-q_2&q_1&q_0
\end{pmatrix}.
\]

Quaternion norm multiplicativity proves orthogonality. Connectedness gives determinant \(+1\).

For completeness, coverage can be seen without assuming it: given \(O\in SO(4)\), let \(u=O(1)\). Then \(L(\bar u)O\) fixes \(1\), so restricts to an \(SO(3)\) rotation of the imaginary quaternions. Write that rotation as \(x\mapsto r x\bar r\). Hence
\[
O(x)=(ur)x\bar r.
\]
Thus every \(SO(4)\) matrix occurs. The kernel is \((1,1),(-1,-1)\).

### Exterior-square coordinates

Order coordinate two-forms as \(12,13,14,23,24,34\). Let \(B\) have columns
\[
\frac{e_{12}+e_{34}}{\sqrt2},\
\frac{e_{13}-e_{24}}{\sqrt2},\
\frac{e_{14}+e_{23}}{\sqrt2},\
\frac{e_{12}-e_{34}}{\sqrt2},\
\frac{e_{13}+e_{24}}{\sqrt2},\
\frac{e_{14}-e_{23}}{\sqrt2}.
\]

Define
\[
A(p)=
\begin{pmatrix}
p_0^2+p_1^2-p_2^2-p_3^2&2(p_1p_2-p_0p_3)&2(p_1p_3+p_0p_2)\\
2(p_1p_2+p_0p_3)&p_0^2-p_1^2+p_2^2-p_3^2&2(p_2p_3-p_0p_1)\\
2(p_1p_3-p_0p_2)&2(p_2p_3+p_0p_1)&p_0^2-p_1^2-p_2^2+p_3^2
\end{pmatrix}.
\]
Then
\[
\boxed{\bigwedge\nolimits^2U(p,q)=B\operatorname{diag}(A(p),A(q))B^T.}
\tag{1}
\]

I verified the stronger, unrestricted polynomial identity
\[
\bigwedge\nolimits^2(L(p)R(\bar q))
=B\operatorname{diag}(\|q\|^2A(p),\|p\|^2A(q))B^T
\tag{2}
\]
by expanding all 36 entries exactly.

---

## 3. Exact actual-spectral support gap

Fix arbitrary complex spectra \(a,b\) and \(|\eta|=1\). Keep
\[
z_\pi=\prod_{i=1}^4(a_i+b_{\pi(i)}),\qquad
h=\max_{\pi\in S_4}\Re(\eta z_\pi).
\]
There are **no additional comparison products**.

Write
\[
C=\Re\!\left[\eta(a_{[4]}+b_{[4]})\right],
\]
\[
c_{ij}
=\Re\!\left[\eta\left(a_{[4]\setminus i}b_j+
a_i b_{[4]\setminus j}\right)\right],
\qquad
d_{IJ}=\Re(\eta a_{I^c}b_J).
\]
With
\[
K(p,q)=B\operatorname{diag}(A(p),A(q))B^T,
\]
the exact gap is
\[
\boxed{
G(p,q)=h-C-\sum_{ij}c_{ij}U_{ij}(p,q)^2
-\sum_{\substack{|I|=2\\|J|=2}}d_{IJ}K_{IJ}(p,q)^2.
}
\tag{3}
\]

This follows directly by combining grades one and three using complementary minors, and using (1) for grade two.

The unrestricted target is precisely
\[
G(p,q)\ge0\qquad(p,q\in S^3).
\tag{4}
\]

An exact homogeneous extension is useful for degree auditing. Set \(s=\|p\|^2,t=\|q\|^2\), and let \(\widetilde K\) denote the right side of (2). Then
\[
\widehat G
=(h-C)s^2t^2-st\sum c_{ij}U_{ij}^2-\sum d_{IJ}\widetilde K_{IJ}^2.
\tag{5}
\]
It has real bidegree \((4,4)\), and for nonzero \(p,q\),
\[
\widehat G=s^2t^2G(p/\sqrt s,q/\sqrt t).
\]
At either zero quaternion it vanishes polynomially. No spectral divisions occur anywhere.

---


## 5. A closed inequality with a genuine \(M_2\to M_2\) map

There is nevertheless an exact positive-map certificate on a concrete Spin(4) subfamily.

Suppose \(O\) preserves the coordinate planes \(12\) and \(34\), with rotation angles \(\theta,\phi\). Define
\[
x=\sin^2\theta,\qquad y=\sin^2\phi,
\]
\[
u=(a_1+b_1)(a_2+b_2),\quad
v=(a_1+b_2)(a_2+b_1),
\]
\[
r=(a_3+b_3)(a_4+b_4),\quad
s=(a_3+b_4)(a_4+b_3).
\]
The two block determinants give
\[
\boxed{
F(O)=((1-x)u+xv)((1-y)r+ys).
}
\tag{7}
\]

The four products \(ur,vr,us,vs\) are exactly the original permutation products for
\[
\mathrm{id},\quad(12),\quad(34),\quad(12)(34).
\]
Let their support gaps be \(g_{00},g_{10},g_{01},g_{11}\), respectively. Each is nonnegative **by the definition of the same 24-product height \(h\)**.

Define, on the full complex matrix algebra,
\[
\boxed{
\Phi(X)=
\begin{pmatrix}
g_{00}X_{11}+g_{10}X_{22}&0\\
0&g_{01}X_{11}+g_{11}X_{22}
\end{pmatrix}.
}
\tag{8}
\]

This map is explicitly complex-linear. If \(X\succeq0\), its diagonal entries are nonnegative, so \(\Phi(X)\succeq0\). In fact it is completely positive, with Kraus matrices
\[
\sqrt{g_{\sigma\tau}}\,|\tau\rangle\langle\sigma|,
\qquad \sigma,\tau\in\{0,1\}.
\]

For real unit spinors
\[
\xi=(\cos\theta,\sin\theta)^T,\qquad
\upsilon=(\cos\phi,\sin\phi)^T,
\]
equations (7)–(8) yield the exact identity
\[
\boxed{
h-\Re(\eta F(O))
=\upsilon^*\Phi(\xi\xi^*)\upsilon\ge0.
}
\tag{9}
\]

Thus this is an actual positive-map argument: domain, complex-linearity, positivity, and polynomial equality are all established.

It includes Spin pairs
\[
p=\cos\alpha+i\sin\alpha,\qquad
q=\cos\beta+i\sin\beta,
\]
whose two plane angles are \(\alpha-\beta,\alpha+\beta\), as well as coordinate-permuted versions. It covers arbitrary complex spectra, repeated entries, vanishing entries, collapsed permutation polygons, and endpoint rotations without continuity arguments.

It does **not** cover arbitrary quaternion factors.

---


## 1. The missing lower-right stationarity equations

Retain the source notation
\[
E=A_0+S,\quad R=E^{-1},\quad
L=QE^{-1},\quad M=E^{-1}V,
\]
\[
c=\frac{a_1+a_2}{2},\quad d=\frac{a_1-a_2}{2},\quad
\gamma=\eta\det E,\quad \tau=\gamma d.
\]

Move the \(12\) rotation onto \(A\), writing its upper block as
\[
Z=cI+dN,\qquad N=N^*,\quad \operatorname{tr}N=0,\quad N^2=I.
\]
Set \(H=Z+T\). The lower-right adjugate block is
\[
\boxed{
(\operatorname{adj}(A(N)+B))_{22}
=\det E\bigl(\det H\,R+M\operatorname{adj}(H)L\bigr).
}
\tag{1}
\]
This follows from the block inverse formula and remains valid at singular \(H\) by polynomial continuation.

Actual global maximality makes every point of the exact plateau stationary—not merely the original point. This is the source’s maximizer-specific principle at `organized/research/branch_A_maximizer_geometry.md:120–124`.

### A quantitative two-orientation identity

Put
\[
q=t_1-t_2,\qquad
h_0=a_1a_2+t_1t_2+c(t_1+t_2).
\]
At \(N=\pm\operatorname{diag}(1,-1)\),
\[
D_+=\det H=h_0-dq,\qquad D_-=\det H=h_0+dq.
\]
Flatness says
\[
\Re(\gamma dq)=0.
\]
Consequently
\[
r:=\Im(\gamma dq)\ne0,\qquad h=\Re(\gamma h_0).
\tag{2}
\]

Under (NE), the established crossstationarity gives each row of \(L\), and its paired column of \(M\), support at at most one external label. Moreover their supports agree and their corresponding entries have equal modulus.

Therefore, at both diagonal orientations,
\[
M\operatorname{adj}(H)L
\]
is diagonal: each summand is an outer product supported at a single external diagonal entry.

Write \(\delta=a_4-a_3\ne0\). Hermiticity of
\(\eta[\operatorname{adj}(A(N)+B),A(N)]\), restricted to its \(34\) entries, now gives
\[
\boxed{
\gamma\delta D_\pm R_{34}
+\bar\gamma\bar\delta\,\overline{D_\pm}\,
\overline{R_{43}}=0.
}
\tag{3}
\]

The determinant of these two equations, as a system in
\((R_{34},\overline{R_{43}})\), is exactly
\[
\begin{aligned}
&|\gamma\delta|^2
 \bigl(D_+\overline{D_-}-D_-\overline{D_+}\bigr)\\
&\hspace{2cm}
=4i|\gamma\delta|^2\Im(h_0\overline{dq})
=\boxed{-4i|\delta|^2rh}.
\end{aligned}
\tag{4}
\]

This is the new quantitative face statement.

### Consequences

If \(h\ne0\), equation (4) forces
\[
R_{34}=R_{43}=0,
\]
so \(E\) is diagonal.

Using
\[
Q=LE,\qquad V=EM,\qquad P=T+LEM,
\tag{5}
\]
the singleton-support pattern then gives:

- different external supports: a \(2+2\) coordinate reducing decomposition;
- the same external support: a \(3+1\) decomposition;
- a zero coupling row: a common coordinate eigenvector.

Hence:

\[
\boxed{\text{Every nonendpoint distinct-\(t\) flat maximum of nonzero height is already reducible.}}
\]

Subtracting the two equations (3), whether or not \(h=0\), also yields
\[
\boxed{\delta R_{34}=\bar\delta\,\overline{R_{43}}.}
\tag{6}
\]

No positivity inference from the mixed normality equation is being made here.

---

## 2. At height zero, different external supports are impossible

Suppose \(h=0\). By (2), both \(\gamma h_0\) and \(\gamma dq\) are purely imaginary, so
\[
\frac{h_0}{dq}\in\mathbb R.
\]
Equivalently,
\[
\frac{(a_1+t_1)(a_2+t_2)}
     {(a_2+t_1)(a_1+t_2)}
\in\mathbb R.
\tag{7}
\]
Under (NE), all four factors are nonzero. Equation (7) says that
\[
a_1,\ a_2,\ -t_1,\ -t_2
\]
lie on one generalized circle \(\Gamma\).

If a coupling row vanishes, (5) already gives a reducing coordinate. Assume both rows are nonzero.

The established resonance condition says:

- row \(1\) supported at \(k\) implies \(-t_2\) lies on the circle through \(a_1,a_2,a_k\);
- row \(2\) supported at \(k\) implies the same statement for \(-t_1\).

Because neither effective eigenvalue is an endpoint, these circles must equal \(\Gamma\). If the two rows used different external labels, \(\Gamma\) would contain all four \(a_i\), contrary to hypothesis.

Thus the only remaining pattern is, after possibly interchanging \(3,4\),
\[
\boxed{
L=\begin{pmatrix}\ell_1&0\\ \ell_2&0\end{pmatrix},
\qquad
M=\begin{pmatrix}m_1&m_2\\0&0\end{pmatrix},
\qquad \ell_1\ell_2\ne0,
}
\tag{8}
\]
where
\[
a_1,a_2,a_3,-t_1,-t_2\in\Gamma,\qquad a_4\notin\Gamma.
\]

If \(E\) is diagonal, this already gives a \(3+1\) block. It remains to treat nondiagonal \(E\).

---

## 3. Möbius normalization preserves the exact coupling pattern

The useful normalization is to send \(\Gamma\) to the real line. Its admissibility must be checked because ordinary affine normalization cannot generally do that.

Choose
\[
\phi(z)=\frac{\alpha z+\beta}{\chi z+\omega},
\qquad k=\alpha\omega-\beta\chi\ne0,
\]
mapping \(\Gamma\) to \(\mathbb R\cup\{\infty\}\). Choose its pole away from the finite set
\[
\{a_i,-t_1,-t_2\}\cup\sigma(-B).
\]
Define
\[
A'=\phi(A),\qquad B'=-\phi(-B).
\]
Both remain normal, and \(B'\) varies over a unitary orbit when \(B\) does.

The exact identity
\[
(\chi A+\omega I)(A'+B')(\omega I-\chi B)
=k(A+B)
\]
gives
\[
\det(A'+B')=\kappa\det(A+B),
\]
where
\[
\kappa=
\frac{k^4}{\det(\chi A+\omega I)\det(\omega I-\chi B)}
\]
is nonzero and constant on the orbit. Taking
\[
\eta'=\eta/\kappa
\]
preserves the support objective **exactly for every unitary conjugate**.

Here are the Schur-coordinate transformation formulas. With
\[
J=\omega I-\chi T,\qquad R_0=\chi A_0+\omega I,
\]
one obtains
\[
\boxed{
T'=(\alpha T-\beta I)J^{-1},\quad
L'=J^{-1}LR_0,\quad M'=R_0MJ^{-1}.
}
\tag{9}
\]
Also,
\[
\det E'
=\frac{k^2\det E\det J}
       {\det R_0\det(\omega I-\chi B)}
\ne0.
\tag{10}
\]

Thus \(T'\) stays diagonal and distinct, and the singleton-support pattern (8) survives. In particular, this normalization does not discard an inherited constraint.

Since \(T'=-\phi(-T)\), we now have
\[
a'_1,a'_2,a'_3,t'_1,t'_2\in\mathbb R,\qquad
a'_4\notin\mathbb R.
\]

For the following calculation, drop primes.

---

## 4. Full normality now forces a Hermitian model

In these normalized coordinates, \(d,q\) are nonzero real numbers. Flatness therefore makes \(\gamma\) purely imaginary.

For the supported external label \(3\), both crossstationarity coefficients \(f_{\mu3},g_{\mu3}\) are real. They cannot vanish simultaneously: if
\(f_{\mu3}=0\), then
\[
g_{\mu3}=(a_1-a_3)(a_2-a_3)\ne0.
\]
The two established crossstationarity equations consequently imply
\[
\boxed{M=L^*.}
\tag{11}
\]

Write
\[
E=\begin{pmatrix}e&u\\v&f\end{pmatrix},\qquad
x=(\ell_1,\ell_2,1)^T,\qquad
D=\operatorname{diag}(t_1,t_2,-a_3).
\]
Then the **entire normal matrix**, grouped as \(123\mid4\), is
\[
B=
\begin{pmatrix}
C&ux\\
vx^*&s
\end{pmatrix},
\qquad
C=D+exx^*,\qquad s=f-a_4.
\tag{12}
\]

The \(44\) normality equation gives
\[
|u|=|v|.
\tag{13}
\]
Hence the upper-left normality equation reduces to
\[
[C,C^*]=0.
\]
But
\[
[C,C^*]=(\bar e-e)[D,xx^*].
\]
Because \(t_1\ne t_2\) and \(\ell_1\ell_2\ne0\),
\([D,xx^*]\ne0\). Therefore \(e\in\mathbb R\), and \(C\) is Hermitian.

The remaining cross normality equation becomes
\[
(\bar v-u)Cx+(u\bar s-\bar v s)x=0.
\tag{14}
\]
The vectors \(Cx\) and \(x\) are linearly independent: otherwise \(Dx\) would be proportional to \(x\), contradicting \(t_1\ne t_2\). Thus
\[
u=\bar v.
\]
Since we are in the nondiagonal-\(E\) case, \(u\ne0\), so (14) also gives \(s\in\mathbb R\).

We have proved
\[
\boxed{B=B^*}
\]
in the normalized problem.

### An exact spectral collision

Put
\[
\Delta=\det E,\qquad \delta=a_4-a_3.
\]
Using \(v=\bar u\), equation (6) becomes
\[
\frac{\delta}{\Delta}\in\mathbb R.
\]
But
\[
\Delta=e(s+a_4)-|u|^2
=e\delta+\underbrace{e(s+a_3)-|u|^2}_{\text{real}}.
\]
Since \(\delta\notin\mathbb R\), this forces
\[
\boxed{|u|^2=e(s+a_3),\qquad \Delta=e\delta.}
\tag{15}
\]
In particular \(e\ne0\).

Now
\[
z=(0,0,u,-e)^T
\]
satisfies, directly from (12)–(15),
\[
\boxed{Bz=-a_3z.}
\tag{16}
\]

Undoing the Möbius transformation preserves this spectral collision:
\[
-a_3\in\sigma(B)
\]
also in the original coordinates.

---

## 5. Execute the second flat transport

It remains to show that rotating \(z\) to a coordinate vector preserves the support—not merely that the eigenvector exists.

Write
\[
a_4=\alpha_4+i\beta_4,\qquad \beta_4\ne0,\qquad
\eta=p+iq.
\]
Since \(\gamma=\eta\Delta\) is purely imaginary and \(\Delta=e(a_4-a_3)\), equation (15) gives
\[
p(\alpha_4-a_3)-q\beta_4=0.
\tag{17}
\]

For every Hermitian \(X\) on the orbit of \(B\), determinant affinity in the fourth diagonal entry yields
\[
\boxed{
\Re\{\eta\det(A+X)\}
=p\det\bigl(\operatorname{diag}(a_1,a_2,a_3,a_3)+X\bigr).
}
\tag{18}
\]
Indeed, writing \(A_r=\operatorname{diag}(a_1,a_2,a_3,\alpha_4)\), the left side is
\[
p\det(A_r+X)-q\beta_4\det(A_r+X)_{\widehat4,\widehat4},
\]
and (17) replaces \(q\beta_4\) by \(p(\alpha_4-a_3)\).

The right side of (18) is invariant under **every** coordinate \(34\) rotation, because its diagonal matrix is scalar on those coordinates.

Choose such a rotation \(W\) with
\[
Wz=\|z\|e_3.
\]
Then
\[
WBW^*e_3=-a_3e_3.
\]
Normality makes this a reducing coordinate. The support has remained constant along the entire rotation.

Finally, Möbius functional calculus commutes with unitary conjugation. Therefore this same \(W\) gives an exact support-preserving transport in the original problem as well.

**There is no iterative sparsification argument here:** after the initial \(12\) diagonalization, at most one additional \(34\) rotation is needed.

---


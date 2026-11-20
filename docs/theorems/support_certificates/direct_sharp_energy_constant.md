# The optimized energy constant is exactly sharp on actual spectral data

Direct track, campaign 3. The underlying determinant case is elementary and
already belongs to a settled rank-one spectral class. Its role here is an
exact equality model for the proposed universal optimized energy inequality.
No novelty claim is made for MOC in this special spectral class.

## 1. A single assignment deficit is an actual spectral support

For any \(n\ge2\), let

\[
a=(1,0,\ldots,0),\qquad b=(1,2,1,\ldots,1),\qquad\eta=1.
\]

Writing \(v=Ue_2\), the determinant is

\[
\begin{aligned}
\det(D_a+UD_bU^*)
 &=\det(I+e_1e_1^*+vv^*)\\
 &=\det\begin{pmatrix}2&e_1^*v\\v^*e_1&2\end{pmatrix}
 =4-|U_{12}|^2.
\end{aligned}
\tag{1}
\]

The permutation support height is \(h=4\), attained at the identity, and
the complete support deficit is \(g(U)=|U_{12}|^2\).

For a complex isometry \(Y:\mathbb C^2\to\mathbb C^n\), put
\(P=YY^*\), \(L(T)=y_1Ty_2^*\), \(d=\det T\), and
\(V(T)=(I+iT)(I-iT)^{-1}\). The exact two-by-two adjugate identity gives

\[
V(T)-I=\frac{2(iT+dI)}{1-d-i\operatorname{tr}T}.
\]

Thus

\[
\boxed{
g\bigl(I+Y(V(T)-I)Y^*\bigr)\det(I+T^2)
=4|L(T)-idP_{12}|^2.
}
\tag{2}
\]

In the convention of the spectral energy budget,

\[
\mathcal A(T)=|L(T)|^2,\qquad
\ell(T)=4\Im\{L(T)\overline{P_{12}}\},\qquad
g(R)=4|P_{12}|^2.
\tag{3}
\]

## 2. Equality of the optimized budget

Regard \(L\) as a real-linear map from Hermitian two-by-two matrices to
\(\mathbb C\), with its usual two-dimensional real inner product. The
covector \(\ell/4\) is represented by the target \(iP_{12}\). Its minimum
representation energy is the squared norm of the orthogonal projection
of that target onto \(\operatorname{image}L\).

If the two rows \(y_1,y_2\) are complex-linearly independent, \(L\) is onto
\(\mathbb C\). Indeed choose a basis sending the first row to \((r,0)\),
with \(r>0\), and write the second as \((u,v)\) with \(v\ne0\). The
off-diagonal entry of a Hermitian \(T\) is an arbitrary complex number,
and its coefficient in \(L(T)\) is nonzero. Therefore

\[
\boxed{
\frac14\ell^T\mathcal A^+\ell=4|P_{12}|^2=g(R).
}
\tag{4}
\]

When \(P_{12}\ne0\), the energy ratio is exactly one. Consequently no
universal inequality of the form
\(\frac14\ell^T\mathcal A^+\ell\le\kappa g(R)\) can hold with
\(\kappa<1\), even for these real spectra. The proposed unrestricted
constant one is optimal if the inequality is true.

## 3. An entirely rational order-four equality example

Take

\[
K=\begin{pmatrix}1&0\\0&1\\1&-1\\-2&1\end{pmatrix},\quad
G=K^*K=\begin{pmatrix}6&-3\\-3&3\end{pmatrix},\quad
G^{-1}=\begin{pmatrix}1/3&1/3\\1/3&2/3\end{pmatrix}.
\]

The isometry is \(Y=KG^{-1/2}\), but the projection is rational:

\[
P=KG^{-1}K^*,\qquad
R=I-2P=\frac13
\begin{pmatrix}
1&-2&0&2\\-2&-1&2&0\\0&2&1&2\\2&0&2&-1
\end{pmatrix}.
\]

Use raw Hermitian coordinates
\(S=\left(\begin{smallmatrix}s&x+iy\\x-iy&t\end{smallmatrix}\right)\)
and \(T=G^{1/2}SG^{1/2}\). Then

\[
L(T)=x+iy,\qquad d=9\det S,\qquad P_{12}=1/3,
\]

so

\[
\mathcal A=\operatorname{diag}(0,0,1,1),\quad
\ell=(0,0,0,4/3)^T,\quad g(R)=4/9.
\tag{5}
\]

These exact quantities satisfy (4). The whole numerator identity is

\[
\boxed{
g(U)\bigl[(1-9\det S)^2+(6s+3t-6x)^2\bigr]
=4\bigl[x^2+(y-3\det S)^2\bigr].
}
\tag{6}
\]

The denominator is the squared modulus of
\(\det(I-iGS)\) and cannot vanish for Hermitian \(S\), because \(GS\) is
similar to a Hermitian matrix. Formula (6) is a direct all-parameter
identity, not a conclusion from evaluations at finitely many points.

The sharper proposed chirality metric also saturates here. For the
permutation deficit \(g_\pi=\mathbf1_{\{\pi(1)=2\}}\), in dimensions at
least three one can choose a three-cycle with \(g_\pi=1\) and
\(g_{\pi^{-1}}=0\). Hence

\[
\chi=\max_\pi
\frac{|c_\pi-c_{\pi^{-1}}|}{2h-c_\pi-c_{\pi^{-1}}}=1,
\qquad \rho=\chi^2=1.
\]

Zero denominators are assigned ratio zero, as both corresponding
nonnegative deficits vanish. This equality example does not prove the
proposed \(\rho\le\chi^2\) bound for other spectra.

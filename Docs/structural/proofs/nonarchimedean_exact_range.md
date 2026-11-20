# An exact determinant-range theorem over a non-Archimedean valued field

Let \(K\) be a field with a multiplicative non-Archimedean absolute value. Write

\[
\mathcal O=\{x\in K:|x|\le1\}
\]

for its valuation ring. No completeness, local compactness, or discrete valuation is required.

For diagonal matrices

\[
A=\operatorname{diag}(a_1,\ldots,a_n),\qquad
B=\operatorname{diag}(b_1,\ldots,b_n)
\]

over \(K\), define

\[
z_\pi=\prod_{j=1}^n(a_{\pi(j)}+b_j),\qquad \pi\in S_n.
\]

The similarity action in this note is \(UBU^{-1}\), not \(UBU^*\). The allowed conjugators are \(\operatorname{GL}_n(\mathcal O)\), namely matrices over the valuation ring whose determinants are units of that ring.

## Exact range theorem

Fix any permutation vertex \(z_0\), and put

\[
R=\max_{\pi\in S_n}|z_\pi-z_0|.
\]

Then

\[
\boxed{
\left\{\det(A+UBU^{-1}):U\in\operatorname{GL}_n(\mathcal O)\right\}
=\{x\in K:|x-z_0|\le R\}.
}
\tag{1}
\]

The same equality holds with \(\operatorname{SL}_n(\mathcal O)\) in place of \(\operatorname{GL}_n(\mathcal O)\).

Thus the determinant range is exactly the smallest closed ultrametric ball containing the permutation vertices. If all vertices coincide, this ball and the determinant range are singletons.

### Proof of the upper inclusion

For any invertible \(U\), not yet assumed integral,

\[
(A+UBU^{-1})U=AU+UB=((a_i+b_j)U_{ij})_{i,j}.
\]

Expanding its determinant gives the algebraic identity

\[
\det(A+UBU^{-1})=\sum_{\pi\in S_n}c_\pi(U)z_\pi,\qquad
c_\pi(U)=\frac{\operatorname{sgn}(\pi)\prod_jU_{\pi(j),j}}{\det U}.
\tag{2}
\]

The determinant expansion for \(U\) itself shows

\[
\sum_\pi c_\pi(U)=1.
\tag{3}
\]

If \(U\in\operatorname{GL}_n(\mathcal O)\), then \(c_\pi(U)\in\mathcal O\), so \(|c_\pi(U)|\le1\). Therefore, for every \(w\in K\),

\[
\boxed{
\left|\det(A+UBU^{-1})-w\right|
\le\max_\pi|z_\pi-w|.
}
\tag{4}
\]

Indeed, subtract \(w\) using (3) and apply the ultrametric inequality to the sum in (2). Taking \(w=z_0\) proves the upper inclusion in (1). Taking \(w=0\) gives the uncentered estimate

\[
|\det(A+UBU^{-1})|
\le\max_\pi\prod_j|a_{\pi(j)}+b_j|.
\tag{5}
\]

### Proof that every point of the ball occurs

Assume \(R>0\). The graph on \(S_n\) joining permutations that differ by a transposition is connected. The ultrametric inequality applied along any path in this graph shows that

\[
\max_{\pi,\sigma}|z_\pi-z_\sigma|
=\max_{\pi,\sigma\text{ adjacent}}|z_\pi-z_\sigma|.
\tag{6}
\]

The left side equals \(R\). Thus some transposition edge has endpoints \(z_\alpha,z_\beta\) with

\[
|z_\alpha-z_\beta|=R.
\]

Let \(P_\alpha\) be the permutation matrix defined by \(P_\alpha e_j=e_{\alpha(j)}\). The adjacent permutation \(\beta\) swaps two of the resulting assignments, in row positions \(r,s\).

On these two row coordinates, embed

\[
G(t)=
\begin{pmatrix}
1&1\\
t&1+t
\end{pmatrix},
\qquad t\in\mathcal O,
\tag{7}
\]

and use the identity on the other coordinates. Since \(\det G(t)=1\), the resulting \(U(t)=G(t)P_\alpha\) belongs to \(\operatorname{GL}_n(\mathcal O)\).

A direct two-by-two determinant expansion, with all unaffected diagonal factors carried along, gives

\[
\det(A+U(t)BU(t)^{-1})
=(1+t)z_\alpha-tz_\beta
=z_\alpha+t(z_\alpha-z_\beta).
\tag{8}
\]

As \(t\) ranges over \(\mathcal O\), the right side ranges over

\[
z_\alpha+(z_\alpha-z_\beta)\mathcal O
=\{x\in K:|x-z_\alpha|\le R\}.
\]

This ball equals the ball centered at \(z_0\) of radius \(R\), because both centers lie in it. Explicitly, a desired point \(x\) is obtained by taking

\[
t=\frac{x-z_\alpha}{z_\alpha-z_\beta}\in\mathcal O.
\]

If \(R=0\), (2) and (3) already give the constant value \(z_0\).

Finally, every \(U\in\operatorname{GL}_n(\mathcal O)\) can be replaced by

\[
U D,\qquad D=\operatorname{diag}((\det U)^{-1},1,\ldots,1).
\]

The diagonal matrix \(D\) belongs to \(\operatorname{GL}_n(\mathcal O)\), commutes with \(B\), and makes \(\det(UD)=1\). The conjugated matrix and its determinant are unchanged. Hence the special-linear and general-linear ranges coincide. This proves (1).

## The coefficient interpretation

For a finite subset \(Z=\{z_\pi\}\subset K\), define explicitly its \(\mathcal O\)-affine hull by

\[
\operatorname{Aff}_{\mathcal O}(Z)=
\left\{\sum_\pi c_\pi z_\pi:
c_\pi\in\mathcal O,\ \sum_\pi c_\pi=1\right\}.
\tag{9}
\]

For \(z_0\in Z\), this is

\[
z_0+\sum_\pi\mathcal O(z_\pi-z_0).
\]

A difference \(\Delta=z_\pi-z_0\) with maximal absolute value generates this finitely generated ideal: every other difference divided by \(\Delta\) lies in \(\mathcal O\). Consequently (9) equals the smallest closed ultrametric ball containing \(Z\), including the singleton case.

Thus (1) can also be written as equality of the determinant range with the explicitly defined \(\mathcal O\)-affine hull. This terminology does not assert a unique canonical meaning of “p-adic convex hull.” The coefficient condition is membership in the valuation ring, not real nonnegativity.

The distinction from ordinary complex convexity is essential. A valuation ring is closed under addition, so bounded coefficients with sum one suffice for (4). Over the complex numbers, the corresponding disk-bounded coefficients need not be nonnegative real probabilities and do not imply convex-hull membership.

## Sharpness

For every \(w\in K\),

\[
\max_{U\in\operatorname{GL}_n(\mathcal O)}
|\det(A+UBU^{-1})-w|
=\max_\pi|z_\pi-w|,
\]

since permutation matrices are allowed. The stronger theorem (1) describes the whole range, not only this maximum.


## Exact small examples

For \(A=B=\operatorname{diag}(0,1)\) and \(U=G(t)\),

\[
\det(A+UBU^{-1})=-t.
\]

Therefore the entire range over \(\operatorname{GL}_2(\mathbb Z_p)\) is \(\mathbb Z_p\), exactly the smallest \(p\)-adic ball containing \(0,1\).

For an order-three example over \(\mathbb Q_3\), take

\[
A=\operatorname{diag}(0,1,2),\qquad
B=\operatorname{diag}(0,1,3).
\]

The six permutation vertices, including repetitions, are \(0,0,5,8,9,12\). Their smallest 3-adic ball is \(\mathbb Z_3\). Mixing the first two row coordinates with \(G(t)\) gives

\[
\det(A+G(t)BG(t)^{-1})=-5t.
\]

Since 5 is a 3-adic unit, this single family fills \(\mathbb Z_3\).

The accompanying exact_examples.py verifies these formulas using fractions and integer valuations only.

## Consequences over Gaussian rationals

Let \(K=\mathbb Q(i)\), with the valuation associated to a Gaussian prime. For any fixed \(U\in\operatorname{GL}_n(K)\), one has

\[
U\in\operatorname{GL}_n(\mathcal O_{\mathfrak p})
\]

for all but finitely many prime ideals \(\mathfrak p\). Indeed, only finitely many primes occur in denominators of entries of \(U\) or in the numerator and denominator of \(\det U\). Consequently (4) and (5) hold at all remaining places.

If \(v_{\mathfrak p}\) is the additive valuation, the centered form says

\[
v_{\mathfrak p}(d-z_0)
\ge\min_\pi v_{\mathfrak p}(z_\pi-z_0),
\tag{10}
\]

at every place where \(U\) is integrally invertible. This can provide genuine divisibility or congruence information.

There is a ring-level version that requires no valuation. If \(A,B\) have diagonal entries in \(\mathbb Z[i]\) and \(U\in\operatorname{GL}_n(\mathbb Z[i])\), then (2) and (3) imply

\[
d-z_0\in (\,z_\pi-z_0:\pi\in S_n\,)\subseteq\mathbb Z[i].
\tag{11}
\]

Because the Gaussian integers form a principal ideal domain, if \(g\) is a greatest common divisor of the vertex differences, then \(d\equiv z_0\pmod g\). With finitely many primes inverted, the same statement holds in the corresponding localization. This is an arithmetic affine-combination statement, not a complex convexity statement.

For fixed nonzero values, the almost-everywhere valuation assertion is often trivial: away from their finitely many prime divisors and denominators, all relevant nonzero quantities have absolute value one. The useful information is at specific primes where the centered vertex differences have positive valuation and \(U\) remains integrally invertible.


## Scope

The exact range theorem is a valid all-dimensions valued-field analogue, proved by explicit affine determinant coefficients and elementary two-coordinate transformations. Its reverse inclusion depends crucially on the ultrametric inequality and the availability of general integral similarities.

It does not establish real nonnegative permutation weights for complex normal matrices, does not replace \(UBU^{-1}\) by a p-adic adjoint action, and does not solve the Archimedean Marcus–de Oliveira conjecture. No claim of publication novelty is made.

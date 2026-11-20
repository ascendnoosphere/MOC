# Exact determinant ranges over finite adeles

This note concerns diagonal matrices and similarity conjugation. It does not assume a spectral theorem for arbitrary matrices called normal over a non-Archimedean field. The finite adeles form a commutative ring, not a field.

Write

\[
\mathbb A_f=\prod_p'\mathbb Q_p,\qquad
\widehat{\mathbb Z}=\prod_p\mathbb Z_p,
\]

where a tuple belongs to \(\mathbb A_f\) precisely when its coordinates are integral at all but finitely many primes. Let \(A=\operatorname{diag}(a_i)\), \(B=\operatorname{diag}(b_j)\) have entries in \(\mathbb A_f\), and put

\[
f(U)=\det(A+UBU^{-1}),\qquad
z_\pi=\prod_j(a_{\pi(j)}+b_j).
\]

Fix one vertex \(z_0\), and let

\[
J=\sum_{\pi\in S_n}\widehat{\mathbb Z}(z_\pi-z_0)
\subseteq\mathbb A_f.
\]

## The two exact range theorems

The finitely generated \(\widehat{\mathbb Z}\)-module \(J\) is principal: there is \(\delta\in\mathbb A_f\) with \(J=\delta\widehat{\mathbb Z}\). More explicitly, at each prime choose a vertex difference of greatest \(p\)-adic absolute value and use that difference for \(\delta_p\); if every difference vanishes, set \(\delta_p=0\).

Then

\[
\boxed{
f\!\left(\prod_p\operatorname{GL}_n(\mathbb Z_p)\right)
=f\!\left(\prod_p\operatorname{SL}_n(\mathbb Z_p)\right)
=z_0+\delta\widehat{\mathbb Z}.
}
\tag{1}
\]

For unrestricted invertible adelic matrices,

\[
\boxed{
f(\operatorname{GL}_n(\mathbb A_f))
=f(\operatorname{SL}_n(\mathbb A_f))
=z_0+\delta\mathbb A_f.
}
\tag{2}
\]

Formula (1) is exactly the product of the local closed balls

\[
\prod_p\left\{x_p\in\mathbb Q_p:
|x_p-z_{0,p}|_p\le\max_\pi|z_{\pi,p}-z_{0,p}|_p\right\}.
\tag{3}
\]

This product lies in \(\mathbb A_f\): its coordinates are integral at almost every prime. It is compact with its inherited finite-adelic topology, including cases where some local balls are singletons. Formula (2), by contrast, can be a nonclosed proper affine ideal.

### Proof

Over any commutative ring and any invertible matrix \(U\),

\[
(A+UBU^{-1})U=AU+UB=((a_i+b_j)U_{ij})_{ij}.
\]

The determinant expansion consequently gives

\[
f(U)=\sum_\pi c_\pi(U)z_\pi,
\qquad
c_\pi(U)=\frac{\operatorname{sgn}(\pi)\prod_jU_{\pi(j),j}}{\det U},
\qquad \sum_\pi c_\pi(U)=1.
\tag{4}
\]

For integral invertible adelic \(U\), these coefficients belong to \(\widehat{\mathbb Z}\). For general invertible adelic \(U\), they belong to \(\mathbb A_f\). This proves the upper inclusions in (1) and (2), once \(J\) is identified.

Because only finitely many vertex differences occur, all of them are integral outside a fixed finite set of primes. Hence the coordinatewise selected \(\delta\) is an adele. Each quotient \((z_\pi-z_0)/\delta\), defined to be zero at a coordinate where \(\delta_p=0\), belongs to \(\widehat{\mathbb Z}\). Conversely, partition the primes according to the chosen vertex difference. The characteristic functions of these finitely many sets are idempotents in \(\widehat{\mathbb Z}\); multiplying the corresponding differences by these idempotents and adding gives \(\delta\). Thus \(J=\delta\widehat{\mathbb Z}\).

For the lower inclusions, consider the connected graph of permutations with edges given by transpositions. At each prime, the ultrametric triangle inequality along graph paths implies that some edge has vertex distance equal to the diameter of all vertices. Select such an edge with endpoints \(z_{\alpha_p,p},z_{\beta_p,p}\), whenever this diameter is nonzero. At a zero-diameter coordinate use any edge if \(n\ge2\); the case \(n=1\) is already constant.

Let \(c_p=z_{\alpha_p,p}\) and \(\epsilon_p=z_{\alpha_p,p}-z_{\beta_p,p}\). These selections are among finitely many adelic entries, so define adeles \(c,\epsilon\). We have

\[
c-z_0=\delta b\quad(b\in\widehat{\mathbb Z}),\qquad
\epsilon=\delta u\quad(u\in\widehat{\mathbb Z}^{\times}).
\]

For the second relation choose \(u_p=\epsilon_p/\delta_p\) at nonzero coordinates and \(u_p=1\) at zero coordinates.

Given a desired \(x=z_0+\delta a\), set \(t=u^{-1}(a-b)\). Then \(t\in\widehat{\mathbb Z}\) if \(a\in\widehat{\mathbb Z}\), and \(t\in\mathbb A_f\) if \(a\in\mathbb A_f\). On the two row coordinates of the selected transposition, use

\[
G(t_p)=\begin{pmatrix}1&1\\t_p&1+t_p\end{pmatrix},
\qquad \det G(t_p)=1,
\]

and set \(U_p=G(t_p)P_{\alpha_p}\), with the identity on other row coordinates. Direct expansion gives

\[
f(U)_p=(1+t_p)z_{\alpha_p,p}-t_pz_{\beta_p,p}
=c_p+\epsilon_pt_p=x_p.
\]

The resulting matrix is integral invertible at every prime in case (1), and at almost every prime in case (2); hence it is an allowed adelic matrix. Finally, right multiplication by

\[
\operatorname{diag}((\det U)^{-1},1,\ldots,1)
\]

preserves \(UBU^{-1}\), since the factor commutes with diagonal \(B\), and changes the determinant of \(U\) to one. The correcting factor belongs to the same ring. This proves both equalities.

## Rational spectra: a rational gcd controls the compact range

Suppose all \(a_i,b_j\) are rational, diagonally embedded in \(\mathbb A_f\). Choose a positive integer \(D\) so that every \(D(z_\pi-z_0)\) is an integer, and let

\[
g=\gcd_\pi D(z_\pi-z_0),\qquad r=g/D\ge0.
\]

The choice of \(D\) does not affect \(r\). Formula (1) becomes

\[
f\!\left(\prod_p\operatorname{SL}_n(\mathbb Z_p)\right)
=z_0+r\widehat{\mathbb Z}.
\tag{5}
\]

If \(r>0\), then \(r\) is an invertible finite adele, so (2) gives the whole ring \(\mathbb A_f\). If \(r=0\), the determinant is identically \(z_0\). Thus unrestricted adelic similarities have a complete singleton-or-everything dichotomy for rational diagonal spectra.

A rational matrix belongs to \(\operatorname{GL}_n(\mathbb Z_p)\) for every prime exactly when it lies in \(\operatorname{GL}_n(\mathbb Z)\). Consequently any rational determinant obtained under these all-prime integral restrictions satisfies

\[
f(U)\in(z_0+r\widehat{\mathbb Z})\cap\mathbb Q=z_0+r\mathbb Z
\quad(r>0).
\tag{6}
\]

The last identity uses \(\mathbb Q\cap\widehat{\mathbb Z}=\mathbb Z\). It does not, by itself, prove that every rational point of this affine lattice is attained by one integer matrix.

If rational conjugators are unrestricted at finite primes, there is also a simple exact answer: when the rational vertices are nonconstant, \(f(\operatorname{SL}_n(\mathbb Q))=\mathbb Q\). Choose one unequal transposition edge and take its parameter \(t=(x-z_\alpha)/(z_\alpha-z_\beta)\in\mathbb Q\) for any desired \(x\in\mathbb Q\). The determinant correction in the proof remains rational. Thus arbitrary rational determinant values are attainable, but one rational matrix still yields a single diagonal rational value across all completions, rather than an arbitrary adelic tuple.

## Simultaneous integral approximation

For \(n\ge2\),

\[
\overline{\operatorname{SL}_n(\mathbb Z)}
=\prod_p\operatorname{SL}_n(\mathbb Z_p),
\tag{7}
\]

where the closure is taken in the product of the integral groups. Therefore, for the fixed diagonal adelic spectra above,

\[
\boxed{\overline{f(\operatorname{SL}_n(\mathbb Z))}
=z_0+\delta\widehat{\mathbb Z}.}
\tag{8}
\]

This means that a single determinant-one integer matrix can approximate any prescribed admissible determinant values at any finite set of primes, to any finite precision. It is a density statement, not exact simultaneous equality of all coordinates.

Here is a direct proof of the approximation fact. A neighborhood in the right side of (7) imposes finitely many matrix congruences modulo prime powers. By the Chinese remainder theorem they amount to a matrix in \(\operatorname{SL}_n(\mathbb Z/M\mathbb Z)\). Every such matrix is a product of elementary matrices:

* Over \(\mathbb Z/p^k\mathbb Z\), some entry of the first column is a unit. Determinant-one row exchanges move it to the top; row additions clear the remaining entries.
* The diagonal correction \(\operatorname{diag}(u,u^{-1})\) is elementary: writing \(E_{ij}(a)=I+a e_{ij}\), one has
  \[
  E_{12}(u)E_{21}(-u^{-1})E_{12}(u)
  \begin{pmatrix}0&-1\\1&0\end{pmatrix}
  =\operatorname{diag}(u,u^{-1}),
  \]
  and the displayed fixed matrix is itself a product of three elementary matrices.
* Induction clears the remaining block. Chinese-remainder idempotents place each local elementary factor in one prime-power component and the identity in the others.

Lifting each elementary parameter to an integer gives an exact determinant-one integer lift. This proves (7). The map \(f\) is continuous on the compact product of integral special-linear groups: there \(U^{-1}\) is its adjugate, so \(f\) is polynomial in the matrix entries with fixed adelic coefficients. Its image is compact and therefore closed in \(\mathbb A_f\). Applying continuity to (7) proves (8).

Keith Conrad's *SL(2,Z)*, Theorem 3.2, gives the corresponding surjectivity for order two; his later discussion states the all-order version. The proof above supplies the needed all-order argument explicitly. Source: https://kconrad.math.uconn.edu/blurbs/grouptheory/SL(2,Z).pdf


## Full adeles and the Archimedean place

The full rational adele ring is \(\mathbb A=\mathbb R\times\mathbb A_f\). If the real and finite conjugators are independently specified, their determinant ranges form a Cartesian product. For real diagonal spectra and unrestricted \(\operatorname{SL}_n(\mathbb R)\), the real range is a singleton when every real pairing vertex agrees, and otherwise all of \(\mathbb R\): a nonconstant transposition edge and the same \(G(t)\), now with \(t\in\mathbb R\), fill the real line. Combine this factor with (1) or (2), according to the finite restrictions.

If the real or complex group is instead restricted to orthogonal or unitary matrices, its range is a separate question. A finite-adelic factor does not prove the complex MOC inclusion at the Archimedean place.

A diagonal rational conjugator cannot choose its local components independently. In particular, \(\mathbb Q\) is discrete in the full adeles: the neighborhood

\[
(-1/2,1/2)\times\widehat{\mathbb Z}
\]

contains no nonzero rational number. For \(A=B=\operatorname{diag}(0,1)\), integer special-linear conjugators give exactly the diagonal integers as determinant values, whereas independent real and integral finite conjugators give \(\mathbb R\times\widehat{\mathbb Z}\). Finite-place density does not persist after adding simultaneous real approximation with integrality at every finite place.

For standard definitions and the discreteness assertion, see Kiran Kedlaya's *Notes on class field theory*, Section 6.1, especially Remark 6.1.8: https://kskedlaya.org/cft/sec_adeles.html

No global absolute value is being assigned to a general adele in these statements. An adele can have zero coordinates, and even a nonzero adele such as \((p)_p\) need not be invertible. The familiar finite product formula for nonzero rational numbers is not an ordinary absolute-value norm on this entire ring.

## Scope

These are exact determinant-range identities for diagonal inputs and specified similarity groups. They use affine modules and ideals, not real probability weights. They do not establish the original complex Marcus–de Oliveira conjecture, and no claim of publication novelty is made.

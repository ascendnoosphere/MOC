# Almost-sure coverage after a large scalar shift

This note records a distributional consequence of the all-unitary theorem in
`large_shift_all_U.md`. The qualitative theorem and its
critical variational steps have been independently audited by two other agents.
This is an informal mathematical audit, not machine-checked formal verification.
No claim of literature priority is made. No explicit shift threshold is asserted.

## 1. Deterministic theorem being used

For fixed \(n\geq3\), put

\[
 A(a)=\operatorname{diag}(a_1,\ldots,a_n),\qquad
 B(b)=\operatorname{diag}(b_1,\ldots,b_n),\qquad
 w_\pi(a,b)=\sum_{i=1}^n a_i b_{\pi(i)}.
\]

Call \((a,b)\) boundary regular when the convex hull of its trace-assignment
points \(w_\pi\) is two-dimensional, each vertex is produced by exactly one
permutation, and each edge contains exactly two permutation points, counting
permutations rather than just distinct point locations. Let \(\mathcal G\) be
the set of boundary-regular pairs.

The deterministic result is:

> For every \((a,b)\in\mathcal G\), there exists a finite \(R(a,b)\) such that,
> for every complex scalar \(s\) with \(|s|>R(a,b)\) and every \(U\in U(n)\),
> \[
> \det(sI+A(a)+UB(b)U^*)\in
> \operatorname{conv}\left\{
> \prod_{i=1}^n(s+a_i+b_{\pi(i)}):\pi\in S_n
> \right\}.
> \tag{1}
> \]

The order of quantifiers is essential: one radius controls every unitary and
every complex argument of \(s\). Equivalently, the MOC conclusion holds for the
shifted pair \((A(a)+sI,B(b))\). One can instead shift both matrices by \(s/2\).

## 2. Boundary regularity holds with probability one

In fact, outside a real-algebraic set of Lebesgue measure zero in
\(\mathbb C^{2n}\), all \(w_\pi\) are distinct and no three are collinear.
For \(n\geq3\), this stronger property implies boundary regularity.

Here is a proof that rules out an otherwise possible concern about unavoidable
assignment identities. For a permutation \(\pi\), let \(P_\pi\) have a one in
position \((i,\pi(i))\). Then

\[
w_\pi=a^T P_\pi b.
\]

For two distinct permutations \(\pi,\sigma\), the polynomial
\(a^T(P_\sigma-P_\pi)b\) is nonzero: its coefficient matrix is nonzero.
Thus equality of those two trace points is a proper real-algebraic condition.

For three distinct permutations, consider the real polynomial

\[
 F_{\pi\sigma\tau}(a,b)=
 \operatorname{Im}\left[
 (w_\sigma-w_\pi)\overline{(w_\tau-w_\pi)}
 \right].
 \tag{2}
\]

Suppose for contradiction that this polynomial vanished identically. On any
nonempty connected open subset on which \(w_\sigma-w_\pi\ne0\), the function

\[
 q(a,b)=\frac{w_\tau-w_\pi}{w_\sigma-w_\pi}
\]

would be both holomorphic and real-valued. Therefore it would be a real
constant \(c\). The identity theorem for polynomials would give

\[
 P_\tau-P_\pi=c(P_\sigma-P_\pi).
 \tag{3}
\]

Because \(\pi\ne\sigma\), there is an entry where \(P_\pi=0\) and
\(P_\sigma=1\). Equation (3) makes the corresponding entry of \(P_\tau\)
equal to \(c\), so \(c\in\{0,1\}\). Either value makes \(\tau\) equal to
\(\pi\) or \(\sigma\), a contradiction. Consequently (2) is a nonzero
real polynomial.

A nonzero real polynomial has a zero set of Lebesgue measure zero. There are
only finitely many pairs and triples of permutations. Their exceptional sets
therefore have a finite union of measure zero. Their complement is also open
and dense. In particular,

\[
 \mathbb P\bigl((a,b)\in\mathcal G\bigr)=1
 \tag{4}
\]

for every jointly absolutely continuous law of the \(2n\) complex spectral
coordinates. Independent coordinates, each having a density with respect to
two-dimensional Lebesgue measure, are a sufficient special case. Merely
assuming the individual coordinates have densities, while allowing arbitrary
dependence between them, would not be sufficient.

## 3. Distribution theorem: coverage tends to one

**Theorem.** Suppose the random spectral pair \((a,b)\) has a jointly absolutely
continuous law on \(\mathbb C^{2n}\), and \(Z\) is a complex random variable
with \(\mathbb P(Z=0)=0\). The variable \(Z\) may depend on \((a,b)\). For
real \(T>0\), let \(E_T\) be the event that (1) holds with \(s=TZ\),
simultaneously for all \(U\in U(n)\). Then

\[
 \boxed{\lim_{T\to\infty}\mathbb P(E_T)=1.}
 \tag{5}
\]

Consequently, for every \(\varepsilon>0\), there exists a deterministic finite
\(T_\varepsilon\) such that

\[
 \mathbb P(E_T)\geq1-\varepsilon
 \quad\text{for every }T\geq T_\varepsilon.
 \tag{6}
\]

**Proof.** With probability one, the spectral pair is boundary regular and
\(Z\ne0\). On each such outcome, the deterministic theorem supplies a finite
radius \(R(a,b)\), while \(|TZ|\to\infty\). Thus \(E_T\) holds for every
sufficiently large \(T\) on that outcome. Its indicator tends pointwise almost
surely to one. Dominated convergence proves (5), and the definition of the
limit gives (6).

For completeness, the event is measurable without making any measurable
selection of the radius \(R(a,b)\). Define

\[
\begin{aligned}
 \Phi(a,b,s)=\max_{U\in U(n),\,\theta\in[0,2\pi]}
 \biggl[&\operatorname{Re}\bigl(e^{-i\theta}
       \det(sI+A(a)+UB(b)U^*)\bigr)\\
 &-\max_{\pi\in S_n}\operatorname{Re}\biggl(
       e^{-i\theta}\prod_i(s+a_i+b_{\pi(i)})\biggr)\biggr].
\end{aligned}
\]

The maximized expression is continuous and its parameter set is compact, so
\(\Phi\) is continuous. Moreover, \(\Phi\geq0\), because the allowed
unitaries include all permutation matrices. The required inclusion for all
unitaries is equivalent to \(\Phi=0\), by separation of compact convex sets.
Hence \(E_T=\{\Phi(a,b,TZ)=0\}\) is measurable. \(\square\)

This statement includes independent standard complex Gaussian \(a_i,b_j,Z\).
For those variables, it gives eventual coverage exceeding one half, 90%, or
any prescribed number below 100%. It also includes the deterministic choice
\(Z=1\): the large center need not itself be random.

## 4. A radius uniform over compact sets of regular spectra

**Corollary.** For every compact \(K\subset\mathcal G\), there is one finite
\(R_K\) for which (1) holds for all \((a,b)\in K\), all \(|s|>R_K\), and all
unitaries \(U\).

This is slightly stronger than separately asserting existence of \(R(a,b)\).
To prove it, use the normalized determinant from the deterministic proof:

\[
 G_t(a,b,U)=
 \frac{\det(I+t(A(a)+UB(b)U^*))-c_{a,b}(t)}{t^2},
 \qquad
 G_0(a,b,U)=-\operatorname{tr}(A(a)UB(b)U^*),
\]

where \(c_{a,b}(t)\) comprises the three unitary-independent Taylor terms.
The extension at zero is polynomial in \(t\), and is jointly continuous in
\((a,b,t)\) in the \(C^2(U(n))\) topology.

Fix a base parameter \((a_0,b_0,\theta_0)\in K\times S^1\). Its leading
maximum set \(M\) is one permutation torus, two disjoint permutation tori, or
one block-unitary manifold with a single \(2\times2\) block. Its leading
normal Hessian is uniformly negative. Crucially, every nearby spectral pair
still has diagonal \(A(a)\) and \(B(b)\). At every point of the *same fixed*
manifold \(M\), the actual determinant is exactly stationary in every normal
direction, for all these nearby parameters, all \(t\), and all support angles.
Thus the compact maximum-stability argument applies uniformly in a product
neighborhood of \((a_0,b_0,\theta_0,0)\). Every maximum in that neighborhood
lies on \(M\), where the determinant is a vertex or an exact convex
combination of two vertices. A finite cover of \(K\times S^1\) supplies one
positive \(t\)-radius; its reciprocal supplies \(R_K\).

This is an existence statement. No effective estimate of \(R_K\), or of the
probabilistic threshold \(T_\varepsilon\), is supplied here.

## 5. Re-audit of the delicate deterministic steps

1. **No circular convex-weight assertion.** Birkhoff's theorem is used only
   for the leading trace functional, where its variables are the entries
   \(|U_{ij}|^2\). The determinant is treated by a genuine perturbation
   argument. On the only nontrivial surviving block, the required weights
   are the explicit \(2\times2\) mixing weights.

2. **No unsupported claim that a stationary point must commute.** The proof
   classifies global maxima of the limiting assignment functional and then
   excludes all points away from the resulting compact maximum manifolds.
   Other stationary points of the determinant play no role.

3. **Long assignment cycles cannot make a missing manifold.** If the only
   optimal permutations differ by one cycle of length at least three, an
   interior convex combination of their permutation matrices cannot equal
   \((|U_{ij}|^2)\). Consecutive cycle rows would overlap in exactly one
   nonzero column, violating orthogonality. Only the two permutation tori
   remain, and every transposition direction has a strict negative Hessian.

4. **Uniformity at an edge normal.** At a two-permutation transposition face,
   the whole \(U(2)\times U(1)^{n-2}\) manifold is retained when the support
   angle or spectra vary. A small tangential slope merely favors an
   endpoint; the transverse Hessian remains negative. The proof does not
   try to retain an endpoint's vanishing Hessian uniformly.

5. **Exact normal stationarity includes singular sums.** At a block point,
   \(A+UBU^*\) and its adjugate are block diagonal. A normal variation is
   \([K,UBU^*]\), which is off-block. The trace pairing is zero. The adjugate
   is a polynomial in the matrix, so no inverse or nonsingularity assumption
   is needed.

6. **The compact stability lemma uses normal geodesics.** The metric is the
   bi-invariant real Frobenius metric. Each maximum set is a finite disjoint
   union of compact smooth submanifolds. A tubular neighborhood gives normal
   geodesics with first derivative zero and uniformly negative second
   derivative; the compact complement has a positive leading-value gap.
   These are the ingredients needed to exclude every off-manifold maximum.

The theorem's
proof is regarded here as complete under its stated hypotheses, subject to
ordinary independent mathematical review.

## 6. Scope and limitations

- The conclusion concerns a distribution with a sufficiently large common
  scalar center. It does **not** establish even 50% coverage for the original
  centered complex-Gaussian spectral pair.
- The unspecified threshold prevents this note alone from certifying a
  specific finite numerical shift or a numerical sampling experiment.
- The shifted law is a deliberately changed law. Increasing its success
  probability is not a proof of unshifted MOC, because MOC is not known to
  be reversible under scalar translation.
- The deterministic conclusion controls every unitary. This is different
  from a probability estimate with respect to Haar-distributed unitaries.
- Dimensions one and two already satisfy MOC without a shift; the argument
  here is for \(n\geq3\), including arbitrary larger dimensions.


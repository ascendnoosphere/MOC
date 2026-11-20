# Positive common laws persist in a unitary neighborhood

Let permutations map column indices to row indices. For a unitary matrix U of order n define

\[
\tau_\pi(U)=\operatorname{Re}\left(
\frac{\operatorname{sgn}(\pi)\prod_j U_{\pi(j),j}}{\det U}
\right).
\]

These weights may be negative. Laplace expansion and Jacobi's complementary-minor identity nevertheless give, for every pair of equally sized subsets I,J,

\[
\sum_{\pi:\pi(J)=I}\tau_\pi(U)=|\det U_{I,J}|^2,
\qquad \sum_\pi\tau_\pi(U)=1.
\]

Suppose a particular unitary V has a strictly positive common law p^0: its subset marginals equal every squared minor of V, and its total mass is one. Define

\[
p_\pi(U)=p_\pi^0+\tau_\pi(U)-\tau_\pi(V).
\]

Every subset marginal of this new law equals the corresponding squared minor of U; its total mass is one. It remains only to prove positivity.

For unitary U,V and epsilon=||U-V||_op, product telescoping gives

\[
\left|\prod_j U_{\pi(j),j}-\prod_j V_{\pi(j),j}\right|\le n\epsilon.
\]

Column telescoping of the determinant, followed by Hadamard's inequality, gives `|det U-det V| <= n epsilon`. Since both determinants have modulus one and every entry has modulus at most one,

\[
|\tau_\pi(U)-\tau_\pi(V)|\le2n\epsilon.
\]

Consequently, if m=min_pi p^0_pi>0 and

\[
\|U-V\|_{\rm op}\le\frac{m}{2n},
\]

then all p_pi(U) are nonnegative. Expanding the paired-sum vertices into their subset monomials proves

\[
\det(A+UBU^*)=\sum_\pi p_\pi(U)\prod_j(a_{\pi(j)}+b_j)
\]

for arbitrary complex diagonal A,B. This is an explicit neighborhood theorem for arbitrary spectra.

## A rational example in dimension four

Take

\[
V=\frac1{65}\begin{pmatrix}
-35&20&-10&-50\\
-20&-35&50&-10\\
-38&-34&-35&20\\
34&-38&-20&-35
\end{pmatrix}.
\]

In lexicographic order of the 24 permutations of (0,1,2,3), a common positive law has numerators

```
357, 618, 2450, 50, 150, 50,
618, 282, 50, 50, 50, 150,
150, 50, 50, 150, 50, 3882,
50, 50, 50, 2450, 50, 818
```

over the common denominator 12675. The independent exact verifier checks orthogonality, determinant one, normalization, and all 70 subset-marginal equations. The minimum weight is `2/507`. Therefore MOC holds for arbitrary spectra whenever

\[
\boxed{\|U-V\|_{\rm op}\le1/2028.}
\]

The Fourier neighborhood note supplies additional explicit strictly positive baselines and sharper entrywise bounds. The transfer lemma is one general mechanism; its examples are not used to inflate a count of independent literature cases.

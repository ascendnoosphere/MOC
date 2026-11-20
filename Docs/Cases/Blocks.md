# Determinant certificates for block eigenbases

Let normal matrices have ordered eigenvalue lists \(a,b\in\mathbb C^n\).
In an eigenbasis of the first matrix write the pair as
\(A=D_a\), \(B=W D_b W^*\), where \(D_x=\operatorname{diag}(x)\).
For \(\pi\in S_n\) put \(v_\pi=\prod_i(a_i+b_{\pi(i)})\).
A probability distribution on \(S_n\) with
\(\det(A+B)=\mathbb E v_\pi\) proves the Marcus–de Oliveira inclusion.

**Block theorem.** Suppose independent reorderings of the two eigenbases
put \(W\) in block diagonal form with block sizes at most three. Then
there is such a distribution depending only on \(W\) and the
reorderings. In particular it works simultaneously for every pair of
spectra in those bases.

## A probability law on one block

Write \(V\in U(m)\) for the block and \([m]=\{1,\ldots,m\}\). For any
subsets \(I,J\subseteq[m]\) let \(a_{I^c}=\prod_{i\notin I}a_i\)
and \(b_J=\prod_{j\in J}b_j\). Expansion along the diagonal summand
selects one principal minor of \(V D_b V^*\) for each \(I\).
Cauchy–Binet on that minor gives
\[
\det(D_a+V D_b V^*)=
  \sum_{|I|=|J|}a_{I^c} b_J\,|\det V_{I,J}|^2 .
\]
The coefficient with which the same indexed term occurs in
\(\mathbb E v_\pi\) is \(\Pr[\pi(I)=J]\).

For \(m\leq3\), choose any Birkhoff–von Neumann decomposition
of the doubly stochastic matrix \(P_{ij}=|V_{ij}|^2\).
With the convention that the permutation matrix has a one in position
\((i,\pi(i))\), the decomposition gives
\(\Pr[\pi(i)=j]=|V_{ij}|^2\).
This covers all singleton terms. Empty and full subsets have probability
one, agreeing with their squared minor moduli. For \(m=3\) and
\(I=[3]\setminus\{i\}\), \(J=[3]\setminus\{j\}\), the cofactor
formula for \(V^{-1}=V^*\) gives
\[
|\det V_{I,J}|^2=|\det V|^2|\overline{V_{ij}}|^2
                 =|V_{ij}|^2=\Pr[\pi(I)=J].
\]
These identities exhaust the terms. For \(m=2\), the identity and
transposition have explicit weights \(|V_{11}|^2\) and \(|V_{12}|^2\).

## Combining blocks

In block coordinates \(A+B\) is a direct sum. Each restriction of
\(A\) is diagonal, and each restriction of \(B\) is unitarily
diagonalizable by its block of \(W\). Hence all restricted pairs are
normal. Choose the block permutations independently and concatenate them
to a permutation of \([n]\). Multiplicativity of determinant and
independence give
\[
\det(A+B)=\prod_r \mathbb E v^{(r)}_{\pi_r}
         =\mathbb E\!\left[\prod_r v^{(r)}_{\pi_r}\right]
         =\mathbb E v_\pi .
\]
Reversing the two initial reorderings bijectively relabels the
permutations. This argument works for zero factors, repeated eigenvalues,
and arbitrary block determinant phases. It also applies to larger blocks
whenever each restricted pair has its own MOC certificate. For blocks
larger than three that certificate can depend on the spectra.

## Consequences in the requested cases

| Cases | Conclusion |
| --- | --- |
| A, G, I, J, M, N, R, S, AH, AJ, AK, BE, BF, BZ | The \(3+1\) and \(2+2\) reductions above prove inclusion for arbitrary spectra. In \(3+1\) the scalar factor is exactly \(a_4+b_4\). In \(2+2\) the weights are products of the two Bernoulli laws. The block restriction preserves normality. Equality or inequality of the two unitary block determinants has no effect. All degeneracies within these block families are included. |
| B | A monomial matrix gives a diagonal \(W D_b W^*\). Its entries are \(b_{\pi(i)}\) for one permutation, so the determinant equals \(v_\pi\) in every dimension. |
| C | If the unitary preserves a coordinate plane \(E\), its restriction is onto \(E\). Thus \(W^*E=E\) and \(W(E^\perp)=E^\perp\). Reorder coordinates to obtain the \(2+2\) certificate in dimension four. |
| AI | Every complex \(1\times1\) unitary is a scalar of modulus one. The stipulated nonscalar block has no instances. |

In dimension five a preserved coordinate plane yields \(2+3\), so case C
still holds for arbitrary spectra. Other covered partitions include
\(3+1+1\), \(2+2+1\) and their refinements. In dimension six the theorem
also covers \(3+3\) and \(2+2+2\). In general a preserved coordinate
plane leaves an \((n-2)\)-dimensional block. A preserved coordinate line
leaves an \((n-1)\)-dimensional block. For either reduction, inclusion
follows once the complementary pair is certified.

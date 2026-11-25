# Flat swaps of a real diagonal summand

Let \(A=\operatorname{diag}(a)\) have distinct real eigenvalues. Let
\(B\) be any complex matrix with strictly positive imaginary part
\(\operatorname{Im}B=(B-B^*)/(2i)\). Fix \(\eta\ne0\). Suppose
\(I\) maximizes \(\operatorname{Re}(\eta\det(VAV^*+B))\) over unitary
\(V\), and switching diagonal slots \(i,j\) gives the same value.
Then \(B\) reduces the plane spanned by \(e_i,e_j\).

The positive-imaginary-part hypothesis can be replaced throughout by
strict negative definiteness. No normality of \(B\) is needed. If \(B\)
is normal, this applies when its spectrum lies strictly on one side of
the real axis. A least-order strict counterexample within this
Hermitian–normal class, with distinct real labels, has no tied swap at a
support maximizer for a strict separating direction. A reducing pair
splits off a verified order-two instance and leaves a smaller instance
in the same class. This is not the assertion that a
terminal matching-contact tie produces a tied swap at the actual
unitary maximizer. That transfer remains open.

## Proof

Fix a third index \(k\). Keep the three active coordinates \(S=\{i,j,k\}\)
and eliminate all inactive coordinates in \(A+B\). Every principal
inactive block is invertible: a nonzero null vector would give zero
imaginary quadratic form, contrary to positive definiteness. Let \(D\)
be that block and write the active Schur complement as
\[
  \operatorname{diag}(a_i,a_j,a_k) + C,\qquad
  C=B_{SS}-B_{S S^c}D^{-1}B_{S^cS}.
\]
Under all rotations or swaps within \(S\), \(D\) and \(C\) remain fixed.
The support phase for the reduced problem is \(\xi=\eta\det D\ne0\).
The Schur complement and its principal two-coordinate block have
strictly positive imaginary part: for active \(v\ne0\), put
\(w=(v,-D^{-1}B_{S^cS}v)\). Then
\(w^*(A+B)w=v^*(\operatorname{diag}(a|_S)+C)v\) and the diagonal
summand is real. Hence the reduced sum is invertible before and
after the swap.

The stationarity condition at each nonsingular maximum says that
\(\xi[A_S,\operatorname{adj}(A_S+C)]\) is Hermitian. For distinct real
diagonal labels \(p,q\), this is equivalent to
\[
  \xi\operatorname{adj}(A_S+C)_{pq}+
  \overline{\xi\operatorname{adj}(A_S+C)_{qp}}=0.
\]
After the swap, the same equation holds with the permuted real diagonal:
it is another maximum because it lies on the same orbit and has the same height.

For \(p\in\{i,j\}\), let \(r\) denote the other index of the pair.
The off-block cofactor satisfies
\(\operatorname{adj}(A_S+C)_{pk}=\operatorname{adj}(C)_{pk}-a_r C_{pk}\),
and likewise in the reverse position. Comparing the equations before and
after the swap therefore gives
\[
  \xi C_{pk}+\overline{\xi C_{kp}}=0,\qquad
  \xi\operatorname{adj}(C)_{pk}+\overline{\xi\operatorname{adj}(C)_{kp}}=0.
\]
Write \(C=\begin{pmatrix}P&u\\v^*&c\end{pmatrix}\), and \(T=\operatorname{adj}P\).
The two equations read \(\xi u+\bar\xi v=0\) and
\(\xi T u+\bar\xi T^*v=0\). Thus \((T^*-T)u=0\).
On two-by-two matrices the adjugate is linear and commutes with adjoint,
so \(T^*-T=\operatorname{adj}(P^*-P)\) is invertible because
\(\operatorname{Im}P>0\). It follows that \(u=v=0\).

Since the inverse of the Schur complement is the corresponding principal
block of \((A+B)^{-1}\), that inverse has zero off-block entries between the
chosen pair and \(k\). This holds for every outside index \(k\). Thus
\((A+B)^{-1}\), hence \(A+B\) and \(B\), reduce the pair. In order two the
assertion is vacuous and no third index is needed.

## Complex labels

The [complex tied-swap theorem](ComplexTiedSwap.md) now derives the
two cofactor equations and the resulting circle alternative in Lean,
including singular active sums. The argument above still supplies the
ambient strictly dissipative reducing-plane conclusion on paper.

## Verification and sources

The mixed determinant formula in **TripleOrbit.lean** represents the local
three-slot determinant as an additive unitary-frame objective. The
reducing argument compares two stationary endpoints and does not require
this extra objective formula. The core local implications are
**adjugate_cross_of_real_diagonal_support_max**,
**triple_tied_swap_cross_cofactors** and
**triple_cross_zero_of_cofactor_skew_nonsingular**. Lean checks the three local implications. The ambient block
reconstruction and the minimal-order consequence are proved above on
paper and are not exported as Lean theorems.

* Juan Ignacio Mulero-Martínez, *A variational framework for determinantal
  inequalities of normal matrices: Successes and obstructions*,
  Linear Algebra Appl. (2026),
  [DOI](https://doi.org/10.1016/j.laa.2026.03.019). Context for support-function
  stationarity; the tied-swap cofactor comparison is proved directly here.
* Dan Wang, Wei Chen, Sei Zhen Khong and Li Qiu, *On the phases of a complex
  matrix*, Linear Algebra Appl. 593 (2020), 152–179,
  [DOI](https://doi.org/10.1016/j.laa.2020.01.035),
  [author preprint](https://arxiv.org/abs/1904.07211), §4, Theorem 4.3.
  Sectorial Schur-complement interlacing is stronger than the half-plane
  inheritance used here. The proof above uses the elementary elimination
  vector identity rather than taking that theorem as an assumption.

* Richard W. Cottle, *Manifestations of the Schur complement*,
  [DOI](https://doi.org/10.1016/0024-3795(74)90066-4). The active-block
  determinant and inverse identities are standard block elimination.

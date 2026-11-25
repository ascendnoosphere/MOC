# A circle obstruction at a tied swap

The checked declarations are in [ComplexTiedSwap.lean](MOC/ComplexTiedSwap.lean). A stationary sum
and its swap may be singular. For an active triple in higher order the
inactive Schur pivot is required to be invertible.

Let \(C\in\mathbb C^{3\times3}\), let \(a,b,s\) be distinct complex
diagonal labels, and put \(A=\operatorname{diag}(a,b,s)\). Fix
\(\eta\ne0\). Suppose the identity maximizes
\(\operatorname{Re}\{\eta\det(VAV^*+C)\}\) over \(V\in U(3)\), and
swapping \(a,b\) ties this maximum. Write
\[
 C=\begin{pmatrix}P&u\\v^*&c_0\end{pmatrix},
 \qquad T=\operatorname{adj}P,
 \qquad X=T+aI,\quad Y=T+bI,\quad c=\overline{a-s}(b-s).
\]
Then either \(u=v=0\), or the following explicit matrix is singular:
\[
 Q=cY^*X-\bar c X^*Y.
\]

## Proof and exact scalar geometry

For any distinct coordinate positions \(i,j\), the pair-plane support
criterion from **PairRayleigh.lean** yields
\[
 \eta(a_i-a_j)\,\operatorname{adj}(A+C)_{ij}+
 \overline{\eta(a_i-a_j)\,\operatorname{adj}(A+C)_{ji}}=0.
\]
The criterion initially uses a flattened diagonal, but replacing the
\(i,i\) entry leaves each of these cofactors unchanged: in one cofactor
row \(i\) is deleted, in the other column \(i\) is deleted. This is
true even at singular matrices. The swapped diagonal is another global
maximum on the same orbit; apply the same equation there.

Fix a position \(p\in\{0,1\}\). Its cofactor in column 2 is
\(\operatorname{adj}C_{p2}-rC_{p2}\), where \(r\) is the other label
of the pair, and the reverse cofactor obeys the same rule. Combining
the two stationary endpoints therefore gives
\[
 (a-s)Y(\eta u)+\overline{a-s}\,Y^*(\bar\eta v)=0,\quad
 (b-s)X(\eta u)+\overline{b-s}\,X^*(\bar\eta v)=0.
\]
Multiply the equations by \(\overline{b-s}\,X^*\) and
\(\overline{a-s}\,Y^*\), respectively, and subtract. The adjoint
pencils commute, so \(Q u=0\). If \(Q\) is nonsingular, \(u=0\).
Then both \(X^*,Y^*\) annihilate \(v\), hence \(v=0\) by \(a\ne b\).
Neither \(X\) nor \(Y\) itself needs to be invertible.

For noncollinear labels put \(\gamma=c-\bar c\ne0\) and
\(w=-\bar c(b-a)/\gamma\). The exact identity
\[
 Q=\gamma\big[(T+(a+w)I)^*(T+(a+w)I)-|w|^2I\big]
\]
shows that a nonreducing tie forces a singular value \(|w|\) of
\(T+(a+w)I\). The scalar zero set is the circle centered at \(-a-w\)
through \(-a,-b,-s\). For collinear labels \(c\) is real and
\(Q=c[\overline{b-a}(T+aI)-(b-a)(T+aI)^*]\).
For nonnormal \(T\), do not replace the singular-value condition by
a claim that an eigenvalue lies on the circle.

The singular-safe cofactor equation, the tied-swap dichotomy, the
centered Gram identity and the reduction through an invertible
spectator block are Lean-checked. Lean also checks the off-diagonal inverse-zero covariance. The two
additional consequences below are paper statements.

## Additional consequence: exact three-slot optimality in the tied case

The three-slot mixed determinant expansion expresses the real objective
as a constant plus \(\sum_j v_j^* H_j v_j\), where \(v_j\) are the
columns of \(V\), and
\[
 H_j=\operatorname{Herm}\big(\eta(a_j\operatorname{adj}C+
                \prod_{k\ne j}a_k\, C)\big).
\]
Let \(W=\operatorname{span}(e_0,e_1)\). The two stationary endpoint
equations say that \(H_0-H_2\) and \(H_1-H_2\) have zero cross entries
from \(W\) to \(e_2\), since for each pair of slots the cost difference
is the same in the two swapped bases. Subtract \(H_2\) from every cost;
this subtracts only the constant \(\operatorname{tr}H_2\).
On \(W\), \(H_0-H_1\) is a scalar: the pair-plane objective is a
Rayleigh quotient and the two orthogonal endpoints tie at its maximum.
Thus the corrected costs are
\[
 H_2=0,\qquad H_0=(K+\lambda I_W)\oplus c_0,\qquad
 H_1=K\oplus c_1 .
\]
Here \(K=K^*\) and \(c_0,c_1,\lambda\) are real. If \(w_j\) is the
projection of \(v_j\) onto \(W\) and \(t_j=|\langle e_2,v_j\rangle|^2\),
the corrected objective is
\[
 \operatorname{tr}K+\lambda-w_2^* K w_2+(c_0-\lambda)t_0+c_1t_1 ,
 \qquad \|w_2\|^2=t_0+t_1 .
\]
The tied endpoint is a global maximum on this triple exactly when
\(c_0-\lambda\le\lambda_{\min}(K)\) and \(c_1\le\lambda_{\min}(K)\).
The formula proves sufficiency. For necessity, rotate slots 0 and 1
at equal height to place a minimum-eigenvalue vector in either slot,
then swap that vector with \(e_2\). If both inequalities are strict,
all optimal triple rotations leave \(e_2\) in slot 2, up to phase.
If either is tight, the same swap is flat, giving a further exact
flat rotation with the spectator.

## Additional consequence: separation circles that can vary by spectator

Use the difference convention \(K=A-B\), with both matrices normal
and \(A\) diagonal with simple spectrum. Fix a tied swap of slots
\(i,j\) at a global support maximum. Suppose for every spectator
\(k\notin\{i,j\}\) the generalized circle through \(a_i,a_j,a_k\)
contains the spectrum of \(A\) on one closed side and the spectrum
of \(B\) strictly on its other side. The circle is allowed to vary
with \(k\). Then the tied pair is a reducing plane for \(B\).

For each \(k\), send its circle to the real axis by a common regular
Möbius map \(f(z)=(\alpha z+\beta)/(\gamma z+\delta)\), orienting the
closed \(A\) side upward. Then \(\operatorname{Im} f(A)\succeq0\) and
\(\operatorname{Im}[-f(B)]\succ0\); the active three labels are real.
Determinants at every orientation are multiplied by one nonzero common
factor, so the tied optimum survives with its correspondingly changed
phase. The inactive principal block is invertible, and the Schur
complement inherits strict positive imaginary part by elimination.
The collinear form of \(Q\) is then nonsingular, because it is a
nonzero scalar multiple of \(T^*-T=\operatorname{adj}(P^*-P)\).
Thus the transformed inverse has zero entries linking the pair and
\(k\).

To see that these statements from different maps combine, let
\(M=\gamma A+\delta I\), \(d=\alpha\delta-\beta\gamma\). The elementary
fractional-linear difference identity gives
\[
 [f(A)-f(B)]^{-1}=d^{-1}\big(MK^{-1}M-\gamma M\big).
\]
Indeed \(f(A)-f(B)=dM^{-1}K(\gamma B+\delta I)^{-1}\) and
\(\gamma B+\delta I=M-\gamma K\). Since \(M\) is invertible diagonal,
the off-diagonal zeros of the inverse are unchanged. Hence
\(K^{-1}\) reduces the pair against all spectators, and \(B\) does too.

## Sources and remaining scope

* G. Lakos, *A short proof of the elliptical range theorem*, Arch. Math.
  122 (2024), [DOI](https://doi.org/10.1007/s00013-023-01957-9):
  numerical-range background for the verified pair-plane criterion.
* S. W. Drury, *Essentially Hermitian matrices revisited*, Electron.
  J. Linear Algebra 15 (2006), 285–296,
  [DOI](https://doi.org/10.13001/1081-3810.1239), §1:
  common fractional-linear transport in the determinantal conjecture.
  The inverse zero-pattern calculation above is proved directly.
* D. Wang, W. Chen, S. Z. Khong and L. Qiu, *On the phases of a complex
  matrix*, Linear Algebra Appl. 593 (2020), 152–179,
  [DOI](https://doi.org/10.1016/j.laa.2020.01.035), Theorem 4.3:
  the general phase interlacing under a Schur complement. Only its
  elementary half-plane consequence enters the paper argument.

These results do not establish a tied swap at an unrestricted global
violating maximum. Matching-label contacts at the terminal threshold
are not ties of swaps of the optimizing mixer.

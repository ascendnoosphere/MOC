# Stationary signed marginals

[StationaryPivot.lean](MOC/StationaryPivot.lean) checks the weighted
pivot identity at every nonsingular real representative of a global
unitary support maximum, in every finite order. It also checks that the
seven contacts and all nonzero-pivot restrictions can be imposed on
one order-four witness. The direct paper derivation below assumes
only real stationarity and does not need nonsingularity. Neither
formulation proves positivity of the signed weights. No finite ray
or permutation census is part of the argument.

## 1. Direct stationary marginal identity, valid in every real order

Use row-to-column permutations. Put \(K_{ij}=a_i+b_j\),
\(A=\operatorname{diag}(a)\), \(B=\operatorname{diag}(b)\), and let
\(U\) be a real orthogonal matrix. Define
\[
C=A+UBU^T,\quad W=K\circ U=CU,\quad
p_\sigma=\prod_iK_{i,\sigma(i)},\quad
s_\sigma=\Re(\eta p_\sigma),\quad
w_\sigma=\frac{\operatorname{sgn}(\sigma)\prod_i U_{i,\sigma(i)}}{\det U}.
\]
Let \(F=\Re(\eta\det C)=\sum_\sigma w_\sigma s_\sigma\).

If \(U\) is stationary on its real orthogonal component, then for every
entry (including zero entries)
\[
\boxed{\sum_{\sigma:\sigma(i)=j} w_\sigma s_\sigma=U_{ij}^2F.}\tag{1}
\]

Proof: differentiate \(\Re(\eta\det(K\circ X)/\det U)\) as a polynomial
in the real matrix entries of \(X\), at \(X=U\). Its real gradient is
\[
G=\Re\bigl(\eta K\circ\operatorname{cof}(W)/\det U\bigr).
\]
Here the cofactor matrix is the transpose of the adjugate. Since \(C\)
is complex symmetric, its adjugate is symmetric, and
\[
\operatorname{cof}(W)=(\det U)\operatorname{adj}(C)U.
\]
This follows from the inverse formula at invertible \(C\), and extends
to singular \(C\) by the polynomial adjugate identity (or continuity).
Using \(UB=(C-A)U\), we obtain
\[
\begin{aligned}
K\circ(\operatorname{adj}(C)U)
 &=A\operatorname{adj}(C)U+\operatorname{adj}(C)UB\\
 &=(\det C\,I+[A,\operatorname{adj}(C)])U.
\end{aligned}
\]
Thus
\[
GU^T=FI+\Re(\eta[A,\operatorname{adj}(C)]).
\]
The second term is real skew-symmetric. Stationarity against every real
skew-symmetric left tangent \(XU\) says \(GU^T\) is symmetric. Therefore
\(G=FU\). Expanding the derivative of the determinant in entry \((i,j)\)
and multiplying by \(U_{ij}\) gives (1), without division by the entry.
QED.

This is an alternative proof of the order-four stationary pivot identity
which needs neither nonsingularity nor the minor complement argument.
It is valid in arbitrary finite real orthogonal order for additive
complex spectra. The stationary identity for complex unitaries requires
a different argument and is not asserted here.

Let \(m=\max_\sigma s_\sigma\), \(g_\sigma=m-s_\sigma\ge0\),
and \(\delta=F-m\). The singleton identity
\(\sum_{\sigma(i)=j}w_\sigma=U_{ij}^2\) now gives
\[
\boxed{\sum_{\sigma(i)=j}w_\sigma g_\sigma
      =-\delta\,U_{ij}^2.}\tag{2}
\]
In particular, at a strictly violating dense stationary point every
one of the sixteen marginal sums is strictly negative.

## What the full pivot system imposes

At a dense real orthogonal mixer the pivot equations recover exactly
first-order real stationarity. In the paper derivation let \(G\) be
the real entry gradient and \(F\) the stationary score candidate.
Before imposing stationarity, the weighted marginal at \((i,j)\)
is \(U_{ij}G_{ij}\). Since \(U_{ij}\ne0\), the pivot equation
there is equivalent to \(G_{ij}=F U_{ij}\). Taken together these
equations give \(G=FU\), hence \(GU^T=FI\), which annihilates
every real skew tangent. The converse is the gradient argument
above. There are not sixteen independent first-order constraints.
The [linear relaxation obstruction](ZhengRealLiftObstruction.md#independent-obstruction-to-using-contacts-and-stationarity-alone)
shows why the contact count does not replace the exact spectral
equations.

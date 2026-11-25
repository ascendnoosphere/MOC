# Corank-two cubic coefficient and limits of the tangent correction

The following is a paper derivation. The corresponding Lean modules
certify the [matrix correction](MOC/AntipodalMovingCompression.lean),
the [signed residual identity](MOC/AntipodalCubicEnergy.lean), and the
[cubic coefficient formula](MOC/AntipodalCubicSchur.lean). The common
spectral mixture below is a paper proof.

Let \(J,K\) denote Hermitian involutions of the same sign counts. Suppose
\(S=J+K\) has a two-dimensional kernel with unit lines \(e_+\) and \(e_-\),
where \(Je_\pm=\pm e_\pm\) and \(Ke_\pm=\mp e_\pm\). Write \(C\) for the
orthogonal complement. For \(D=V+W\) and affine parameter \(t\), \(V\)
commutes with \(J\) and \(W\) commutes with \(K\). In kernel and complement
coordinates write
\[
 S+tD =
 \begin{bmatrix} tE&tL\\tM&S_C+tN\end{bmatrix}.
\]
Here \(E=\operatorname{diag}(\xi_+,\xi_-)\). Let \(R=S_C^{-1}\),
\(d=\det S_C\), and
\[
 T=\tfrac12(\operatorname{tr}(JV)+\operatorname{tr}(KW)).
\]
Block elimination by the Schur complement
([Cottle, DOI 10.1016/0024-3795(74)90066-4](https://doi.org/10.1016/0024-3795(74)90066-4))
gives coefficient \(d\xi_+\xi_-\) at \(t^2\)
and
\[
 d\left(\xi_+\xi_-\operatorname{tr}(RN)
     -\xi_-(LRM)_{++}-\xi_+(LRM)_{--}\right)
\]
at \(t^3\). No invertibility of \(E\) is used.

Let \(x_\pm\) and \(y_\pm\) be independent spectral eigenvalue draws
from \(V\) and \(W\) in the corresponding sign groups, using squared
overlaps with \(e_\pm\). Then \(\xi_\pm=\mathbb E(x_\pm+y_\pm)\). The
cross terms in the diagonal of \(LRM\) vanish because \(R K_C=J_C R\),
which follows from \(K_C S_C=S_CJ_C\). Pure terms are half signed:
\[
 (LRM)_{\pm\pm}
  =\tfrac{\pm1}{2}\bigl(\operatorname{Var}_{\rm alg}(x_\pm)
                       -\operatorname{Var}_{\rm alg}(y_\pm)\bigr),
 \qquad
 \operatorname{Var}_{\rm alg}(x)=\mathbb E(x^2)-(\mathbb E x)^2.
\]
Indeed the \(V\) row/column contributions have \(J_C\)-sign \(\pm\),
and the \(W\) row/column contributions have \(K_C\)-sign \(\mp\). The
anticommutators with \(R\) then give one-half those signs. To identify
the pure row/column product, insert the complement projection before
multiplication: \(V\)'s kernel diagonal is scalar and its other kernel
entry vanishes, so the resulting product is exactly the algebraic
variance; likewise for \(W\).

The prior invertible-antipodal derivative gives
\[
 \operatorname{tr}(RN)
  =T-\tfrac12(\mathbb E x_+-\mathbb E y_+
                -\mathbb E x_-+\mathbb E y_-).
\]
Putting both equations together gives
\[
 [t^3]\det(S+tD)
  = d\,\mathbb E\left[
     (x_++y_+)(x_-+y_-)
     \left(T-\tfrac12(x_+-y_+-x_-+y_-)\right)
    \right].
\]
For the algebra, independence yields
\(\mathbb E((x+y)(x-y))=\mathbb E x^2-\mathbb E y^2\), and the squared means
cancel against the trace contribution.

Choose the two mismatches from those four draws and match the remaining
labels within their signs. Its quadratic and cubic coefficients have
the same formulas with the aligned residual determinant in place of \(d\).
Multiplying by the residual ratio \(0\le\rho\le1\), and assigning the
remaining mass to a four-mismatch product (whose quadratic and cubic
coefficients vanish), gives one common mixture for both coefficients.
If either sign group has only one label, the remaining signs are uniform
and \(\rho=1\), so no padding is needed. This is for fixed mixer and an
affine spectral path.

## Why a varying mixer changes the picture

For a skew-Hermitian orbit tangent \(X\), the compressed \([X,K]\)
has zero diagonal and conjugate off-diagonals. Thus its determinant
correction in the two-dimensional kernel is exactly
\(-4|(E^*XE)_{01}|^2\), where here \(E\) is the column matrix of kernel
vectors. The projection of the correction is nonpositive if it is
nonnegative on the complement determinant. This is the favorable
support sign pointing away from the aligned antipodal center product.
The correction vanishes in the tangent direction that annihilates the
kernel off-diagonal, but that does not alone say anything about all
higher coefficients.

In a four-dimensional kernel, the naive product-of-probabilities
bound on the mixed quartic term is false at nonzero support levels.
With \(\sigma_z,\sigma_x\) the Pauli matrices, take the two diagonal
blocks \(A=\sigma_z+i\sigma_x\) and \(B=\sqrt 2(\sigma_z-i\sigma_x)\).
The latter is the sum of normal matrices
\((1-i)(\sigma_z+\sigma_x)/\sqrt 2\) and
\((1+i)(\sigma_z-\sigma_x)/\sqrt 2\).
Thus the two scalar crossed factor sets are
\(\{\pm1\pm i\}\) and \(\{\pm2,\pm2i\}\).
Every real scalar product is at most 2. Nevertheless for the crossed
block \(C=I\) the mixed trace normalized by \(\operatorname{tr}(CC^*)\)
is \(2\sqrt 2\): both blocks are traceless, so their adjugates are
their negatives, and \(\operatorname{tr}(AB)=4\sqrt 2\).
This refutes a general direct bound on that quartic term, not MOC:
the example has nonzero competing quadratic matching jets.

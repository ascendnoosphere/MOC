# Number representations and changes of matrix basis

Changing the radix used to write a number, including an irrational or
transcendental radix, leaves the MOC question unchanged if the represented
values and field operations are unchanged. Restricting the permitted digit
strings is a new restriction on values, and needs its own definition.

There is a separate matrix-basis issue. Let S be invertible over C, and use
coordinates x=S x'. The old standard inner product becomes the Gram form
G=S* S. Set A'=S^-1 A S and B'=S^-1 B S. The correct adjoint in the new
coordinates is X^dagger=G^-1 X* G. Direct multiplication gives

    (S^-1 X S)^dagger = S^-1 X* S.

Thus normality, unitarity, spectra, and all determinant values are preserved
when the metric and adjoint are transported with the basis. In particular,
if U'=S^-1 U S then

    A'+U' B' (U')^dagger = S^-1 (A+UBU*) S.

Its determinant is unchanged. Irrational or transcendental entries in S
cannot create an easier problem by themselves. If one keeps the standard
adjoint after a nonunitary basis change, one has changed the normality and
unitarity hypotheses rather than re-expressed the same MOC instance.

This distinction is relevant to nested decompositions: common orthogonal
reducing subspaces preserve the original adjoint. Arbitrary independent
similarities of the two matrices do not preserve their relative geometry.

For value-field restrictions, see arithmetic_reductions.md. In particular,
Q(i) is dense in C, so every field containing Q(i) retains the full problem.
A real-only spectral restriction is Hermitian; a nonreal generator beta
makes Q+beta Q dense in C. Fixed-dimensional transfer to real-closed
ordered fields is different from using p-adic fields, which carry a
valuation rather than the needed real order.

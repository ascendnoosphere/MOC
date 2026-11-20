# Scalar rank-two compression reduces to eight outcomes on each side

## Theorem

If the scalar rectangular compression conjecture CMC(2;m,n) has a strict
counterexample for any finite m,n, it has one with at most eight nonzero
columns in each frame. Thus proving CMC(2;8,8), allowing zero columns,
would prove it for all finite m,n.

If the rays of either frame can all be made real by one unitary basis
change and independent column phases, that side can be reduced to at most
six nonzero columns. In particular the all-real-frame version reduces to
CMC(2;6,6).

This is a scalar support-function statement. It does not reduce the common
law for all spectra, and does not preserve all minor probabilities.

## Proof

Suppose there is a strict separating inequality

    Re(eta det(A_X+B_Y)) > h,

where h is the maximum of the same real functional on every original
injective two-matching product, eta is nonzero, and

    A_X = sum_i a_i E_i, B_Y = sum_j b_j F_j,
    E_i=x_i x_i*, F_j=y_j y_j*, sum_i E_i=sum_j F_j=I_2.

Discard initially zero effects. Keeping the rays E_i and the entire second
frame fixed, consider the compact polytope

    T = {t_i>=0: sum_i t_i E_i=I_2}.

Compactness follows by taking traces: each tr(E_i)>0 and
sum_i t_i tr(E_i)=2. The original vector t_i=1 is feasible. Maximize

    f(t) = Re(eta det(sum_i a_i t_i E_i+B_Y))

over T and select a maximizer with the fewest positive coordinates, s.
On the relative interior of its active face, every tangent vector v
satisfies sum_i v_i E_i=0, so the tangent dimension is at least s-4.
Stationarity gives df(v)=0, and the quadratic second-order form is
negative semidefinite on this tangent space.

The determinant on complex 2 by 2 matrices is a nondegenerate complex
quadratic form in four complex coordinates. The real quadratic form
Q(Z)=Re(eta det Z) therefore has signature (4,4). The quadratic part of
f is a real linear pullback of Q. Its restriction to any subspace can
have negative index at most four. A negative semidefinite restriction
on a space of dimension greater than four must consequently have a
nonzero null vector v.

If s>8, such a v exists. Because f is quadratic and df(v)=Q(v)=0,

    f(t+lambda v)=f(t)

for every real lambda. Trace positivity implies that a nonzero feasible
tangent vector has both signs. The feasible segment in this direction
therefore has a finite endpoint where at least one active coordinate
becomes zero. This gives a maximizer with smaller support, a contradiction.
Hence s<=8.

Replace x_i by sqrt(t_i) x_i for the retained coordinates. This remains a
coisometry, and its separating functional is at least the original value.
Its matching vertex set is a subset of the original one, since only
spectral indices have been removed. It therefore remains a strict
counterexample to the corresponding reduced scalar conjecture.

Now fix this reduced first frame and repeat the same argument for the
second. Its number of nonzero columns also becomes at most eight. Strict
separation from the original halfspace is preserved at both stages.

For the real-ray refinement, the moment constraints lie in the
three-dimensional space of real symmetric 2 by 2 matrices. The variable
matrix lies in the complexification of that space, where the determinant
is a nondegenerate quadratic form in three complex coordinates. Its real
part has signature (3,3). The same proof gives s<=3+3=6. The fixed other
summand affects only the linear and constant terms and need not be real.

## Scope

This reduces an unbounded family of scalar rank-two problems to one finite
size. It supplies no positivity certificate at that remaining size. The
subsequently proved common law for (2;3,n), for every finite n, is
therefore useful but does not yet close the full rank-two problem, much
less the rank-three compression problem equivalent to MOC in dimension four.

The argument was independently checked by the geometry and review tracks
in the present campaign. No historical-priority claim is made.

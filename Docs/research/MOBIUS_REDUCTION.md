# Möbius invariance and a dense normal form for MOC4

**Status:** elementary exact reduction, not a proof of MOC4. The Möbius identity and dense normalization were cross-checked in the **VALID** [independent rectangular-reduction audit](rectangular_compression_independent_review.md). The spectral-family certificate with fixed b is not enough to close
this reduction.

## Invariance in every order

Let f(t)=(alpha*t+beta)/(gamma*t+delta), with
Delta=alpha*delta-beta*gamma nonzero. Suppose none of the eigenvalues of A or -B
is a pole. Put A'=f(A), B'=-f(-B). Both are normal if A,B are normal.

For any Y similar to -B,

(gamma*A+delta*I)f(A)-f(Y)
    = Delta*(A-Y).

This follows by expanding
(alpha*A+beta*I)(gamma*Y+delta*I)
 -(gamma*A+delta*I)(alpha*Y+beta*I): the ordered AY terms cancel; no assumption
that A and Y commute is used. With Y=-UBU*, determinants give

    det(A'+U B' U*) = K det(A+UBU*),
    K = Delta^n / [product_i(gamma*a_i+delta)
                    product_j(delta-gamma*b_j)].

K is nonzero and independent of U. For each permutation pi, independently,

    product_i[f(a_i)-f(-b_pi(i))] = K product_i(a_i+b_pi(i)).

Multiplication by K is an invertible real-linear map of the complex plane and
preserves convex combinations. Thus MOC membership for each U is equivalent
before and after the transformation. This does not require f to have real
coefficients, to preserve the upper half-plane, or to map either entire spectrum
to the real line.

## Dense normal form in order four

For three distinct a_1,a_2,a_3 define

    r(t)=(t-a_1)(a_2-a_3)/[(t-a_3)(a_2-a_1)],
    f(t)=r(t)/(r(t)+1).

Use the rationally simplified map

    f(t)=(t-a_1)(a_2-a_3)/[(t-a_1)(a_2-a_3)+(t-a_3)(a_2-a_1)].

Then f(a_1)=0, f(a_2)=1/2, f(a_3)=1. The last evaluation uses this canceled expression: r itself has a pole at a_3, but the displayed denominator of f is nonzero there for the stipulated distinct triple. Away from its single pole and spectral
collisions, this transforms A to diag(0,1/2,1,z). The transformed B spectrum is
still an arbitrary four-point complex spectrum.

Pole avoidance is important: it is not asserted that this particular f works
at every nongeneric pair. For fixed labels, collisions and pole incidences lie
in a proper algebraic exceptional set. Generic pairs avoid it. If MOC were
proved for every finite normalized z and **every** remaining b spectrum, the
identity above would prove MOC for this dense set of original pairs. Continuity
of the determinant and of the 24 permutation products would then extend it to
collisions, poles, and all other degenerate limits.

In detail, convex-hull membership is closed under convergence of finitely many
vertices: take a convergent subsequence of coefficient vectors in the compact
24-simplex. This is enough for all exceptional limits, without ever evaluating
a rational function at a pole.

## Exact remaining theorem

The following would suffice for unrestricted MOC4:

> For every b in C^4, every z in C, and every U in U(4),
> det(diag(0,1/2,1,z)+U diag(b)U*) belongs to the convex hull of the 24
> permutation products.

The currently recovered 68 rational SOS certificates establish this only for
b=(i,-i,1+i,-1+2i). Testing further b values, or verifying finitely many support
fans at selected b values, does not establish the quantified statement above.
A new uniform argument in b, or another gap-closing theorem, is still required.


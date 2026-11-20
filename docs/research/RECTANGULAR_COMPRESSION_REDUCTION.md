# Exact square–rectangular equivalence, and why the fiber-at-infinity step is not MOC3

**Status:** elementary algebraic equivalence in every order, with exact block identities and rational regression checks. The [independent mathematical audit](rectangular_compression_independent_review.md) is **VALID**, including degeneracies, complex scaling and the nonnormality obstruction. **This is not a proof of either equivalent conjecture.**

[Verifier](../../code/research/verify_rectangular_compression_reduction.py). No numerical optimization is used. The general proof is below; finite regressions are not its substitute.

## 1. Two precise universal statements

For n>=2, let MOC(n) mean the usual unrestricted complex statement

    det(D_a+U D_b U*) in conv{product_i(a_i+b_pi(i)): pi in S_n}

for every a,b in C^n and U in U(n).

Let R(n-1,n) mean

    det(D_x+W D_y W*)
       in conv{product_(i=1..n-1)(x_i+y_iota(i)): iota injective}

for every x in C^(n-1), y in C^n and every (n-1)-by-n **coisometry** W, WW*=I_(n-1). The compression W D_y W* need not be normal.

**Theorem.** MOC(n) and R(n-1,n) are equivalent. In particular the unrestricted3-by-4 coisometry statement is equivalent to unrestricted MOC4, **not** an already-solved order-three special case.

## 2. Exact common-scalar identity

Let W be the first n-1 rows of U. Suppose

    d_i=a_i-a_n !=0  (i<n),
    c_j=a_n+b_j !=0  (j<=n).

Put

    x_i=1/d_i, y_j=1/c_j,
    L=(product_(i<n) d_i)(product_(j<=n)c_j) !=0.

Then

    det(D_a+U D_b U*) = L det(D_x+W D_y W*).       (1)

**Proof.** Let E embed C^(n-1) as the first coordinates, D=diag(d_i), and C=U diag(c_j)U*. Then C is invertible and

    D_a+U D_b U* = C+E D E*.

Sylvester's rectangular determinant identity gives

    det(C+EDE*)
      =det(C)det(I_n+C^(-1)EDE*)
      =det(C)det(I_(n-1)+D E*C^(-1)E)
      =det(C)det(D)det(D^(-1)+E*C^(-1)E).

But E*C^(-1)E=W diag(1/c_j)W*, giving (1). This requires no commutation of D and the compression.

For each pi in S_n, exactly the **same** nonzero scalar satisfies

    product_(i<=n)(a_i+b_pi(i))
      = L product_(i<n)(x_i+y_pi(i)).               (2)

Indeed x_i+y_pi(i)=(c_pi(i)+d_i)/(d_i c_pi(i)); the one unused c_j is c_pi(n). Restricting pi to the first n-1 indices is a bijection from S_n to these injections. The comparison set has not been enlarged.

Multiplication by L preserves convex combinations in the complex plane (with real nonnegative coefficients). In a support-function version it rotates/rescales the one original support direction; it does not introduce a separate phase or independent budget.

## 3. Both implications and all degeneracies

R(n-1,n) implies MOC(n) whenever all displayed d_i,c_j are nonzero, by (1)–(2). Such spectral data are dense with U fixed. Determinants and all finite vertex lists are continuous. Convex-hull membership passes to the limit: the coefficient vectors lie in the compact n!-simplex, so a convergent subsequence gives the limiting convex combination. No rational expression is evaluated at a pole.

Conversely, given arbitrary W, complete its orthonormal rows to U. First assume every x_i,y_j is nonzero and choose

    a_n=0, a_i=1/x_i, b_j=1/y_j.

The previous identity applies with this W. MOC(n) and division by L prove the desired rectangular statement. If some x_i or y_j is zero, perturb only x,y to nonzero values with W fixed, and take the limit **in the finite compressed statement**. There is no assertion that the reciprocal square spectra stay bounded.

Thus the equivalence includes repeated spectra, zero entries and all other degenerate data by a proved continuity argument. It does not presume existence of Gram completions or an SOS representation.

This is the point-at-infinity form of the [Möbius reduction](MOBIUS_REDUCTION.md), made exact without evaluating a rational function at its pole.


## 5. Consequence for affine one-eigenvalue fibers

For fixed a_1,...,a_(n-1),b,U, the coefficient of t in

    det(diag(a_1,...,a_(n-1),t)+U D_b U*)

is exactly det(D_a[1:n-1]+W D_b W*). The coefficient of t in a permutation product is product_(i<n)(a_i+b_pi(i)). Thus a **universal** support bound for all leading coefficients at infinity is R(n-1,n), and by the theorem is already equivalent to MOC(n).

The [actual-fiber interpolation proposition](ACTUAL_FIBER_ALLOCATION.md) remains valid and useful for a bounded contact polygon with verified vertices. But an attempted global proof by checking finite vertices and then saying “the unbounded rays follow from MOC3” leaves precisely an equivalent unrestricted problem. No theorem about convexity of the support function alone resolves it.

## 6. Source for the block determinant identity


Sylvester's identity is also stated in Peter Michael Reichstein Rasmussen, *Flow Equivalence of Shift Spaces*, [arXiv:1510.00326v1](https://arxiv.org/abs/1510.00326v1), **Lemma2.24**. Its two elementary block factorizations are verified symbolically for arbitrary independent3-by-4/4-by-3 entries by the local verifier. The proof works over C and needs no invertibility of those rectangular matrices; only C,D in section2 are inverted under the stated nonzero conditions.


# An elementary four-dimensional case of the determinantal conjecture

## Theorem

Let A and B be normal complex 4-by-4 matrices. If an eigenvalue of A is the negative of an eigenvalue of B, then the Marcus–de Oliveira determinant inclusion holds for A and B. Equivalently, the inclusion holds whenever at least one permutation vertex is zero.

This is an all-unitary spectral class: the remaining eigenvalues can be arbitrary complex numbers, including simple noncocircular spectra. It does not require a common eigenvector, and A+B need not be singular. No claim of novelty is made here. The unrestricted conjecture is not proved.

After diagonalizing, reordering, and replacing A by A−a_0 I and B by B+a_0 I, it suffices to take

    A=diag(0,a_1,a_2,a_3),  B=diag(0,b_1,b_2,b_3),

with all six displayed parameters arbitrary complex numbers and an arbitrary U in U(4). We prove that one probability distribution p_pi(U) works simultaneously for all six parameters.

## 1. The squared minors that actually occur

Write R={1,2,3}, and define

    r = 1−|U_00|²,
    x_i = |U_i0|²,  y_l = |U_0l|²  (i,l in R),
    Q_il = |det U_({0,i}, R\{l})|².

Unitarity gives sum_i x_i=sum_l y_l=r. Cauchy–Binet gives

    sum_l Q_il = det(U_({0,i},R) U_({0,i},R)*)
               = det(I_2−U_({0,i},{0}) U_({0,i},{0})*)
               = r−x_i.

The equality of the absolute values of complementary minors of a unitary matrix gives

    Q_il = |det U_(R\{i},{0,l})|².

Applying Cauchy–Binet in the other direction consequently gives

    sum_i Q_il = det(U_(R,{0,l})* U_(R,{0,l})) = r−y_l.

These identities are exact for every unitary U.

For a subset S of R, let a_S=product_{i in S} a_i and b_S=product_{j in S} b_j. The usual determinant/minor expansion reduces, because a_0=b_0=0, to

    d := det(A+U B U*)
       = a_R sum_l y_l b_l
         + sum_(i,l in R) Q_il a_(R\{i}) b_(R\{l})
         + b_R sum_i x_i a_i.                         (1)

Indeed, only row sets containing 0 and column sets avoiding 0 survive. The size-one minors give y_l. The size-two minors give Q_il. The size-three minors have complements (i,0), and therefore give x_i.

If r=0 then x=y=Q=0, so d=0. The identity permutation also has vertex zero, proving the assertion in that case. Assume r>0 below.

## 2. A genuine normalized probability distribution

The following 4-by-4 matrix is doubly stochastic:

                   [ Q    x ]
    D = (1/r)      [ y^T  0 ].                         (2)

It is entrywise nonnegative. The row-sum and column-sum identities just proved show that every row and column sums to one.

By the Birkhoff–von Neumann theorem, D is a convex combination of permutation matrices. Since the lower-right entry of D is zero, every permutation matrix with positive coefficient in this combination also has lower-right entry zero. Its upper-left 3-by-3 block is therefore a matching consisting of exactly two entries equal to one, in different rows and columns.

Let nu be the probability distribution on these two-edge matchings obtained from a Birkhoff decomposition. If M is a random matching with law nu, then

    Pr((i,l) is an edge of M) = Q_il/r,
    Pr(row i is missing from M) = x_i/r,
    Pr(column l is missing from M) = y_l/r.           (3)

There are precisely 18 possible matchings: choose one missing row, one missing column, and one of the two bijections between the remaining two rows and columns.

## 3. Convert each matching into a permutation vertex

Suppose a matching has edges (i_1,l_1), (i_2,l_2), missing row h, and missing column k. Define a permutation pi of {0,1,2,3} by

    pi(0)=h,  pi(k)=0,
    pi(l_1)=i_2,  pi(l_2)=i_1.                       (4)

The crossing of the two matched row assignments is essential. This is a bijection from the 18 two-edge matchings onto the 18 permutations satisfying pi(0) != 0.

For this permutation, direct expansion of

    z_pi = product_{j=0}^3 (a_pi(j)+b_j)

gives

    z_pi = a_R b_k + a_h b_R
           + sum_{(i,l) in M} a_(R\{i}) b_(R\{l}).   (5)

For example, the pair of matched edges (i_1,l_1),(i_2,l_2) corresponds to the two mixed terms: pi maps R\{l_1} onto {0,i_1}, and R\{l_2} onto {0,i_2}.

Take the expectation of (5) under nu and multiply by r. Using (3), the result is exactly the right-hand side of (1). Hence

    d = r E_nu[z_pi(M)].                              (6)

Finally, assign mass r nu(M) to each permutation pi(M), and assign the remaining mass 1−r=|U_00|² to the identity permutation. Its vertex is zero because a_0+b_0=0. These weights are nonnegative, sum to one, and (6) proves

    d = sum_pi p_pi(U) z_pi.

This completes the proof.

## Scope and relation to the earlier computation

The proof constructs a distribution reproducing only the squared minors whose monomials survive when a_0=b_0=0. It does not assert the false existence of a common distribution reproducing every squared minor of an arbitrary 4-by-4 unitary.

The earlier computer-assisted theorem for A=(0,1,2,t), B=(0,1,z,2+z) is a special case. Its 27-facet certificate remains an independent exact verification of that narrower family, but it is no longer needed for the broader theorem.

Direct sums of pairs covered by this theorem yield further examples in larger dimensions when the pairs have a common reducing block decomposition into blocks of size at most four, with the size-four blocks satisfying the displayed spectral condition. This does not establish the condition for arbitrary relative unitaries in larger dimensions.

## Optional exact checker

Run `python verify_zero_paired_sum.py`. The standard-library checker verifies all 18 matching-to-permutation maps and the coefficient identity (5). It also constructs an exact rational Birkhoff decomposition for the previously troublesome quaternion U=M/sqrt(13), and checks the relevant minor marginals and probability normalization exactly. The proof above does not depend on this example or on numerical computation.

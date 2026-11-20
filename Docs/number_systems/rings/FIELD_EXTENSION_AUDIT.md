## 2. Finite-unitary affine enclosure: the characteristic-two repair is valid

For U unitary over L=F_(q^2), let

    c_pi=sgn(pi) product_j U_pi(j),j / det U.

Laplace expansion and the complementary-minor identity give

    sum_(pi(J)=I) c_pi = N(det U_(I,J)) in F_q.

Choose eta in L with Tr_(L/F_q)(eta)=1 and put
p_pi=Tr(eta c_pi). The trace map is onto, including characteristic two.
It fixes every displayed marginal after multiplication by eta, and
sum p_pi=1. Consequently these F_q coefficients reproduce the determinant
expansion and give the asserted F_q-affine enclosure for arbitrary n.

These are affine field coefficients, not nonnegative real probabilities.
Using c+conjugate(c) divided by two would fail in characteristic two;
the chosen trace retraction avoids that error.

The exact U(3,2) result in the finite-field agent's note also passes:
two-valued spectra give a rank-one update with the four possible coefficient
vectors of odd parity in F2^3, all realized by unit vectors. Three distinct
values in F4 omit exactly one field element; opposite translations and a
common nonzero scaling reduce the two omitted values to (0,0) or (0,1).
In both resulting cases permutation matrices already realize the full
F2-affine vertex hull.

The unrestricted-similarity singleton classification is correct over every
field: either one spectrum is scalar, or a cross multiplicity satisfies
m_A(alpha)+m_B(-alpha)>n. For zero common vertices this is Hall's matching
obstruction; for nonzero common vertices every factor is nonzero and the
transposition difference forces one spectrum to be constant.

## 3. Integral and unrestricted p-adic unitary groups differ

For a quadratic local extension L/K, the exact integral order-two coefficient
set is

    T={s in O_K : s=N(b), 1-s=N(d), b,d in O_L}.

The matrix [[conjugate(d),b],[-conjugate(b),d]] is special unitary and
realizes the corresponding mixture (1-s)z_id+s z_swap. Thus the formula is
both necessary and sufficient. For an unramified quadratic extension,

    T={s in O_K : v(s) and v(1-s) are nonnegative even integers or infinity}.

This uses the even valuation of a norm and surjectivity of the norm on
units. Its additive Haar volume, normalized on O_K, is

    (q-2)/q + 2 sum_(k>=1)(q-1)/q^(2k+1) = (q-1)/(q+1).

This is the additive volume of the attainable coefficient set. It is not
the determinant law induced by group Haar measure on a unitary group.


## 4. The finite-adelic equalities are valid with the stated groups

For diagonal adelic spectra, fix a vertex z_0 and select delta_p to be one
vertex difference of maximal p-adic norm, or zero if all local differences
vanish. Then delta is an adele and

    sum_pi Zhat (z_pi-z_0)=delta Zhat.

The selection is among finitely many adelic differences; its assembly uses
idempotents in Zhat. The exact determinant ranges are

    f(product_p SL_n(Z_p)) = z_0+delta Zhat,
    f(SL_n(A_f)) = z_0+delta A_f,

and replacing SL by GL does not change either range. Containment follows
from the ring identity. For surjectivity, at every prime a transposition
edge attains the local diameter by the ultrametric path inequality. Patch
these finitely many edge choices; their differences equal delta times a
unit of Zhat. The parameter in the two-by-two interpolation lies in Zhat
or A_f as appropriate. This verifies that the realizing matrices obey
the restricted-product condition, rather than merely solving each local
problem independently.


The density of SL_n(Z) in the product of integral local SL groups follows
from Chinese remaindering and elementary generation. Continuity and
compactness then give density of integer determinant values in the compact
adelic range. This is not exact global integral attainment. Likewise, the
finite-place density does not supply simultaneous approximation at the real
place under all-prime integrality.


The one-sided result for a rank-one Hermitian perturbation passes. Let
A=diag(a_i) have standard complex quaternion eigenvalues and let
UBU*=beta I+(gamma-beta)vv*, where beta,gamma are real, v*v=1, and
w_i=|v_i|^2. If C=diag(a_i+beta) is invertible, multiplicativity and the
rank-one determinant identity give

    S(C+(gamma-beta)vv*)
      = S(C) |1+(gamma-beta)v*C^(-1)v|.

Write v_i=sqrt(w_i)q_i with unit quaternions q_i. The scalar inside the norm
is the sum of w_i conjugate(q_i)(1+(gamma-beta)/(a_i+beta))q_i.
Quaternion norm invariance and the triangle inequality therefore prove

    S(A+UBU*) <= sum_i w_i |a_i+gamma| product_(j!=i)|a_j+beta|.

Continuity covers singular C. The reality of gamma-beta matters in the
algebra. The proof yields the stated upper bound, not a lower bound or a
convex-interval inclusion.

## 6. Gaussian-prime spectra preserve the entire complex problem

Tao's Theorem 1.2, *The Gaussian primes contain arbitrarily shaped
constellations*, supplies x in Z[i] and a nonzero integer r with x+rF
entirely Gaussian prime for every finite distinct set F in Z[i]. The
corrected primary version was checked directly:

https://arxiv.org/pdf/math/0501314

Take F to be the set of distinct values among a_i and -b_j. Put

    a'_i=x+r a_i,     b'_j=r b_j-x.

Every a'_i is Gaussian prime, and so is every b'_j because it is minus a
Gaussian prime. For the SAME arbitrary complex unitary U,

    diag(a')+U diag(b')U* = r[diag(a)+U diag(b)U*].

The determinant and every permutation vertex scale by r^n. Nonzero scalar
multiplication preserves real convex-hull membership exactly. Gaussian-
rational spectral approximation and common denominator scaling therefore
show that full complex MOC is equivalent to its restriction to Gaussian-
prime spectra. This is a reduction of the full problem, not a proof of
the prime-spectral case. It says eigenvalues, not matrix entries.

The explicit constellation with r=10 and x=-1680-1031i has also passed an
independent integer check: all eight displayed norms are prime by exhaustive
trial division, all sixteen pair sums scale exactly, and all twenty-four
four-dimensional pairing vertices scale by 10000.

## 7. Nested blocks and their open neighborhoods

The product construction for weights is valid when the matrices have actual
common reducing blocks; independent diagonalizations do not supply such
blocks. The perturbation theorem also passes independent audit. For a normal
reference pair with a radius-r disk around its determinant inside its hull,
put eta=||A-A_0||_F+||B-B_0||_F and M_0=||A_0||+||B_0||. Then

    2 n (M_0+eta)^(n-1) eta <= r

suffices for MOC for the perturbed normal pair. The overlap matrix of normal
eigenbases gives a doubly stochastic spectral matching with maximum error
bounded by the Frobenius error. Multilinearity bounds both the matched
vertex motion and the determinant motion by n(M_0+eta)^(n-1)eta.

For the displayed two-block example, the four product vertices form
x>=0, y>=x, 6<=x+y<=8; the determinant (7+21i)/4 has margin 1/sqrt(2).
The stated Frobenius radii 1/5000 give the rigorous upper error bound
9261/20000, smaller than that margin. Thus this genuinely extends to fully
coupled nearby normal pairs. It does not make all decompositions or all
small-coupling limits automatic.

## Verification record

Run `python3 rings/check_exact_arithmetic.py` from the
bundle directory. Its output is `exact_arithmetic_check.json`. Mathematical proofs
above are independent of the finite checks. No unrestricted complex MOC
theorem, exact unrestricted PID range theorem, or priority claim is made.

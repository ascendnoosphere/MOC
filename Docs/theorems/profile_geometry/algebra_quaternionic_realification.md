# Rank-four real, complex, and quaternionic determinant convex hulls coincide

## Scope

This note follows the proposed strategy of placing the SO(4) problem among
same-rank variants, rather than restricting either spectrum. It extends the
realification argument in `algebra_unitary_realification.md` from U(4) to Sp(4).
It proves an equivalence of all three unrestricted rank-four problems. It does
**not** prove their common permutation-hull inclusion.

No numerical experiment or symbolic scan is needed. No historical-priority
claim is made.

## 1. The common generalization

For F = R, C, H, let V_F = Herm_4(F), regarded as a real Euclidean Jordan
algebra, and let Delta_F denote its degree-four Jordan determinant. These are
respectively the ordinary determinant on real symmetric matrices, the ordinary
determinant on complex Hermitian matrices, and the Moore determinant on
quaternionic Hermitian matrices.

Extend V_F and Delta_F by scalar complexification. The complex scalar in
V_H tensor_R C is central and must not be confused with a chosen imaginary
quaternion. Our spectral elements have the form

    x = sum_i a_i e_i,  y = sum_j b_j f_j,  a_i,b_j in C,

where (e_i) and (f_j) are real Jordan frames. The conjecture is

    Delta_F(x+y) in conv_R{ product_i(a_i+b_pi(i)) : pi in S_4 }.

The frame-changing groups are O(4), U(4), and Sp(4). Row signs allow O(4)
to be replaced by SO(4) for the determinant problem. For F=C this is exactly
the usual normal-matrix MOC, through Herm_4(C) tensor_R C = M_4(C).
For F=H it is a complexified-Jordan statement, **not** a statement about
arbitrary quaternionic normal matrices and their right eigenvalues.

The three simple algebras have real dimensions 10, 16, and 28, but all have
rank four. Reducible rank-four algebras provide additional siblings; the
already-proved rank-at-most-three theorem and products settle those whose
simple factors have rank at most three. That product argument does not settle
any of the three simple rank-four algebras.

## 2. Quaternionic Gram-minor coordinates

For Q in Sp(4), and index sets I,J of equal size, define

    q_IJ(Q) = Mdet(Q[I,J] Q[I,J]^*).

Set q_empty,empty = 1. All these numbers are nonnegative. For real O they are
(det O[I,J])^2; for complex U they are |det U[I,J]|^2.

We use three standard Moore determinant identities:

1. For a square quaternionic matrix X and its standard complex representation
   chi(X),

       Mdet(XX^*) = det chi(X) >= 0.

2. For a rectangular quaternionic X and a real diagonal D=diag(d),

       Mdet(X D X^*)
         = sum_{|J|=number of rows of X} Mdet(X_J X_J^*) product_{j in J} d_j.

3. Adding a real diagonal matrix to a hyperhermitian matrix has the usual
   principal-minor expansion.

For (3), one can apply (2) to [I,Q] and diag(a,b), then expand the Gram
coefficient associated with selected standard columns. Equivalently it follows
by expanding the Pfaffian definition of Mdet in the diagonal coordinates.
These identities are polynomial in real a,b and therefore extend to their
central complexifications.

Consequently, for all complex a,b,

    Delta_H(D_a + Q D_b Q^*)
      = sum_{|I|=|J|} a_(I^c) b_J q_IJ(Q).                 (1)

Here a_S = product_{i in S} a_i, and similarly for b.

### Complementary minors

The representation chi(Q) is an 8 by 8 complex unitary matrix. A quaternionic
submatrix Q[I,J] corresponds to the complex submatrix on the two coordinates
associated with each index in I,J. Its complementary complex submatrix
corresponds to Q[I^c,J^c]. Jacobi's complementary-minor identity and (1) of
the standard identities above give

    q_IJ(Q) = q_(I^c,J^c)(Q).                              (2)

Only the modulus version of Jacobi is needed, so choices of coordinate
ordering and determinant signs have no effect.

## 3. A three-effect real frame lemma

Let E_1,E_2,E_3 be real symmetric positive semidefinite operators on a
three-dimensional real Euclidean space, satisfying

    tr E_i = 1,   E_1+E_2+E_3 = I_3.

Then the triple is a convex mixture of triples of mutually orthogonal
rank-one projections. At most eleven triples suffice.

### Proof

The feasible set is compact and convex. If every rank is at least two, the
sum of the dimensions of supported symmetric perturbations is at least
3+3+3=9. Preserving the symmetric sum imposes six equations, while individual
trace preservation adds at most two independent equations. Thus there is a
nonzero supported perturbation (H_1,H_2,H_3) preserving all constraints.
Small perturbations of both signs remain positive semidefinite, so such a
triple is not extreme.

At an extreme point one effect is rank one, hence a projection P. The other
two are supported on P-perp and sum to its identity. They commute, and in a
common real orthonormal basis have eigenvalues (theta,1-theta) and
(1-theta,theta). Unless theta is zero or one this is a nontrivial mixture of
the two ordered complementary projection pairs. Thus every extreme point is
an orthogonal projection triple.

The affine dimension of the feasible set is ten: three symmetric 3 by 3
matrices give eighteen coordinates, and the sum and trace constraints have
rank eight. Caratheodory's theorem gives at most eleven extreme points. QED.

Unlike the complex-unitary construction, the effects below need not have
rank at most two. Therefore the earlier four-basis bound is not asserted for
Sp(4); the eleven-basis bound is sufficient here.

## 4. Realify a quaternionic frame

Fix any row index r. Right-multiply Q by a quaternionic diagonal unitary so
that row r becomes a real nonnegative unit vector v. This preserves every
q_IJ: the selected right phases cancel inside the Gram matrix. It also
preserves Q D_b Q^*, since the spectral coefficients are central.

For each other row x_i=(x_i1,...,x_i4), define the real symmetric matrix

    (E_i)_jk = Re(x_ij conjugate(x_ik)).

For real u,

    u^T E_i u = |sum_j u_j x_ij|^2 >= 0.

Row orthogonality implies E_i v=0. Every E_i has trace one, and column
orthogonality, after taking real parts, gives

    sum_(i != r) E_i = I_4-vv^T.

Here Re(x conjugate(y)) = Re(conjugate(x) y) is the ordinary Euclidean
inner product on H=R^4; this equality is why column orthogonality supplies
the stated real matrix sum despite quaternionic noncommutativity.

Restrict to v-perp and apply the three-effect lemma. Write

    E_i = sum_s lambda_s r_i^(s) (r_i^(s))^T,
    lambda_s >= 0,  sum_s lambda_s = 1,  number of s <= 11,

where the three r_i^(s) form a real orthonormal basis of v-perp. Insert v
as row r to obtain O_s in O(4).

### Preserve the coefficients of every degree

Singletons are preserved because q_({i},{j})(Q)=(E_i)_jj for i!=r; row r
is fixed.

For a pair of rows i,r and columns j,k, the Moore determinant of the two by
two Gram matrix gives, using v_j,v_k real,

    q_({i,r},{j,k})(Q)
      = |x_ij v_k - x_ik v_j|^2
      = (v_k e_j-v_j e_k)^T E_i (v_k e_j-v_j e_k).

This is linear in E_i, so the common decomposition preserves every such
pair minor. Every pair of rows not containing r has a complementary pair
containing r; (2) therefore preserves the remaining pair minors.
Three-minors follow from singleton complementation. Degrees zero and four
are one for every frame.

Thus, simultaneously for every I,J,

    q_IJ(Q) = sum_s lambda_s (det O_s[I,J])^2.              (3)

Flipping a nonfixed row of any determinant-minus-one O_s preserves all
squared minors and the fixed row. Hence all O_s can be chosen in SO(4).

## 5. The exact same-rank transfer theorem

Substituting (3) into (1) proves

    Delta_H(D_a + Q D_b Q^*)
      = sum_s lambda_s det(D_a + O_s D_b O_s^T)            (4)

for every complex a,b, with the same lambda_s and O_s for all spectra.

For fixed a,b define the determinant range over each of the three groups.
The inclusions SO(4) subset U(4) subset Sp(4), together with (4), imply

    conv D_SO4(a,b) = conv D_U4(a,b) = conv D_Sp4(a,b).    (5)

The quaternionic range here uses Delta_H, not an ill-defined ordinary
quaternionic determinant. In particular the three support maxima are equal
for every complex support multiplier eta.

Every permutation product is attained by a signed permutation in SO(4).
Therefore proving any one of the three Jordan MOC4 variants is equivalent
to proving the other two. The result is not merely a comparison of ambient
dimensions or an analogy of group names.

## 6. Attempt to exploit the additional quaternionic directions

The group enlargement preserves the full support maximum, so a real global
maximizer is also a maximizer against all Sp(4) variations. This suggests
using more tangent directions than U(4) supplies. At second order, however,
the enlargement gives no new inequalities.

At a real O, every skew-Hermitian quaternionic generator is uniquely

    Z = X + i Y_1 + j Y_2 + k Y_3,
    X^T=-X,  Y_a^T=Y_a,

with real matrices X,Y_a. Simultaneous conjugation of every quaternionic
entry by a unit quaternion fixes real O and rotates (i,j,k) by an arbitrary
SO(3) rotation. It preserves every Gram-minor coordinate, so it preserves
the determinant support objective for central complex spectra.

The Hessian is invariant under these rotations. There is no invariant
linear functional on the three-dimensional imaginary-quaternion space, so
mixed terms between X and the Y_a vanish. Its invariant bilinear forms are
scalar multiples of the Euclidean inner product, so for some real symmetric
bilinear form H_I and the real-skew block H_R,

    H(Z,Z) = H_R(X,X) + H_I(Y_1,Y_1)
                         + H_I(Y_2,Y_2) + H_I(Y_3,Y_3).   (6)

The U(4) restriction already contains X+iY_1 and hence tests both H_R and
H_I. Thus second-order negativity for Sp(4) is exactly the previously known
complex-unitary condition, repeated three times. Quaternionic directions do
not supply a missing positive second derivative.

At higher order the invariant theory allows mixed contractions of several
imaginary directions. Equation (6) does not settle those terms. No sign
identity or support-preserving transport using them has been proved here.

### A concrete higher-order test, not a closure

For symmetric real Y,Z, the two-unit generator A=iY+jZ satisfies

    A^2 = -(Y^2+Z^2) + k[Y,Z].

Thus mixed quaternionic directions do contain a genuine commutator term.
Let g(T)=F(exp(T)O), and let H,T_3,T_4 be its second, third, and fourth
real derivatives at a critical point. If A belongs to ker H, local
maximality along tA+t^2B requires

    T_3(A,A,A)=0,
    T_4(A,A,A,A)+12 T_3(A,A,B)+12 H(B,B) <= 0

for every B. These follow by Taylor expansion; H(A,B)=0 follows from
H being negative semidefinite and H(A,A)=0. For A=iY+jZ the first identity
also follows from quaternionic conjugation by k, which sends A to -A.
Pure gauge null directions have exact symmetry transports and do not, by
this test alone, yield an escape. No nongauge violation is established for
every irreducible stationary point.

### Exact full-rank flatness criterion

For any fixed v, the arbitrary-spectral support objective is linear in the
three effects. In detail, put

    d_ij = Re eta [a_([4] minus i) b_j + a_i b_([4] minus j)],
    t_(i,jk) = Re eta [a_([4] minus {r,i}) b_j b_k
                      + a_r a_i b_([4] minus {j,k})],
    w_jk = v_k e_j-v_j e_k,

and restrict

    M_i(v) = diag(d_i1,...,d_i4) + sum_(j<k) t_(i,jk) w_jk w_jk^T

 to v-perp, for i!=r. Then

    F_v(E) = c(v) + sum_(i!=r) tr(M_i(v) E_i),
    c(v) = Re eta (a_[4]+b_[4]) + sum_j d_rj v_j^2.

The second term in t_(i,jk) uses complementary row and column pairs, so
every degree-(2,2) coefficient occurs exactly once.

If a maximizing quaternionic frame has all three effects positive definite
on v-perp, it is an interior point of the feasible effect body. A linear
functional attaining its maximum there is constant on the entire body.
Equivalently, there exist a real symmetric Y and scalars alpha_i such that

    M_i(v) = Y + alpha_i I_3  for all i!=r.                (7)

Conversely these identities make the objective constant. Thus, unless the
pairwise differences of the M_i(v) are scalar, every maximizing effect
triple has a rank-deficient member. This is a concrete test for arbitrary
spectra, not an extra restriction on them.

Crucially, rank reduction of effects is not coordinate-block reduction of
the original frame. Every real orthogonal completion already has rank-one
effects, including dense irreducible examples. Even (7), which makes every
completion of v maximizing, does not supply a block-diagonal completion
when v has four nonzero entries. This is the precise failed transfer.

## 7. Why two other apparent transfers do not close the proof

### Polar-orbitope convexity

The three matrix actions are classical polar representations. Kostant's
convexity theorem controls linear projection of an orbit onto its diagonal
section. It does not say that applying a quartic complex determinant to a
sum preserves the corresponding convex-hull relation. Such a conclusion
needs an additional argument. In degree four the independent mixed (2,2)
minor coefficients are exactly what the diagonal projection forgets.

### Rank-three commutation after compression

For the existing fixed-row support SDP, write A for the restriction of
T_beta(v) to v-perp, B for the restriction of p T_(1/beta)(v), and
s=1+v^T D_beta v. Block adjugation gives, when s!=0,

    B = adj(A)/s.

Complex commutation follows, but simultaneous real-orthogonal
diagonalization does not. The actual spectral family can even contain a
nonzero nilpotent A with A^3=0 and B=A^2/s. Its real frame support can be
positive although every joint eigenvalue pair is (0,0). Thus the elementary
rank-three frame-diagonal Jordan theorem cannot simply be applied to this
compressed pair. The hypotheses needed for that theorem are lost.

## 8. Remaining assertion

What remains unproved is, for all a,b in C^4 and every eta,

    max_(O in SO(4)) Re[eta det(D_a+O D_b O^T)]
      <= max_(pi in S_4) Re[eta product_i(a_i+b_pi(i))].

Equations (4)-(6) identify precisely what the proposed same-rank
comparison accomplishes and where its attempted second-order transfer
stops. Neither general MOC4 nor all-dimensional MOC is claimed solved.

## Sources for the imported identities and comparison framework

* Alexander D. Scott and Alan D. Sokal, "Complete monotonicity for inverse
  powers of some combinatorially defined polynomials," expanded version,
  Appendix A, Proposition A.3(a),(d),(e),(g), especially the restricted
  quaternionic Cauchy-Binet formula:
  https://people.maths.ox.ac.uk/scott/Papers/compmono.pdf
  The paper is associated with arXiv:1301.2449; the linked expanded version
  contains appendices omitted from the journal-length version.
* Tim Kobert and Claus Scheiderer, "Spectrahedral representation of polar
  orbitopes," arXiv:2010.02045, Theorem 3.3 and Example 8.6:
  https://arxiv.org/abs/2010.02045
* The real three-effect lemma and complex U(4) application were already
  proved locally in `algebra_unitary_realification.md`. The rank-two and
  rank-three Jordan proofs are in `root_jordan_rank_three.md`.

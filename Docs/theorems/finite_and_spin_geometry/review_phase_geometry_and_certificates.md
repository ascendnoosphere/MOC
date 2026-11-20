## 1. A flat phase circle through a local maximum consists of critical points

Let F(U)=Re(eta det(A+UBU*)) on U(n), for fixed matrices A,B and eta. The argument applies to any real-analytic objective on U(n). Suppose U_0 is a local maximum and P is a rank-one orthogonal projector such that

    F(exp(i theta P)U_0)=F(U_0)

for every theta. Then every point of this entire circle is a stationary point of F.

Indeed, a neighborhood N of U_0 satisfies F<=F(U_0). A small arc of the circle lies in N. Each point on that arc is therefore itself a local maximum: a sufficiently small neighborhood of the point remains in N. For any fixed skew-Hermitian K, the function

    theta -> d/dt F(exp(tK) exp(i theta P) U_0)|_(t=0)

is real analytic and vanishes on that arc. The identity theorem makes it vanish on the full circle. Taking a real basis of skew-Hermitian K proves stationarity at every point.

The Hessian need not remain negative along the entire circle. For example, the two-phase scalar function

    -(1-cos(phi)) cos(theta)

is flat on phi=0 and has a local maximum at the origin, but its transverse Hessian changes sign by theta=pi. Thus flat transport can reach a stationary point with an improving transverse direction. The lemma supplies a structure for such transport, not a theorem that it always reaches a permutation maximum.

## 2. Exact rigidity on a torus with flat coordinate faces

Let P_1,...,P_k be mutually orthogonal rank-one projectors, and put

    G(theta)=I+sum_j (exp(i theta_j)-1)P_j,
    f(theta)=Re(eta det(A+G(theta) B G(theta)*)).

For each phase separately, f has Fourier frequencies only -1,0,1. To see this, hold the other phases fixed and put the relevant projector first in an orthonormal basis. A bordered determinant expansion contains one row phase and one column inverse phase; after expansion the only possible powers are z^-1,1,z. Orthogonality makes the phase updates commute, so this argument applies to each variable simultaneously.

Assume:

1. theta=0 is a local maximum of f on this torus.
2. For each j, the coordinate hyperface theta_j=0 is identically flat at f(0), at least in a neighborhood of zero.

Then there exists c>=0 such that, for every theta,

    f(theta)=f(0)-c product_j sin^2(theta_j/2).

Here is a short complete proof. Set x_j=tan(theta_j/2) and multiply f(theta)-f(0) by product_j(1+x_j^2). The result H(x) is a real polynomial of degree at most two in every variable. The flat-face hypothesis makes H vanish when any x_j is zero. Nonpositivity near the origin forces the coefficient of the first power of x_j to vanish identically: otherwise, fix sufficiently small other coordinates where that coefficient is nonzero and change the sign of x_j. Thus x_j^2 divides H for every j. The degree bounds leave

    H=-c product_j x_j^2,

and local nonpositivity gives c>=0. Division gives the formula wherever the half-angle coordinates are finite, and continuity includes the missing phase values.

For k=2 the flat-face assumption simply says that the two individual phase axes are flat. In the explicit plateau example from continuous_plateau_transport.md,

    f=7+(24/25)^2 sin^2(theta_1/2) sin^2(theta_2/2).

Its coefficient has the opposite sign, so this torus already proves that the base point is not a local maximum. The gain starts at fourth order along the equal-phase diagonal. For k>2, flat individual axes alone are insufficient: the hypothesis concerns every coordinate hyperface, including all mixed lower-dimensional directions on it.

## 3. The rank-one trap and the two exact escapes are valid

The continuous note's general rank-one phase formula follows by putting the phase vector first in a block decomposition. With z=exp(i theta), the determinant is

    (a+b)det(M_0)-(r+zt)adj(M_0)(s+z^-1 u),

which is first harmonic even if M_0 is singular. At a stationary point its real support gap is sin^2(theta/2) times its Householder gap.

For the stated Walsh-Hadamard configuration, the Householder gap is the exact complex polynomial

    16|v_1v_3-v_2v_4|^2+12|v_1v_4-v_2v_3|^2.

Its bilinear expressions contain no internal conjugates. This is a certificate for every complex phase vector, not merely for real rotations. Together with the displayed Hermitian commutator, it excludes every improving single rank-one phase update while the permutation support ceiling is eight and the current support is seven.

The zero set consists of the four stated complex planes. If the top and bottom coordinate pairs are both nonzero, the two equations reduce to a two-by-two homogeneous system of determinant v_1^2-v_2^2. Therefore v_2=+v_1 or -v_1, with the same sign relating v_4 and v_3. The cases of a zero top or bottom pair give the other two planes.

The orthogonal two-phase factorization is also correct: in the plus/minus block basis, one phase acts only on the block whose determinant begins at seven and the other only on the block whose determinant begins at one. Their determinant factors are 7-i kappa s_1 and 1+i kappa s_2. The product produces the positive mixed fourth-order term in Section 2.

The real rank-two commutant completion is valid because both [Z,A]=0 and [Z,K_4]=0 hold. Thus exp(theta(K_4+Z)/2) differs in the objective from exp(theta K_4/2) only by a factor commuting with A. The generator has rank two, yielding the exact monotone path 7+sin^2(theta)-6i sin(theta). This argument uses the repeated eigenvalues of A. Its commutant is not available in the same form after a generic splitting of those eigenvalues.

## 4. The Schur-feedback torus criterion

Partition a unitary matrix as

    U=[[A,B],[C,E]],

with all blocks two by two. Seek a diagonal unitary diag(z,w,z_3,z_4) whose difference from U has rank at most two. If X=A-diag(z,w) is invertible, Schur complementation requires

    S(z,w)=E-C X^-1 B=diag(z_3,z_4).

For |z|=|w|=1, S is unitary whenever defined. An energy proof is immediate: if the internal input x solves Xx=-By, then the first output of U(x,y) is diag(z,w)x, which has the same norm as x. The remaining output Sy therefore has norm equal to that of y.

A two-by-two unitary S is diagonal exactly when one of its off-diagonal entries is zero. Clearing det(X) from S_12 gives

    p(z,w)=alpha z w+beta z+gamma w+delta,

where, with one-based indices,

    alpha=U_34,
    beta=-det U[23,24],
    gamma=-det U[13,14],
    delta=det U[123,124].

There is a point on the two-torus with p=0 if and only if

    |C_0|<=2|D_0|,

where

    C_0=|beta|^2+|delta|^2-|alpha|^2-|gamma|^2,
    D_0=beta conjugate(delta)-alpha conjugate(gamma).

Indeed solve w=-(beta z+delta)/(alpha z+gamma). The modulus-one condition is

    C_0+2 Re(D_0 z)=0.

Its range on the unit circle is [C_0-2|D_0|,C_0+2|D_0|]. If the denominator vanishes at a solution, the numerator vanishes as well, and p is then zero for every w at that z; hence the torus-zero criterion itself still has no exception. Such a zero need not lie in the regular feedback chart, which is why the next section is needed for a rank-completion obstruction.

## 5. Off-diagonal invertibility excludes every hidden Schur pole

Let M=[[X,B],[C,Y]] have rank at most two and assume B and C are invertible. Its last two columns form a basis of its column space, so

    M=[[B],[Y]] [B^-1 X, I].

In particular C=YB^-1X. Since C is invertible, X and Y are invertible as well. Therefore every rank-two diagonal completion is in the regular feedback chart if B,C are invertible.

If all thirty-six two-by-two minors of U are nonzero, this conclusion applies after every column permutation. Thus a negative torus discriminant for all twenty-four permutations really excludes every monomial unitary completion of rank at most two; a singular internal block cannot bypass the certificate.


## 7. The exact complex facet certificate requires no realification theorem

For the data beta and lambda in dual_boolean_facet_rank_one_proof.md, gauge the anchor row v real by column phases. Put P=I-vv^T and y=PKv, where K_12=177/5, K_21=-66, and the other entries vanish. The two real symmetric compressed objectives are M_v and L_v.

The certified Gram identities prove, for every real r perpendicular to v,

    r^T(alpha(v)I-M_v+(Kv)(Kv)^T)r>=0,

and the analogous statement with gamma and L_v. Projection of Kv onto v-perp does not change this quadratic form. A real positive semidefinite matrix is positive semidefinite on the complexification as well: substitute r=x+iy and add the real inequalities for x and y. Thus the certificate controls arbitrary complex remaining rows directly.

For complex orthonormal rows r,s,t in v-perp,

    r* M_v r+s* L_v s
    <=alpha+gamma+|r*y|^2+|s*y|^2
    <=alpha+gamma+||y||^2
    =2850-(23409/25)v_1^2 v_2^2.

The independent script checks all pair Gram blocks, the restrictions of both diagonal Gram matrices to sum d_i=0, and the exact constant budget. The criterion itself follows by writing z_ij=r_i v_j and d_i=r_i v_i: z_ij z_ji=d_i d_j permits each pair allocation, and orthogonality gives sum d_i=0. This is an actual support inequality for every U(4), not merely for orthogonal matrices.

The claimed completeness of the Gram format within the bilinear-SOS class is also justified. Averaging a certificate over simultaneous coordinate sign changes splits its bilinear monomials into the diagonal character space and the pair character spaces span(z_ij,z_ji). The only remaining diagonal-block freedom is a multiple of (sum d_i) times a linear form in d. A Gram form positive on 1-perp can be extended positively to the full space by changing precisely such a multiple. This does not assert that every nonnegative orthogonal biquadratic is SOS.

## 8. Equality and local openness of the certified facet

The reciprocal diagonal Gram is positive definite on 1-perp. At equality this forces s_i v_i=0 for every i. Its strict pair blocks and one-entry blocks then leave only four potentially nonzero incidence products:

    s_1 v_2, s_2 v_3, s_2 v_4, s_4 v_1.

The unit-norm conditions force one of three patterns: v=e_1 with s=e_4; v=e_2 with s=e_1; or v in span(e_3,e_4) with s=e_2, up to phases. The first slack forces r=e_2, r=e_3, or r in span(e_3,e_4) perpendicular to v, respectively. These are exactly phased permutations 2143,3214 and the single U(2) block joining 3421 to 4321.

The note's quantitative gap estimate is sufficient for local openness. The reciprocal slack bounds a positive multiple of the sum of all forbidden |s_i v_j|^2. Near the U(2) family this controls

    v_1^2+v_2^2+1-|s_2|^2.

The first slack additionally controls |r_1|^2. Row and column orthonormality then control every off-block entry. At the two isolated phased-permutation families, the strict first-slack pair blocks control the remaining missing row coordinates. Hence the support Hessian is strictly negative in every normal direction at the equality set.

For arbitrary nearby beta and lambda, each equality block family retains a common permutation law and every off-block first derivative of the squared-minor objective is zero. A nonzero balanced minor has no off-block first-order determinant variation; a zero minor has zero first derivative of its squared modulus. The same tubular-neighborhood and compactness argument as in the first review batch proves an open neighborhood of this support instance. It does not prove all support directions at the nearby spectra.

## 9. Audits of the categorical and holomorphic statements

### Reality, positivity, and the Grace tangent cone

Normalization fixes the leading coefficient of Q(x+t1) to 2^n. Homogeneous stability supplies both upper- and lower-half-plane nonvanishing, forcing all roots of this univariate polynomial to be real and therefore Q to have real coefficients. Positivity on the positive orthant and squarefree homogeneity then force each Boolean coefficient to be nonnegative. The two normalization identities give both stochastic sums.

The first-order Rayleigh identity at the identity kernel is correct. Its sign implies divisibility by every outside factor a_k+b_k. Multiaffinity removes outside-variable dependence from the quotient, and translation covariance reduces that quotient to a nonpositive multiple of (b_i-b_j)^2. Subtracting the corresponding transposition symbols leaves a homogeneous polynomial in the intersection of the pair ideals (c_i,c_j). The ideal argument and normalization remove the remainder. Thus the contingent tangent cone really is the nonnegative cone of transposition generators.

The continuous-divisibility conclusion holds with the usual integration hypotheses, for example a C^1 evolution or locally integrable rates in a locally absolutely continuous evolution. The theorem in `categorical_grace_tangent_trace.md` explicitly assumes continuous differentiability. The autonomous semigroup conclusion needs no additional nonautonomous regularity qualification.

### Optimal finite phase designs have uniform weights

The universal quadrature lower bound follows from the middle-level subset characters being orthonormal. If the number N of positive-weight nodes equals the number M=binom(n,floor(n/2)) of those characters, form the square matrix Phi of character values. The moment identity is Phi W Phi*=I. Hence Phi sqrt(W) is unitary. Every entry of Phi has modulus one, so each column has squared norm M. Its normalization forces every weight to equal 1/M.

Thus every optimal six-node positive phase quadrature in dimension four has equal weights 1/6 and a complex Hadamard matrix of middle-level characters. The displayed cyclic design achieves this. The lower bound concerns a universal phase quadrature, not the smallest mixture needed for an individual pair of kernels.

### Ordinary trace, conic normal forms, and scalar deletion

The two-unitary ordinary-trace formula is correct, including the boundary |alpha|=1, where unitarity makes the off-diagonal coupling vanish and the remaining unitary decouples. A rank-one weighted trace does not retain the same normalized equivariant class; the two-site swap example demonstrates the obstruction exactly.

The Cl2 affine-plane classification correctly uses a traceless matrix normal to the plane. A nonnilpotent normal gives constant diagonal idempotents and proportional paired spectra; a nilpotent normal gives constant lower-left entries and constant paired sums. The degenerate constant-diagonal conic can contain both branches, so it must not be called simultaneously triangular without an invariant-line argument. The actual simultaneous-triangular case has cycle values zero or one and target |det U[A,A]|^2, proving its scalar hull assertion.

Finally, the degree-independent holomorphic CMC bound is sound. On either parent side the normalization has real rank d and the variable compressed matrix lies in a complex space of dimension at most d. The minimum-face lemma therefore retains at most 2d labels. Applying it sequentially on both parents preserves the strict scalar violation and cannot increase either previously reduced parent size. This is a finite witness reduction for fixed compression rank, not a reduction of that rank itself.

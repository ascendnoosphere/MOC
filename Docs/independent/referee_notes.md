# Independent referee notes on MOC

These notes contain checked reductions and special cases, not a general solution.

## 1. Rank-two normal perturbations admit a common assignment law

Let x,y in C^n be orthonormal. Put

q_ij = |x_i y_j - x_j y_i|^2, i<j.

There are nonnegative p_ij, i != j, such that

* p_ij+p_ji=q_ij;
* sum_{j != i} p_ij=|x_i|^2;
* sum_{i != j} p_ij=|y_j|^2;
* sum_{i != j} p_ij=1.

Proof: Regard every unordered edge {i,j} as mass q_ij which must be assigned between its two endpoints. Assigning mass to i means assigning the first exceptional eigenvalue to i and the second to j. The prescribed vertex masses are r_i=|x_i|^2. The source-edge-vertex-sink flow network has source-to-edge capacity q_ij, edge-to-each-endpoint infinite capacity, and vertex-to-sink capacity r_i. A full flow exists exactly when, for every vertex set S, the mass of the edges lying entirely in S is at most sum_{i in S} r_i, and the totals agree. Indeed finite cuts are equivalent to those inequalities, and max-flow/min-cut applies.

Let X_S=sum_S |x_i|^2, Y_S=sum_S |y_i|^2, Z_S=sum_S conjugate(x_i)y_i. Cauchy--Binet gives

sum_{i<j in S} q_ij=X_S Y_S-|Z_S|^2 <= X_S,

because Y_S<=1. The total edge mass is det([x y]^*[x y])=1. This proves the required flow. Also sum_{j != i}q_ij=|x_i|^2+|y_i|^2, so the second marginal follows from the first.

Consequently, if C=diag(c_i),

det(C+delta_1 xx^*+delta_2 yy^*)
 = sum_{i != j} p_ij (c_i+delta_1)(c_j+delta_2) product_{ell != i,j} c_ell.

To verify, both sides have the same constant, delta_1, delta_2, and delta_1 delta_2 coefficients by the determinant expansion and the four identities above. No invertibility hypothesis is required.

This proves MOC whenever n-2 eigenvalues of one matrix coincide, an established case of Kovacec (1994), DOI 10.1016/0024-3795(94)90107-4. For n=4, any counterexample must therefore have both spectra simple.

## 2. Commuting-vertex Hessian

Let A=diag(a_i), B=diag(b_i), K^*=-K, U(t)=exp(tK), and z_id=product_i(a_i+b_i). Then

det(A+U(t)BU(t)^*)
 = z_id + t^2 sum_{i<j}|K_ij|^2(z_(ij)-z_id) + O(t^3).

Here

z_(ij)-z_id=(a_j-a_i)(b_j-b_i) product_{ell != i,j}(a_ell+b_ell).

Derivation: [K,B]_ij=K_ij(b_j-b_i), and the diagonal of [K,[K,B]]/2 is sum_j |K_ij|^2(b_j-b_i). In the determinant expansion, combine these second-order diagonal terms with products of two first-order off-diagonal terms. The coefficient for the pair i,j becomes exactly the displayed transposition difference. This is a polynomial computation, so zero diagonal entries cause no exception.




A higher-order local consequence follows if the identity is a maximum among all permutation vertices in the chosen supporting direction. Take K with zero diagonal, as is natural in local coordinates on the unitary orbit of a simple diagonal B. If its second-order supporting coefficient vanishes, every edge ij with K_ij nonzero has zero transposition gap. The third-order coefficient also vanishes. To see this, invariance under K -> D K D^* for diagonal unitary D forces every degree-three Taylor monomial to be a balanced closed walk; with zero diagonal these are triangles. Therefore the cubic coefficient is the sum of the coefficients obtained from the three-index principal restrictions of K. For each such restriction, the 3-by-3 MOC applies, while the fixed remaining diagonal factors multiply its supporting direction. Its identity vertex is support-maximizing, and its second-order coefficient vanishes. An analytic real function bounded above by its value at zero cannot have a nonzero cubic leading coefficient. Every triangle coefficient is consequently zero. Thus an outward local violation under these hypotheses would first occur at order at least four.

The 3-by-3 enclosure used here has an elementary independent proof: choose Birkhoff weights for the doubly stochastic matrix |U_ij|^2. They match the one-minor marginals, and complementary-minor identities for a unitary match the two-minor marginals with the same weights. The determinant expansion completes the proof. This argument does not invoke general MOC.

## 3. Exact integer counterexample certificates lose no generality

If any strict MOC violation exists, one exists with Gaussian-rational spectra and a Gaussian-rational unitary. A scalar phase first moves the target unitary away from eigenvalue -1 without changing its conjugation action. The inverse Cayley transform is skew-Hermitian. Approximate its independent real coordinates rationally and apply the Cayley transform to get exact rational unitaries converging to the target. Approximate the spectra and a strictly separating complex supporting direction rationally. Strict separation survives continuity.

Equivalently, there exist Gaussian integers alpha_i,beta_i,c and a Gaussian-integer matrix M, with a positive integer q such that MM^*=q^2 I, and

Re(c det T) > q^(2n) Re(c product_j(alpha_{pi(j)}+beta_j))

for every permutation pi, where

T=q^2 diag(alpha)+M diag(beta)M^*.

The associated normal matrices are A=diag(alpha) and U diag(beta)U^*, U=M/q. Common denominators of the original rational spectra can be absorbed by a common scaling, so integer spectra suffice. These are finitely many strict integer inequalities and an exact integer unitarity identity. They give an exact finite formulation of the conditional violation.

## 4. Independent check of the Fourier F5 assignment law

Take U_ij=omega^(ij)/sqrt(5), omega=exp(2pi i/5), indexed by F5, and weights

p_{pi_{r,s}}=(2/25)sin^2(pi r/5), pi_{r,s}(j)=rj+s,

for r in F5\{0}, s in F5, all other permutations having zero weight. This construction checks exactly:

* The weights sum to one because sum_{r=1}^4 sin^2(pi r/5)=5/2.
* For any fixed j->i, one intercept s exists for each r, giving probability 1/5.
* If the row-set difference is d and column-set difference is e, two affine maps carry the two-set to the row-set, with slopes plus/minus d/e. Their weight sum is (4/25)sin^2(pi d/e/5). Since e^2 is plus/minus 1 in F5, d/e equals plus/minus de modulo 5. This equals the squared Fourier 2-minor, (4/25)sin^2(pi de/5).
* Complementary minors of a unitary have equal absolute values, and permutation set-images also complement, so sizes 3 and 4 follow. Sizes 0 and 5 are immediate.

Therefore all squared-minor marginals are matched for this specific unitary, and the MOC inclusion follows for arbitrary spectra with relative eigenbasis F5. No general-unitary conclusion follows.

## 5. Four-cycle quartic formula and exact scalar criterion

Let Delta_pi=Re(c(z_pi-z_id)), assume every permutation gap is nonpositive, and assume the four cycle-edge transposition gaps Delta_12,Delta_23,Delta_34,Delta_14 vanish. Let the real skew matrix K have independent entries K12=x,K23=y,K34=z,K14=w, with the other two independent entries zero. The coefficient of t^4 in Re(c(det(A+exp(tK)B exp(-tK))-z_id)) is

F4 = ((xy-zw)^2/4) Delta_13 + ((yz-xw)^2/4) Delta_24
     + x^2 z^2 Delta_(12)(34) + y^2 w^2 Delta_(14)(23)
     + xyzw (Delta_(1234)+Delta_(1432)).

Independent derivation: K^2_13=xy-wz and K^2_24=yz-xw. Each opposite transposition initially contributes minus one quarter the corresponding squared K^2 entry. The two pairs of oriented triangles contribute plus one half that square after using

z_(ijk)+z_(ikj)=z_(ij)+z_(ik)+z_(jk)-z_id

and the four flat-edge assumptions. The net coefficient is therefore plus one quarter. The two double transpositions have positive coefficients x^2z^2 and y^2w^2, and each oriented four-cycle has coefficient xyzw. Remaining identity and edge contributions disappear after subtracting z_id and using the flat-edge assumptions.

Set a=-Delta_13, b=-Delta_24, c0=-Delta_(12)(34), d=-Delta_(14)(23), e=-Delta_(1234)-Delta_(1432), all nonnegative. Then F4<=0 for every real x,y,z,w if and only if

e <= a+b+2 sqrt(c0 d).

For xyzw>=0 all terms have the correct sign. If P=xyzw<0, then

(xy-zw)^2 >= 4|P|,
(yz-xw)^2 >= 4|P|,
c0 x^2z^2 + d y^2w^2 >= 2|P|sqrt(c0 d).

These establish sufficiency. Necessity follows by taking |x|=|z|, |y|=|w|, P<0, and |x|^2/|y|^2=sqrt(d/c0), which simultaneously attains all three bounds when c0,d>0. If either vanishes, the same bound is approached by an extreme ratio; a strict violation of the scalar condition still yields F4>0 for some finite ratio. This criterion is an exact conditional reduction, not a proof that the spectral hypotheses imply its scalar inequality.

## 6. Exact audit of the quaternion two-parameter family

Let

M = [[1,-2,-2,-2], [2,1,-2,2], [2,2,1,-2], [2,-2,2,1]],
U=M/sqrt(13), A=diag(0,1,2,t), B=diag(0,1,i s,2+i s).

The four one-based permutations (1,3,4,2), (3,4,1,2), (3,4,2,1), (4,1,3,2) have respective vertices

0,
(-2s^2+6is)(1+t),
(4-2s^2+6is)(1+t),
(6-s^2+5is)t.

Weights [29,52-3s^2,36+3s^2,52]/169 sum to one and are nonnegative for real s satisfying 3s^2<=52. Their weighted sum is

[144-164s^2+528is + (456-216s^2+788is)t]/169.

This equals the determinant exactly. Independent verification used Gaussian-rational arithmetic to evaluate det((a_i+b_j)M_ij) at the six nodes s=0,1,2 and t=0,1. Both that determinant and the asserted numerator have degree at most two in s and at most one in t, so the six exact equalities certify the polynomial identity. The weighted vertex formula was also expanded directly. This is a verified family for all complex t and the stated real s range, not a claim of novelty or a general proof.

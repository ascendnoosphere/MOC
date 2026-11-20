# A global fixed-three-plane formulation of unrestricted MOC4

**Status: reduction proved using a published external theorem. The remaining inequality is NOT proved.** This is a global cover, unlike the earlier fixed-two-plane certificates. No claim of novelty in the literature.

## 1. External theorem actually used

Martin Idel and Michael M. Wolf, *Sinkhorn normal form for unitary matrices*, arXiv:1408.5728v3, Theorem 2, states: for every U in U(n), diagonal unitaries L,R exist such that W=LUR has every row and column sum equal to 1. The proof combines Lemma 1 (equivalence to an intersection of Clifford tori), non-displaceability of the Clifford torus, and the Hamiltonian action of the unitary group. The theorem has no genericity, nonzero-entry, or convergence assumption. Its iterative scaling algorithm is NOT asserted always to converge.


## 2. Exact full-range reduction

Let A=diag(a), B=diag(b), and F(U)=det(A+UBU*). For diagonal unitaries L,R,

    F(LUR)=det(L(A+UBU*)L*)=F(U).

Thus both phase gauges are valid, with no restriction on the complex spectra.

Put

    e=(1,1,1,1)^T/2,
    Y=(1/2) [[ 1, 1, 1],
             [-1, 1,-1],
             [ 1,-1,-1],
             [-1,-1, 1]],
    H=[e Y].

H is real orthogonal, Y^T Y=I3, and YY^T=I4-ee^T. If W is unitary and We=e, then also W*e=e. Consequently

    H^T W H = diag(1,V),  V in U(3),
    W(V)=ee^T+Y V Y^T.

Conversely every W(V) is unitary and fixes e. Therefore, for EVERY fixed pair of spectra,

    {F(U):U in U(4)} = {F(W(V)):V in U(3)}.             (1)

No density argument is needed for (1); it is exact, including singular sums and repeated eigenvalues. All 24 permutation matrices themselves fix e, so all target permutation products occur in this subgroup too.

For every support scalar eta, let h=max_pi Re(eta product_i(a_i+b_pi(i))). Unrestricted MOC4 is exactly the assertion

    Re(eta F(W(V))) <= h  for all a,b,eta and V in U(3). (2)

**This is not the known MOC3 theorem.** The compressed matrices below are generally nonnormal and the determinant remains four-dimensional with a coupled border.

## 3. Explicit reduced determinant: a coupled 3x3 border

Define the Hadamard spectral coordinates

    s_a=(a1+a2+a3+a4)/4,
    x_a=(a1-a2+a3-a4)/4,
    y_a=(a1+a2-a3-a4)/4,
    z_a=(a1-a2-a3+a4)/4,
    u_a=(x_a,y_a,z_a)^T,
    M_a=[[s_a,z_a,y_a],[z_a,s_a,x_a],[y_a,x_a,s_a]],

and likewise for b. Then

    H^T A H = [[s_a,u_a^T],[u_a,M_a]].

In particular

    F(W(V)) = det [[s_a+s_b, u_a^T+u_b^T V*],
                    [u_a+V u_b, M_a+V M_b V*]].       (3)

Every quantity in (3) is explicit in the original eight eigenvalues. The transpose u_a^T is NOT u_a*: the spectral entries may be complex. Replacing it by an adjoint or discarding the border would change the problem.

## 4. Equivalent nine-real-variable sextic inequality

For Hermitian T of size 3, set S=YTY^T and

    V=(I+iT)(I-iT)^(-1),
    W=(I+iS)(I-iS)^(-1),
    C0=A+B, D=A-B,
    K(T)=C0+i[D,S]+S C0 S,
    d(T)=det(I3+T^2)>0.

Multiplying the matrix sum on the left by I-iS and on the right by I+iS gives the exact identity

    det K(T) = d(T) F(W(V)).                           (4)

Hence (2) for the dense Cayley chart is equivalent to

    G(T)=h d(T)-Re(eta det K(T)) >= 0.                  (5)

Continuity extends (5) to unitary V with eigenvalue -1. Conversely a proof of unrestricted MOC4 implies (5), so this is an equivalence, not just a sufficient relaxation.

For clarity, write H^T C0 H=[[c,r^T],[r,M]] and H^T D H=[[d,s^T],[s,N]]. Then

    H^T K(T) H =
       [[c, r^T+i s^T T],
        [r-i T s, M+i(NT-TN)+TMT]].                   (6)

The determinant in (6) has degree at most six in the nine real entries of T: the c term uses three bottom-block factors of degree <=2; a term using both border factors uses two further bottom-block factors. Thus (5) is an explicit real sextic, with parameters a,b,eta and the maximum of 24 explicitly known numbers. No denominator or inverse of A+B is required.

If the identity is a maximizing permutation, G(0)=0 and its degree-one homogeneous part vanishes. The latter is the exact zero first variation at a commuting configuration, even when A+B is singular. Its quadratic part is the already-known transposition-gap Hessian restricted to this fixed three-plane. Establishing the whole sextic's nonnegativity from product-linked support constraints is the still-open step.

## 5. A useful exact leading-term certificate

Let R0=2ee^T-I4=(1/2)11^T-I4. Along T -> tT with T invertible, W -> R0. Polynomial identity then implies that the degree-six homogeneous part of G is

    G_6(T) = [h-Re(eta F(R0))] det(T)^2.               (7)

This coefficient is always nonnegative, and can be certified with a single explicit permutation law:

    F(R0) = (1/8) sum_(pi a 3-cycle in S4) product_i(a_i+b_pi(i)). (8)

There are eight 3-cycles. To prove (8), expand the determinant by complementary minors. R0 has all entry moduli squared 1/4. Its 2x2 minor indexed by row set I and column set J has squared modulus 1/4 exactly when |I intersect J|=1, and zero otherwise. A uniform random 3-cycle has those same singleton and two-set assignment probabilities; size-three probabilities follow by complements. Size zero/four are 1. Thus the complementary-minor expansions agree coefficient by coefficient. This also supplies (8) when spectral entries vanish.

Identity (8) proves only the leading coefficient, not the cubic, quartic or quintic terms of (5). Nonnegative leading term plus nonnegative quadratic term does NOT by itself imply a nonnegative sextic.


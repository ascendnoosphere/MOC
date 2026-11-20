# Quaternionic determinant conventions and valid theorems

## Fix the determinant before posing the conjecture

For M=X+Yj with complex matrices X,Y, use the complex representation

    chi(M) = [[X,Y],[-conj(Y),conj(X)]].

This is a real algebra homomorphism compatible with adjoints. Define explicitly

    S(M) = sqrt(det_C chi(M)) = product_i s_i(M),

where s_i(M) are the quaternionic singular values. This normalization is commonly called the Study determinant and extends |det_C| on complex matrices. Terminology and powers vary between authors; the displayed formula fixes the convention.

For quaternionic Hermitian H, its eigenvalues lambda_i are real. The Moore determinant is

    Mdet(H)=product_i lambda_i.

It can be negative, and S(H)=|Mdet(H)|. General normal matrices do not carry this same signed Hermitian determinant.

A quaternionic right eigenvalue is a conjugacy class. Its standard complex representative is alpha+i beta with beta>=0. Quaternionic unitary conjugation can rotate its imaginary direction.

Primary determinant reference: N. Cohen and S. De Leo, The quaternionic determinant, Electronic Journal of Linear Algebra 7 (2000), 100–111; https://www.ime.unicamp.br/~deleo/Sissa/s29.pdf (also arXiv:math-ph/9907015). Primary quaternionic spectral theorem: D. Farenick and B. Pidkowich, The spectral theorem in quaternions, LAA 371 (2003), 75–102, DOI 10.1016/S0024-3795(03)00420-8.


## The complete scalar replacement

Let a=alpha+i beta and b=gamma+i delta, with beta,delta>=0. As q ranges over unit quaternions, q b conjugate(q)=gamma+delta v ranges over the conjugacy sphere, where v is any unit imaginary quaternion. Therefore

    |a+q b conjugate(q)|^2
      =(alpha+gamma)^2+beta^2+delta^2+2 beta delta cos(theta).

Every cos(theta) in [-1,1] occurs. The exact range of S(a+q b q*) is consequently

    [ sqrt((alpha+gamma)^2+(beta-delta)^2),
      sqrt((alpha+gamma)^2+(beta+delta)^2) ]
    = [ |a+conj(b)|, |a+b| ].

Allowing independent conjugate choices is necessary to capture even the scalar orientations, but it does not yield the naive absolute-value interval in higher dimensions.


## A valid full all-dimensional analogue for Hermitian matrices

For quaternionic Hermitian A,B with real eigenvalues a_i,b_i, the Moore determinant satisfies

    min_sigma product_i(a_i+b_sigma(i))
      <= Mdet(A+B)
      <= max_sigma product_i(a_i+b_sigma(i)).

This is an established theorem: David Sossa, A Fiedler-type determinantal inequality in Euclidean Jordan algebras, LAA 667 (2023), 151–164, DOI 10.1016/j.laa.2023.03.011, Theorem 1. The theorem covers every Euclidean Jordan algebra, explicitly including all quaternionic Hermitian matrix algebras and the exceptional 3-by-3 octonionic Hermitian Jordan algebra. It is not a theorem about arbitrary normal quaternionic matrices.

Primary theorem page:
https://www.sciencedirect.com/science/article/abs/pii/S0024379523000952
Author's publication list:
https://sites.google.com/site/davidsossa/papers

Writing m and M for the two permutation extrema, the full Moore-determinant range over quaternionic unitary conjugations of B is exactly [m,M]. The endpoint values are attained by permutation matrices, while the quaternionic unitary group Sp(n) is connected and the determinant is continuous.

Consequently the exact Study-determinant range for this Hermitian orbit is the absolute-value image of [m,M]:

    [0,max(|m|,|M|)]                    if m<=0<=M,
    [min(|m|,|M|),max(|m|,|M|)]         otherwise.


## A short self-contained proof in the positive-semidefinite case

Assume A,B are quaternionic Hermitian positive semidefinite, with eigenvalues a_1>=...>=a_n>=0 and b_1>=...>=b_n>=0. Then

    product_i(a_i+b_i)
       <= Mdet(A+UBU*) = S(A+UBU*)
       <= product_i(a_i+b_(n+1-i)).

Proof. First replace A by A+epsilon I, epsilon>0, so H=A+UBU* is positive definite for every U. The minimum and maximum exist by compactness. Write C=UBU*. For a skew-Hermitian quaternionic K, vary C through exp(tK) C exp(-tK). The complex representation gives

    d/dt log Mdet(H(t)) at t=0
      = Re Tr(H^{-1}[K,C])
      = Re Tr([C,H^{-1}] K).

The commutator L=[C,H^{-1}] is skew-Hermitian. At an extremum this derivative vanishes for all skew-Hermitian K; taking K=L* forces Re Tr(L L*)=0 and hence L=0. Thus C commutes with H, and therefore with A. Commuting quaternionic Hermitian matrices are simultaneously unitarily diagonalizable, so every extremal determinant is a permutation product.

For nonnegative real numbers, interchanging two pairings gives

    (a+b)(a'+b')-(a+b')(a'+b)=-(a-a')(b-b').

Successive swaps show that equal ordering minimizes the positive product and opposite ordering maximizes it. Letting epsilon decrease to zero proves the assertion for positive-semidefinite inputs. This proof does not resolve the arbitrary-normal case.

## A further normal-matrix upper bound with one exceptional real eigenvalue

Let A be any quaternionic normal n-by-n matrix, and let B be quaternionic Hermitian with real spectrum gamma,beta,...,beta. If a_1,...,a_n are the standard complex right eigenvalues of A, then for every quaternionic unitary U,

    S(A+UBU*)
      <= max_i [ |a_i+gamma| product_(j!=i)|a_j+beta| ].

More explicitly, after diagonalizing A and writing UBU*=beta I+(gamma-beta)vv* with v*v=1, the upper bound is the convex average

    S(A+UBU*)
      <= sum_i |v_i|^2 |a_i+gamma| product_(j!=i)|a_j+beta|.

Proof. Put C=diag(a_i+beta), delta=gamma-beta. When C is invertible, the Study determinant's Schur-complement identity gives

    S(C+delta vv*) = S(C) |1+delta v*C^{-1}v|.

Write v_i=sqrt(w_i)q_i with w_i=|v_i|^2 and q_i unit whenever w_i>0. Because beta,delta are real and sum_i w_i=1,

    1+delta v*C^{-1}v
      =sum_i w_i q_i* (1+delta/(a_i+beta)) q_i.

The quaternion norm triangle inequality gives the convex-average bound. Continuity removes the invertibility assumption. This proves only the stated upper bound.

## Scope

These theorems concern the stated scalar, Hermitian, and exceptional-real-eigenvalue cases. They do not establish a general quaternionic-normal MOC theorem.

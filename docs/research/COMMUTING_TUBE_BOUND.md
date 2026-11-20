# An explicit fixed-direction exclusion tube around a strict commuting contact

**Restricted local theorem, NOT unrestricted MOC.** The contribution is an elementary explicit radius, including singular matrix sums.

## Original target and limited use

For arbitrary complex spectra a,b of length n, every unitary U, and every support scalar eta, unrestricted MOC asks

    Re(eta det(D_a+U D_b U*)) <= h = max_pi Re(eta z_pi),
    z_pi = product_i (a_i+b_{pi(i)}).

This note proves that inequality for a **fixed direction** in a quantified neighborhood of a maximizing permutation whose transposition gaps are strictly positive. It excludes only that neighborhood from a possible strict violation. It neither controls noncommuting contacts away from the tube nor handles directions with vanishing transposition gaps. One must not minimize the radii over all directions and assume the minimum is positive.

## Statement

Let n>=2, eta!=0. Relabel b so that the identity maximizes Re(eta z_pi). Put

    delta_ij = Re(eta (z_id-z_(ij))),
    delta = min_(i<j) delta_ij > 0,
    R = max_i |a_i| + max_j |b_j|.

Give U(n) its bi-invariant Frobenius metric, and let T be the diagonal unitary torus. Define

    r = 3 delta / (16 |eta| n^3 R^n).

Then, whenever d(U,T)<=r,

    Re(eta det(D_a+U D_b U*))
       <= h - (delta/4) d(U,T)^2.

At d=0 the right hand side is h. No paired sum a_i+b_j, determinant, or eigenvalue needs to be nonzero. R>0 follows from delta>0. Right diagonal phases do not affect U D_b U*.

For a different maximizing permutation P, relabel columns; the corresponding right-phase torus is P T. The distance and the formula transform isometrically.

## Proof

### 1. Remove only the true gauge directions

T is compact and U(n) is complete. There is a shortest geodesic from T to U. A shortest geodesic to a submanifold is orthogonal at its initial endpoint. With the bi-invariant metric, write that geodesic

    gamma(t) = exp(t K) D,
    D in T, K*=-K, diag(K)=0,
    ||K||_F = d(U,T).

The orthogonality condition is exactly diag(K)=0: the tangent space to T consists of imaginary diagonal matrices. This avoids the incorrect assertion of strict curvature along diagonal gauge directions. The conclusion needs existence, not uniqueness, of the nearest point/geodesic.

Kupferman–Shachar, *On strain measures and the geodesic distance to SO_n in the general linear group*, [arXiv:1603.05868](https://arxiv.org/abs/1603.05868), Lemma 3.1, applies to a complete Riemannian manifold and compact submanifold; those hypotheses hold here. The orthogonality also follows directly from first variation of length.

### 2. Exact Hessian, with no invertibility hypothesis

Put f(t)=Re(eta det(A+exp(tK) B exp(-tK))), with A=D_a,B=D_b. At t=0 the sum is diagonal; [K,B] has zero diagonal, so f'(0)=0. Expansion of the determinant gives

    f''(0) = -2 sum_(i<j) delta_ij |K_ij|^2.

To see the coefficient explicitly, write c_i=a_i+b_i. Then

    (ad_K^2 B)_ii = 2 sum_(j!=i) |K_ij|^2 (b_j-b_i),
    (ad_K B)_ij = K_ij (b_j-b_i).

Only one second-derivative diagonal column or a pair of first-derivative off-diagonal columns can contribute to the t^2 coefficient. The contribution for i<j is

    |K_ij|^2 (b_j-b_i)(a_j-a_i) product_(k!=i,j)c_k
       = |K_ij|^2 (z_(ij)-z_id).

This derivation is polynomial and is valid even when any c_i is zero. Since diag(K)=0,

    f''(0) <= -delta ||K||_F^2.

### 3. Uniform third derivative, again without inverse matrices

Let C(t)=A+exp(tK) B exp(-tK), k=||K||_op, beta=||B||_op. For real t, unitarity implies

    ||C(t)||_op <= R,
    ||C^(j)(t)||_op <= (2k)^j beta   (j=1,2,3).

Apply column multilinearity, Hadamard's inequality, and the product rule:

    |(det C)'''| <=
      n R^(n-1) ||C'''||
      + 3 n(n-1) R^(n-2) ||C''|| ||C'||
      + n(n-1)(n-2) R^(n-3) ||C'||^3
    <= 8 k^3 [n beta R^(n-1)
             +3n(n-1) beta^2 R^(n-2)
             +n(n-1)(n-2) beta^3 R^(n-3)]
    <= 8 n^3 R^n ||K||_F^3.

For n=2 the final term is omitted, not interpreted as requiring division by R. The last bound uses beta<=R and the identity

    n+3n(n-1)+n(n-1)(n-2)=n^3.

Consequently |f'''(t)|<=8 |eta| n^3 R^n ||K||_F^3 for every t in [0,1].

### 4. Close the quantitative inequality

Taylor's integral remainder gives, with q=||K||_F,

    f(1) <= h - (delta/2)q^2
                   + (4/3)|eta|n^3 R^n q^3.

If q<=r, the last term is at most (delta/4)q^2. This proves the statement.

## Sharpening by centering and by which spectrum is conjugated

The transformation a_i -> a_i+lambda, b_j -> b_j-lambda leaves C(t), every z_pi, all deltas, and the target invariant. Thus any chosen complex lambda can improve R in the same proof. Moreover

    det(A+exp(tK)Bexp(-tK))
       = det(exp(-tK)Aexp(tK)+B),

so the third-derivative estimate may use the smaller centered norm of A and B. If

    alpha=max|a_i+lambda|, beta=max|b_j-lambda|,
    R_lambda=alpha+beta, m=min(alpha,beta),
    L_lambda=8|eta|[n m R_lambda^(n-1)
             +3n(n-1)m^2 R_lambda^(n-2)
             +n(n-1)(n-2)m^3 R_lambda^(n-3)],

then the stronger sufficient radius is **3 delta/(2 L_lambda)**. Indeed the remainder is L_lambda q^3/6 and should be <=delta q^2/4. All quantities are explicit; no minimizer in lambda is required. This is a quantitative optimization, not a global continuation theorem.

## Exact sample in order four

Take

    a=(0,1,2,3+i), b=(3,2,1,i), eta=1.

The identity product is 81+54i. Exact enumeration of all 24 products verifies h=81. In order (12),(13),(14),(23),(24),(34), the transposition gaps are

    (9,36,90,9,45,18), so delta=9.

Here max|a|=sqrt(10)<4 and max|b|=3, so R<7. Therefore the smaller rational radius

    r0 = 27/(16*64*7^4) = 27/2458624

is certified without floating-point square roots. For d(U,T)<=r0, the support margin is at least (9/4)d(U,T)^2. This is **one support direction**, not full MOC for this pair; other directions require their own analysis.


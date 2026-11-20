# HMSV connection: projected nonic necessity and the missing real lift

**Status:** original theorem statements and hypotheses checked; exact coordinate bridge checked. The global nonic argument below is a deduction from the cited original HMSV divisor theorem, **not** a full symbolic expansion of a degree-nine polynomial. The [independent mathematical audit](hmsv_compatibility_independent_review.md) is **VALID with field/normalization clarifications**, now incorporated. **Nothing here proves positivity, universal Gram completion, or unrestricted MOC4.**

- [Full original-source audit](hmsv_original_source_audit.md)
- [Exact bridge verifier](../../code/research/verify_m8_fourier_bridge.py)
- [Direct primitive-cubic reconstruction](M8_PRODUCT_LINKAGE.md), independently [VALID](m8_product_linkage_independent_review.md)

## 1. The actual imported theorems

Howard–Millson–Snowden–Vakil, *The ring of projective invariants of eight points on the line via representation theory*, [arXiv:0809.1233v1](https://arxiv.org/abs/0809.1233v1), **Theorem1.1**, over Q: the unique nonzero S8-skew cubic, up to scale, has the eight-point invariant variety M8 as its singular locus. More precisely, its fourteen derivatives generate the ideal, so this holds scheme-theoretically for affine cones. Base change to C is legitimate.

The characteristic-three issue following Theorem 1.1 in arXiv:0809.1233v1 is irrelevant over Q,R,C.

HMSV, *The geometry of eight points in projective space: representation theory, Lie theory, dualities*, [arXiv:1103.5255v1](https://arxiv.org/abs/1103.5255v1), **Corollary3.12, Proposition3.13, active Proposition3.19 and its following paragraph**: the complex secant variety is a degree21 divisor on the cubic, cut out there by a septic section; the Hessian determinant vanishes to order2 along that divisor. In particular, for a suitable degree-seven polynomial S7 and a nonzero normalization scalar kappa,

    det H_Phi = kappa S7^2 mod Phi.                 (1)

The cited arXiv:1103.5255v1 results identify the exceptional divisor as precisely the secant divisor. This is a complex algebraic statement, not real conjugate-secant sufficiency or a PSD assertion. The active proof contains editorial slips (`dimension at most3` in a Lefschetz parenthetical and P14 instead of P13); neither auxiliary wording is imported here.


## 2. Exact hypothesis and coordinate match

Take eight labeled vectors

    u_i=(a_i,1), v_j=(-b_j,1).

Then [u_i,v_j]=a_i+b_j. The24 permutation products are bipartite perfect-matching invariants with every label occurring once, exactly HMSV's equal linearization O(1,...,1). They span the14-dimensional degree-one invariant space, as independently reconstructed in M8_PRODUCT_LINKAGE.md. Thus their evaluation vector lies in the affine M8 cone, and multiplying by eta preserves that cone. No division by differences or pair sums is involved.

For a24-score array f, define the Fourier coordinates

    c = sum_pi f_pi,
    A = sum_pi f_pi rho31(pi^(-1)),
    B = sum_pi f_pi rho22(pi^(-1)).

Here rho31 uses e0-e3,e1-e3,e2-e3; rho22 uses q0-q2,q1-q2 for q0=01|23,q1=02|13,q2=03|12. A is3-by-3, B2-by-2. The explicit Fourier cubic is

    Phi_F(c,A,B)=162 det A+72c det B-27T(A,B)+8K(B),

with T and K given as exact integer formulas in verify_m8_fourier_bridge.py. They are reconstructed in that program without importing or executing external source code.

The verifier constructs the full14-by-14 map Kbridge from the earlier selected-product coordinates v to (c,A,B). Exactly,

    det Kbridge = 7247757312 != 0,
    Phi_F(Kbridge v) = -20736 Phi_primitive(v).

It checks this as a polynomial identity, not just at spectra. Combined with the previously audited S8 covariance, this identifies the *actual* unique HMSV cubic rather than an abstract representation of the same dimension. The exact196 entries are saved in the bridge record. Hessian transport is a congruence: with alpha=-20736,

    Kbridge^T H_Phi_F(Kbridge v) Kbridge = alpha H_Phi_primitive(v),
    det H_Phi_F(Kbridge v) = alpha^14 det H_Phi_primitive(v)/(det Kbridge)^2.

This preserves the nonzero scalar in the imported square-modulo-cubic statement; it does not set that scalar to1.

A score shift by t changes only c, by24t. The13 nontrivial Fourier entries therefore describe the same gap quotient as the earlier gamma coordinates. With D=det B,

    Q2(gamma) = -D(gamma)/12,

verified symbolically. This pins the exceptional projection chart in both normalizations.

## 3. Global degree-eighteen equation and degree-nine square root

Write Phi_F=72cD+Phi0(A,B). On D!=0 its only cubic-compatible constant is

    c_* = -Phi0/(72D).

Define

    J(A,B) = D^2 det H_Phi_F(c_*,A,B).              (2)

Although written rationally, (2) is a **polynomial**. Here is the denominator argument, not a claim inferred from one line computation.

Order the Hessian coordinates as c,A(9entries),B(4entries). It has block form

    [[0, 0, v^T],
     [0, M, N  ],
     [v, N^T, Q+cK]],

where v=72 grad D and K=72 Hess D. Its determinant has degree at most3 in c: the c row and column each consume one B position, leaving at most three c-dependent B positions. The coefficient of c^3 is

    -det(M) v^T adj(K)v.

Since D is quadratic with det(Hess D)=1,

    v^T adj(K)v = 2*72^5*D.

The bridge verifier checks this exact polynomial identity. Thus the cubic coefficient is divisible by D. Substituting c_* and multiplying by D^2 clears every denominator, including the potential third-order pole. J is homogeneous of degree18.

The sign and nonvanishing assertions below use the following exact rational witness, retained here solely to fix the scalar normalization and genuine degree. In the ordered selected-product basis of [M8_PRODUCT_LINKAGE.md](M8_PRODUCT_LINKAGE.md), Section 1, set

    gamma=(6483/50,8478/25,1183/10,37937/100,4194/25,
           21901/100,54/25,5203/50,241/100,25383/50,
           2243/5,137/50,46851/100),
    h0=6593106261/2187836725,
    v_*=(h0,h0-gamma1,...,h0-gamma13).

Here h0 is the selected-product height, not the Fourier coordinate c. Let (c_F,A_*,B_*)=Kbridge v_*. Exact substitution in the primitive cubic and its Hessian gives

    Phi_primitive(v_*)=0,
    Q2(gamma)=-87513469/10000,
    D_* = det B_* = -12 Q2(gamma)=262540407/2500,
    det H_Phi_primitive(v_*)=
      -974878318923381057593619954706182435722536181007671529
      /47866295352587256250000000000000000 < 0.

Since D_*!=0, c_F is the unique Fourier cubic height c_*(A_*,B_*). The Hessian transport already proved in Section 2 therefore gives

    J(A_*,B_*) = D_*^2 * (-20736)^14 / 7247757312^2
                * det H_Phi_primitive(v_*) < 0.

This supplies both the sign and the nonzero evaluation needed below; no other conclusion about this witness is required. The selected gaps, height and primitive Hessian determinant are reconstructed by `reconstruct()` in the [retained verifier](../../code/research/verify_m8_product_linkage.py).

Now apply the **global original theorem** (1), not a sampled specialization. On D!=0,

    J = kappa [D S7(c_*,A,B)]^2.

Work first in the ordinary UFD `C[A00,...,A22,B00,...,B11]`, **not** in the cubic coordinate ring. The bracket is a rational function r whose square, up to a nonzero complex constant, is polynomial. For every polynomial irreducible p, `2 val_p(r)=val_p(J)>=0`; the constant contributes no valuation. Thus r is a polynomial. Therefore

    J = kappa N9(A,B)^2,                            (3)

initially with N9 in C[A,B] homogeneous of degree9 and kappa in C*. Since J has rational coefficients and characteristic is zero, every irreducible rational factor has even multiplicity. Renormalizing the root yields N9 in Q[A,B] and kappa in Q*. In this real normalization **kappa<0**: the exact rational sign witness specified above has J<0 and hence N9!=0 there. Consequently J<=0 on all real(A,B), a scalar-square sign consequence of the imported theorem, **not** positivity of the MOC support gap or of a Gram block. The same sign witness has D=262540407/2500!=0 and nonsingular Hessian at its unique cubic height, so J is not identically zero. Thus the degree is genuinely18 and its square root genuinely9. This argument does **not** claim to have expanded N9 or separately proved its irreducibility.

Every actual profile satisfies J=0 on D!=0. It also does so at D=0: J composed with the real spectral parameters is polynomial and vanishes on the dense nonempty D!=0 chart, hence identically. The bridge verifier reconstructs this witness directly from a=(-1-2i,2+2i,-1+2i,0), b=(-2-i,-2+i,1,2+2i), eta=1+i and checks D=-86400. This density is in the unrestricted actual parameter space, not a claim about each fixed contact stratum. Equivalently, continuity of these polynomial identities extends the necessary equation through degeneracies without requiring the supporting permutation to remain fixed during the density argument.

**Exceptional-chart caveat:** at D=0, reconstructing an actual score still requires Phi0=0 and a real height/lift. The cleared equation J=0 is only a necessary projected condition, not a license to divide by D or certify a lift there.


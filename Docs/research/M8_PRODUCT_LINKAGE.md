# The actual product-profile cubic and a global Hessian obstruction

**Status:** exact, independently reconstructed polynomial linkage; [independent mathematical audit](m8_product_linkage_independent_review.md) **VALID**, and [original HMSV-source audit](hmsv_original_source_audit.md) completed. All mathematical-scope warnings remain. **No positivity theorem, universal SOS completion, or unrestricted MOC4 proof is claimed.** This gives a concrete coupled constraint on the entire spectral cost profile, beyond the isolated 2-by-2 rank-one block discussed in [ODD_PROFILE_LINKAGE.md](ODD_PROFILE_LINKAGE.md).

The reconstruction does not import the existing compound/Cayley coefficient model. [Verifier](../../code/research/verify_m8_product_linkage.py). Default execution is read-only; only --report writes a requested record. This is exact rational/polynomial verification, not a Lean formalization.

## 1. Fourteen invariant coordinates and thirteen gap coordinates

Put x=(a0,a1,a2,a3,-b0,-b1,-b2,-b3), and

    f_pi(x) = product_(i=0..3) (x_i - x_(4+pi(i)))
            = product_i (a_i+b_pi(i)).

Their coefficient matrix has70 rows indexed by four-element subsets of eight variables and24 columns indexed by permutations. Its rank is **14**. The following lexicographically selected permutations form a basis, in this exact order:

    0123, 0132, 0213, 0231, 0312, 1023, 1032,
    1203, 1230, 1302, 2013, 2031, 2301, 3012.

Write v=(f_basis0,...,f_basis13). Every f_pi is an integer linear combination of these14 coordinates. Evaluating at a=(0,0,0,0), b=(1,1,1,1) shows that each combination's coefficients sum to1. Therefore, with

    r = Re(eta v),   c=r0,   gamma_j=r0-r_j (j=1,...,13),

every original permutation gap is a fixed linear function of gamma alone. The record contains the full24-by-13 matrix L and verifies its rank13. In particular, these are **coordinates on the complete gap space**, not a partial collection of comparisons.

Multiplying pairs of basis polynomials gives a1107-by-105 coefficient matrix of rank91. Its kernel consists of14 independent quadratic relations. Requiring a cubic's fourteen derivatives to lie in that kernel is a linear integrability problem; its1081-by-196 matrix has a one-dimensional kernel. The resulting derivatives span all14 quadratic relations.

The primitive integer cubic Phi has49 monomials. For the basis just specified, its exact definition is:

```text
Phi = v0^2*v6 - v0*v1*v5 - v0*v1*v6 + v0*v10*v6 - v0*v12*v6
 - v0*v13*v6 + v0*v13*v8 - 2*v0*v2*v6 + v0*v3*v6 + v0*v4*v6
 - v0*v5*v6 + v0*v6^2 + v0*v6*v7 - v0*v6*v8
 + v1^2*v5 - v1*v10*v5 + v1*v10*v7 - v1*v10*v8 + v1*v12*v5
 + v1*v13*v5 - v1*v13*v7 + v1*v2*v5 + v1*v2*v6 - v1*v3*v5
 - v1*v4*v5 + v1*v5^2 - v1*v5*v6 - v1*v5*v7 + v1*v5*v8
 - v10*v2*v6 + v10*v3*v6 - v10*v3*v9 + v10*v4*v8
 + v11*v2*v9 - v11*v4*v7 + v13*v2*v6 - v13*v2*v8
 - v13*v3*v5 + v13*v3*v7 + v2^2*v6 - v2*v3*v6 - v2*v4*v6
 + v2*v5*v6 - v2*v6^2 - v2*v6*v7 + v2*v6*v8
 + v3*v4*v5 - v4*v5*v8 + v4*v6*v7.
```

The verifier checks every coefficient of

    gradient Phi(v(x)) = 0

in all eight indeterminates. It also constructs the14-by-14 evaluation-coordinate matrices for all seven adjacent transpositions of the eight points and checks Phi(A_tau v)=-Phi(v). This is the precise skew-cubic covariance, not a guess from the number14. The complete matrices and quadratic relations are retained in the exact record.

## 2. Necessary equations for every actual real support profile

Let w=eta v(x)=r+i s. Homogeneity gives gradient Phi(w)=0. Because Phi has real coefficients and is cubic, real and imaginary parts give

    gradient Phi(r) = gradient Phi(s),
    Hess Phi(r) s = 0.

Furthermore, cubic polarization and Euler's identity give

    3 Phi(r) = r dot gradient Phi(r)
             = r dot gradient Phi(s)
             = (1/2) s^T Hess Phi(r) s = 0.

Thus every actual real product profile satisfies

    Phi(r)=0,        det Hess Phi(r)=0.                 (1)

For the second identity, if s is nonzero it is an explicit Hessian-kernel vector. If s=0 and r is nonzero, gradient Phi(r)=0 and Hess Phi(r)r=2 gradient Phi(r)=0. If r=s=0 the Hessian itself is zero. This proves (1) with **no division, distinctness assumption, or exclusion of eta=0 or zero pair sums**.

The argument establishes necessary conditions only. A general real point on the cubic with singular Hessian is not automatically an actual real conjugate secant. Nor has it been shown that these equations imply the desired Gram inequalities.

## 3. Projecting out the additive constant

The constant vector 1 is a singular point of Phi; its Hessian has rank4. Direct substitution yields the exact identity

    Phi(c*1-(0,gamma1,...,gamma13))
        = c Q2(gamma) + C3(gamma),                    (2)

where Q2 is homogeneous quadratic with39 terms and C3 homogeneous cubic with35 terms. The record gives both expressions explicitly. Hence, **only on Q2!=0**, the sole cubic-compatible constant is

    c = -C3(gamma)/Q2(gamma).

Substitution in (1) gives a necessary rational Hessian equation purely in the13 gap coordinates; it can be cleared of denominators on this chart. On Q2=0 one instead requires C3=0 and retains the constant in the Hessian condition. No division by Q2 is made in a universal claim.

This direct-reconstruction document does **not** claim a symbolic expansion of the stronger degree-nine projected equation. The separate [HMSV compatibility argument](HMSV_COMPATIBILITY.md) now gives a global theorem-based square-root deduction, an exact Fourier-coordinate bridge, and explicit exceptional-chart/real-lift caveats.


## 5. Exact generic dimension, not dimension-as-positivity

Consider the polynomial map from nine complex parameters (a0..a3,b0..b3,eta) to the13 complex selected gaps eta(f_id-f_pi). Its Jacobian has the following three complex kernel generators, written as changes in (a,b,eta):

- translation: (1,-1,0);
- dilation: (a,b,-4eta);
- quadratic projective generator: (a^2,-b^2,-eta(sum a-sum b)).

The verifier expands these identities in **all eight independent spectral symbols and eta**, not just one point. The generators are generically independent, so the generic complex rank is at most6. A concrete Gaussian-integer point has exact complex rank6. The corresponding real gap Jacobian has exact rank12:

    a=(-1-2i,2+2i,-1+2i,0),
    b=(-2-i,-2+i,1,2+2i), eta=1+i.

Thus the actual real gap image has generic dimension **12 inside13**, despite having full13-dimensional linear span. For the stated basis, its exact local normal at this point is

    (83314,28184,-43890,-95469,28398,-161298,-58152,
     46002,139605,-28704,43200,-20040,20064).

That normal is local and is **not** asserted to define a global supporting hyperplane. At this example the Hessian has rank12, but no universal rank12 assertion is inferred from one example. The finite exact rank witnesses prove the generic-rank statements, not a finite test of MOC positivity.

## 6. External theorem connection

The [original-source audit](hmsv_original_source_audit.md) checks HMSV arXiv:0809.1233v1 Theorem1.1 and arXiv:1103.5255v1 active Proposition3.19. [HMSV_COMPATIBILITY.md](HMSV_COMPATIBILITY.md) separates that theorem connection from the elementary identities proved here. The exact Fourier bridge pins the cubic scale to -20736 and the chart identity Q2=-det(B_Fourier)/12. The identities (1) and reconstruction do not need these deeper theorems.

The original theorem identifies the singular locus with the invariant image, but supplies **no PSD inequality**. Neither rank counts, a cubic equation, nor a singular Hessian alone proves simultaneous feasibility of the shared-variable blocks in [PARITY_REDUCED_COMPLETION.md](PARITY_REDUCED_COMPLETION.md) or G_even>=abs(G_odd).

```sh
python -B code/research/verify_m8_product_linkage.py
```

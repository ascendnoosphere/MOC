# Odd-adaptive allocations: a complete contact fiber and a rational sufficient criterion

**Status:** exact constructive partial results from the full-allocation oracle. Main-agent reproduction PASS; [independent mathematical review](actual_fiber_allocation_independent_review.md) **VALID**, including the full-matrix certificates and family-specific dual argument. **Universal feasibility of this selector family and unrestricted complex MOC4 remain open.**

- [Complete oracle report](adaptive_allocation_fiber_lemmas.md)
- [Read-only reproduction adapter](../../code/research/verify_actual_fiber_allocation.py)

The adapter reruns the exact polygon, quadratic-criterion and seed-application programs without an optimizer. This reproduces the supplied certificates, **not** a second independent mathematical derivation. The exact arithmetic is SymPy Rational/LDL, not proof-assistant formalization.

## 1. The full legal allocation family

Order edges as12,13,14,23,24,34, and let w_e=Delta_e/4. Denote the six special weights by alpha to distinguish them from the complex spectrum a. Let r be the three original residual Laplacian coefficients. Then

```text
P(z) = { alpha : 0 <= alpha <= w, r+C alpha >= 0 },
C = [[-2,-2, 2, 2,-2,-2],
     [-2, 2,-2,-2, 2,-2],
     [ 2,-2,-2,-2,-2, 2]],
u = sum_e (2 alpha_e-w_e) ell_e.
```

This corrects the potentially misleading sign shorthand in the original dispatch. The residual changes are the negatives of the special atoms' removed contributions.

The canonical full19-dimensional Gram uses this u and the **same eight cubic gauges** in both parity blocks. No independent9/10-block completion is substituted. Feasibility in this family is sufficient, not known necessary, for the original support inequality.

## 2. A general interpolation proposition that stays on actual spectra

Fix eta, the contact permutation, and all but one complex eigenvalue. The contact height, all24 comparison gaps and every raw compound Gram coefficient are real-affine in that remaining eigenvalue.

Let Q be a finite convex polygon in this actual spectral fiber. If each vertex has the same maximizing permutation and has a legal allocation with a full PSD Gram, then every point of Q has such a completion. Given nonnegative barycentric weights lambda_v, use

    alpha = sum_v lambda_v alpha_v,
    k     = sum_v lambda_v k_v.

The capacity and residual inequalities interpolate. The full Gram is exactly the same convex combination of vertex Grams, so is PSD. This is legitimate because of affineness along this **actual** fiber, not because arbitrary convex combinations of spectral profiles are actual.

For products of finite spectral polytopes, the same argument works by checking all corners and using product barycentric weights; coefficients are separately affine in each eigenvalue. The common-contact hypothesis at every corner is indispensable. This proposition does not reduce all possible spectra to the particular polygon below.

## 3. The entire identity-contact hexagon for seven fixed eigenvalues

Fix

    a=(-4-4i,-2,1/100+x+i(-3+y),-1),
    b=(3i,4-i,-4+2i,1-3i), eta=1.

Identity maximizes the original24 products **exactly** on the bounded hexagon

```text
18   - 700x - 475y >= 0,
5203 +5300x -1350y >= 0,
241  -5900x -8200y >= 0,
49   - 100x + 450y >= 0,
137  -1300x +2450y >= 0,
87   -6300x +2450y >= 0.
```

The contact height is h=153/50+6x-27y. Its vertices, in lexicographic rather than cyclic order, are

```text
(-107/100,       -26/75),
(-169357/205700, 1279/2057),
(-73/425,        -5/34),
(-1/100,         -3/49),
(53/4700,         1/47),
(3417/188300,     3/269).
```

[Six exact certificates](../../data/certificates/research/actual_fiber_allocation/polygon_exact_certificates.json) give an allocation and eight raw cubic gauges at each vertex. Each resulting full Gram has rank17, two exact kernel columns, and a positive17-dimensional principal LDL factorization. The deleted2-by-2 kernel submatrix is invertible, making the principal positivity certificate a certificate for the entire19-dimensional matrix.

**Facet normalization:** the preserved redundancy multipliers act on the six **raw original gaps**, not directly on the displayed primitive integer expressions. In their listed order the raw-gap scales are `(3/25,1/50,1/100,3/50,1/50,1/50)`. The main adapter now recomputes these scales, compares all400 feature products with direct polynomial multiplication and computes/asserts the838-position count rather than trusting a literal coverage field. It also checks the independent boundedness certificate `(180/277)n1+(29/277)n2+n4=0`, whose coefficients are positive and whose first two normals span the plane.

The polygon verification additionally checks:

- all24 original comparisons, with exact redundancy certificates from the six displayed facets;
- all feasible pairwise intersections, absence of recession rays, and both endpoints of every edge;
- all six distinct vertex certificates, capacities and residual inequalities;
- all838 polynomial coefficient positions;
- the triangle and actual Segre/discriminant linkage symbolically on the entire complex fiber.

Barycentric interpolation therefore gives an allocation and cubic completion **throughout the whole maximal identity-contact region**, including its boundary. This is a continuum of actual spectral data. It is only the stated direction eta=1, not every direction for each pair, and does not vary the other seven eigenvalues freely.

At x=y=0 an especially short strict certificate is

    alpha=(419/10,3/10,223/10,461/10,1/5,1/100),
    k=(371,118,-75,-414,18,176,-30,66).

The residual coefficients are (5/8,10149/200,23/200); both parity blocks are positive definite. [Exact seed](../../data/certificates/research/actual_fiber_allocation/seed_certificate.json).

## 4. A solver-free rational test responding to all four odd coordinates

Use the actual13-coordinate profile

    z=(w12,w13,w14,w23,w24,w34,d1,d2,d3,J012,J013,J023,J123).

The rational arrays in [criterion.json](../../data/certificates/research/actual_fiber_allocation/criterion.json) express a representative Gram as

    X(z,x) = sum_(j=1..13) z_j F_j + sum_(i=1..14) x_i V_i.

The first six x_i are special allocations, the remaining eight cubic gauges. The representative differs from the raw actual cubic block only by those permitted gauges, verified on every one of the70 compound directions and all838 coefficient positions.

Let X_*>0,z_*,x_* be the exact strict seed and W=X_*^(-1). Define

    <P,Q>_W = tr(W P W Q),
    H_ij = <V_i,V_j>_W, N_ij = <V_i,F_j>_W,
    T = -H^(-1)N,
    E_j = F_j + sum_i T_ij V_i,
    Cquad_ij = <E_i,E_j>_W.

The14 directions V_i are independent, so H>0. For an actual identity-supported input with g=sum w>0, put

    rho = g/g_*, delta = z-rho z_*, x = rho x_*+T delta.

The following **sufficient**, not necessary, criterion is fully rational:

    first_six(x) in P(z),       delta^T Cquad delta <= rho^2.

Indeed X=rho X_*+Delta and

    || X_*^(-1/2) Delta X_*^(-1/2) ||_F^2
        = delta^T Cquad delta <= rho^2,

so the least eigenvalue after congruence is nonnegative. This bounds the **whole coupled matrix**, not just its diagonal blocks. T minimizes this relative Frobenius residual over all14 parameters; all24 entries coupling six allocations to four odd coordinates are nonzero. The seed is strict, giving a nonempty open sufficient neighborhood even with all spectra varying.

[apply_criterion.py](../../code/research/actual_fiber_allocation/apply_criterion.py) is the preserved implementation; its scratch paths are handled by the reproduction adapter. **Input contract:** the pristine implementation has the following required preconditions (it is not a hardened input validator): trusted, exact numerical expressions, length-four spectra, and a finite exact eta for which identity is already a maximizing permutation. It is not a safe parser for hostile strings, does not accept free symbolic parameters or numerical tolerances as proof, and unsupported input triggers its support assertion rather than a certification. Under that precondition, failure of the sufficient test returns INCONCLUSIVE, never an infeasibility certificate. This is not merely a verbal caveat: swapping a and b at the seed makes the scalar test fail exactly, while reflection supplies another exact positive Gram with the same allocation. The test's score there is approximately167748.98. This limitation is verified exactly.


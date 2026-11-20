# Joint certificates: exact rank reduction and real-lift moment tests

**Status:** exact reductions, an actual-spectral example, and an elementary rank-reduction lemma. **Not a proof or refutation of unrestricted MOC4.** The [independent mathematical audit](joint_certificate_rank_independent_review.md) is **VALID**, including the complete duality/attainment proof, rank/support bounds and constructive rank-two-map lemma. The main agent also reconstructed the finite artifacts exactly. Neither kind of validation proves universal feasibility or MOC.

This note connects the [actual-fiber allocation problem](ACTUAL_FIBER_ALLOCATION.md), [HMSV real-form linkage](HMSV_COMPATIBILITY.md), a minimax theorem, and a concrete PSD-face reduction. It keeps the allocation and all quadratic factors coupled. It does not replace a shared allocation by separately optimal rank-one allocations.

## 1. The primal and the complete simultaneous dual

Use the already coefficient-validated canonical 19-coordinate Gram pencil

    M(z,alpha,h) = F(z) + sum_e alpha_e A_e + sum_j h_j G_j,

where z has thirteen real profile coordinates, alpha has six edge-allocation coordinates, and h has eight surviving cubic gauges. See [parity reduction](PARITY_REDUCED_COMPLETION.md) for the matrices and their target-polynomial meaning. Write w for the six transposition capacities and r for the three unallocated boundary reserves. The allowed allocation polytope is

    P(z) = {alpha : 0 <= alpha <= w, r+C alpha >= 0},

    C = [[-2,-2, 2, 2,-2,-2],
         [-2, 2,-2,-2, 2,-2],
         [ 2,-2,-2,-2,-2, 2]].

For supported actual spectral data the earlier even construction supplies a point in P(z). Thus P(z) is nonempty and compact. This fact is an imported, proved part of the earlier reduction, not a consequence of a numerical feasibility run.

A strictly negative simultaneous dual certificate is

    Y >= 0 (real symmetric 19 by 19),
    mu,nu >= 0 (six coordinates each), xi >= 0 (three),
    <Y,G_j> = 0,                            j=1,...,8,
    b_e := <Y,A_e> = mu_e-nu_e-(C^T xi)_e,  e=1,...,6,
    L_z := <Y,F(z)> + mu.w + xi.r < 0.

Inner products of real symmetric matrices mean trace(XY). For any allowed alpha, the stationarity equation gives

    L_z - <Y,F(z)+sum_e alpha_e A_e>
        = mu.(w-alpha)+nu.alpha+xi.(r+C alpha) >= 0.

Consequently such a certificate rules out **every** allocation and cubic gauge in this restricted atom family. It would not, by itself, disprove an unrestricted-u SOS completion, still less MOC.

### No weak-infeasibility shortcut is needed

The eight G_j are independent and traceless. Both statements are checked from the exact canonical arrays by the verifier below. Hence there is a constant c>0 such that

    lambda_min(sum_j h_j G_j) <= -c ||h||

for every h: restrict first to the unit sphere, use injectivity and the fact that a nonzero traceless symmetric matrix has a negative eigenvalue, and then use compactness. Since alpha ranges over a compact polytope,

    v(z) = max_{alpha in P(z), h in R^8} lambda_min(M(z,alpha,h))

is finite and attained. The pencil is PSD for some allowed parameters exactly when v(z)>=0. In particular, failure gives v(z)<0, not an unattained zero limit.

For completeness, let D={Y>=0:trace Y=1}. Sion's minimax theorem applies to the continuous function, linear in Y and affine in (alpha,h)

    (Y,(alpha,h)) -> <Y,M(z,alpha,h)>

on compact convex D and convex P(z) x R^8. Only one of these sets needs to be compact. It gives

    v(z) = min_{Y in D, <Y,G_j>=0}
                [ <Y,F(z)> + max_{alpha in P(z)} b.alpha ].

The restricted set of Y is nonempty, since I/19 annihilates the traceless gauges. Finite linear-programming duality on the nonempty bounded P(z) gives

    max_{alpha in P(z)} b.alpha
      = min {mu.w+xi.r : mu,nu,xi>=0,
                              b=mu-nu-C^T xi}.

Thus failure of the restricted PSD family does produce a negative joint certificate. No strict primal PSD assumption or genericity is being smuggled into this argument.

**Minimax source.** Maurice Sion, *On general minimax theorems*, Pacific J. Math. 8(1) (1958), 171–176, DOI [10.2140/pjm.1958.8.171](https://doi.org/10.2140/pjm.1958.8.171). The one-compact-set corollary following Theorem3.4 on printed page174 is sufficient; the function here is affine in each variable and continuous, and the density-matrix side is compact.

## 2. A small negative certificate exists if any does

### 2.1 One PSD block: rank at most five

The certificate constraints are homogeneous. Normalize a nonzero certificate by

    trace Y + sum(mu)+sum(nu)+sum(xi) = 1.

The normalized feasible set is a compact spectrahedron with orthant factors. If it contains a point with L_z<0, minimize L_z and choose an extreme point of the minimizing face. There are at most fifteen affine equalities: eight gauge equations, six allocation equations, and the normalization.

If rY=rank Y and s is the number of strictly positive scalar coordinates among mu,nu,xi, the smallest face of the product cone through that point has dimension

    rY(rY+1)/2 + s.

If this dimension exceeded fifteen, its linear span would contain a nonzero direction annihilated by all fifteen equations. A sufficiently small perturbation in either sign would stay in the same cone face and contradict extremality. Therefore

    rY(rY+1)/2+s <= 15,

and in particular **rank Y<=5**.

This is the nongeneric PSD-face bound. Pataki's upper extreme-rank inequality is reproduced with a complete face-dimension proof in Chua–Plaumann–Sinn–Vinzant, *Gram spectrahedra*, [arXiv:1608.00234v3](https://arxiv.org/abs/1608.00234v3), Proposition 3.1. The additional lower bound requires a generic affine space and is **not used**; the product-cone argument above is elementary.

### 2.2 Parity blocks: another, alternative bound

The validated conjugation parity splits the nineteen coordinates into blocks of sizes9 and10. Every A_e, G_j and F(z) is invariant under that parity. Replacing Y by its parity average preserves PSD, all certificate equations and L_z. One can then choose an extreme negative certificate in this block-diagonal feasible cone.

If the two block ranks are r+ and r-, the face argument becomes

    r+(r++1)/2 + r-(r-+1)/2 + s <= 15.

This implies r++r-<=6. It is an **alternative existence guarantee** to the rank-five single-block certificate. We have not proved there is one certificate enjoying both rank guarantees simultaneously.

For a rank-r real PSD block of size n, factors modulo orthogonal right multiplication have nr-r(r-1)/2 essential coordinates. Enumerating the allowed pairs yields maximum

    9r+ + 10r- - r+(r+-1)/2 - r-(r--1)/2 = 51.

This is a finite low-rank search bound, not a universal nonnegativity conclusion.

### 2.3 Scalar supports: 3,824 possibilities, not 2^15

The allocation equations have scalar column matrix

    S = [ I_6 | -I_6 | -C^T ],

of rank6. For a negative extreme certificate its positive scalar columns are independent, so s<=6. Here is the detail that prevents a normalization mistake.

First Y cannot be zero in a negative certificate. For Y=0, use any alpha in the nonempty P(z) in the identity of Section1 to obtain L_z>=0. If the active scalar columns were dependent, perturb just the active scalars by a nonzero vector v in their kernel, in either sign. These perturbations preserve the homogeneous equations and remain nonnegative for small changes. Rescale each perturbed point to satisfy the normalization. Because Y is nonzero, the perturbation is not merely a scaling of the entire certificate; the two rescaled points are distinct, and the original point is their strict convex combination (with weights adjusted by their pre-normalization sums). This contradicts extremality. The same argument applies in either PSD cone representation.

The exact independent-support counts by size0 through6 are

    1, 15, 99, 377, 900, 1344, 1088,

whose sum is **3,824**. The size-zero support is included. These counts are recomputed with exact rational elimination, not inferred from a random sample.

## 3. Actual profiles and all fourteen Fourier coordinates

Let p run over S4 and put

    v_p = eta product_i(a_i+b_{p(i)}),
    w_p = Re v_p.

Write f=(c,A,B) for its fourteen real Fourier coordinates, with A3by3, B2by2, the same real irreducibles and inverse-permutation convention as `verify_m8_fourier_bridge.py`. Fourier inversion is

    w_p = c/24 + trace(A rho31(p))/8 + trace(B rho22(p))/12.

The exact 24by14 map E, the all-gap map D=1 E_identity-E, the 13by14 canonical profile map Z, and the reserve map R are exported in `joint_certificate_rank/exact_bridge.json`. Important checks are

- Fourier inversion holds on **all fourteen coordinate directions**;
- rank Z=13 and its constant column is zero;
- the constant Fourier direction contributes zero to the Gram pencil;
- all fourteen coefficient matrices for F(Zf) match the independent canonical construction;
- for the original exact Gaussian-rational seed, the profile computed from the original24 products equals Zf, and all24 identity-contact gaps are nonnegative.

This exact bridge lets the dual objective be written as an explicit linear function of f, while the equations defining the dual cone do not depend on f. It does **not** permit f to be replaced by an arbitrary point of the cubic, its Hessian locus, or a complex secant variety. The real-form conditions below still matter.

## 4. Real critical-point lifts as a moment problem

Let Phi be the completely reconstructed real homogeneous Fourier cubic, and H_f its Hessian at a real vector f. If w=f+i y is an actual complex product vector, then grad Phi(w)=0. Quadratic polarization gives exactly

    grad Phi(f+i y) = grad Phi(f)-grad Phi(y)+i H_f y.

Thus an actual imaginary part must satisfy

    H_f y=0,             grad Phi(y)=grad Phi(f).

Conversely these two equations are precisely the real and imaginary parts of the critical-point equations. In this statement a “lift” means a lift to that complex critical locus; identifying all affine/boundary matching coordinates with finite spectral charts is a separate matter. We do not use such an identification to assert a new positivity theorem.

Take a real basis K for ker H_f, with k columns, and y=K u. Define the linear moment map

    B_f : Sym_k -> R^14,
    (B_f(M))_j = trace(K^T H_{e_j} K M)/2.

Then B_f(uu^T)=grad Phi(Ku). A real lift exists exactly when

    M>=0, rank M<=1, B_f(M)=grad Phi(f)

has a solution. The zero matrix is allowed. Merely dropping the rank condition is in general a relaxation.

### 4.1 A general exactness lemma with a constructive proof

**Lemma.** For any real linear map B:Sym_k->R^m of rank at most2, if B(M)=d has a PSD solution, it has a PSD solution of rank at most1.

**Proof.** Suppose a feasible M has rank r>=2 and write M=UU^T with U of full column rank r. The map

    W -> B(UWU^T),       W in Sym_r,

has rank at most2, while dim Sym_r=r(r+1)/2>=3. Choose a nonzero real symmetric W in its kernel. The matrices

    U(I+tW)U^T

remain moment-feasible. If W has a positive eigenvalue, take t=-1/lambda_max(W); otherwise take t=-1/lambda_min(W)>0. In either case I+tW is PSD and singular. The resulting feasible matrix has lower rank. Repeat until the rank is0 or1. If d is nonzero, rank0 is impossible. This terminates after at most max(k-1,0) rank reductions. No compactness of the original PSD slice or genericity is required. QED.

This supplies an actual finite construction, not just an existence slogan. For real algebraic input each step can be performed with exact real algebraic arithmetic. In particular, whenever the computed restriction map B_f has rank at most2, its PSD moment relaxation is **exact for the critical-point lift question**, for any kernel dimension.

The rank threshold matters. For B(M)=(M00,M01,M11) on Sym2, the target (1,0,1) has the unique PSD solution I2. It has rank2 and cannot equal uu^T. Here rank B=3. One cannot extend the lemma to arbitrary restriction maps by citing the PSD rank bound.

**Subsequent structural result:** [CORANK_TWO_LIFT_EXACTNESS.md](CORANK_TWO_LIFT_EXACTNESS.md) now proves rank B_f<=2 throughout the complex secant cone's Hessian-rank12 chart, using the original HMSV contraction and derivatives of all13by13minors. Its [separate independent original-source audit](corank_two_lift_exactness_independent_review.md) is **VALID**, including singular points, and all presentation fixes are implemented. Thus the PSD relaxation is exact throughout that chart, including rank-one/zero restriction-map degeneracies. Higher Hessian-corank strata remain unclosed. The two examples alone were never evidence of universality.


## 5. Pure-parity rank-one gauges: a useful but limited computation

On either pure-parity 19-coordinate block, write a rank-one vector as (T,C,d), using the formal Hermitian T and C. The exact eight restricted gauge quadratics span the same eight-dimensional polynomial space as the nine entries of TC=0 (one trace dependence). This is checked by equality of coefficient-row spaces over the rationals for both parity blocks.

This characterizes **rank-one vectors that individually annihilate every gauge**. It does not prove that a general PSD matrix satisfying eight gauge trace equations can be decomposed into rank-one matrices that each annihilate all eight gauges. Cancellations between factors are permitted. Nor can the allocation maximizing the full objective be chosen separately for different factors.


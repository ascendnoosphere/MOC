# Archive extraction: a low-displacement-rank route

## Result and remaining target

Codimension-one normal compression has a rank-one rational-functional defect for arbitrary finite complex spectra. Its defect plane varies with the rational-function pole, so a proof must retain the full pole-dependent family.

For every n, finite a,b in C^n, U in U(n), and eta in C, the target remains

    Re(eta det(D_a+U D_b U*)) <= max_pi Re(eta product_i(a_i+b_pi(i))).

The target allows arbitrary finite complex spectra and support phase, including collisions. The identities below and the exact dimension-five obstruction establish the compression structure; the directional compensation inequality needed for unrestricted MOC remains open.

## 1. Exact compression and descent lemmas

### Signed descent, including all middle minors

The multiplication identity

    (D_a+U D_b U*)U = ((a_i+b_j)u_ij)

proves

    d = sum_pi c_pi z_pi,
    c_pi = sgn(pi) product_i u_i,pi(i) / det U.

Comparing coefficients of a_(I-complement)b_J gives

    sum_{pi(I)=J} c_pi = |det U[I,J]|^2.

Thus p_pi=Re c_pi gives a real affine law reproducing every squared minor simultaneously. One must descend the coefficients first: applying Re directly to a complex spectral product would be invalid. The positivity requirement p_pi>=0 fails. The number-system notes prove this identity over rings with an involution and a linear retraction, without dividing by two. Characteristic two removes determinant/permanent interference but supplies no ordered-real positivity theorem.

### An actual two-unitary dimension-lowering trace

The standalone volume, N061, PDF pages 236–242, proves the following recursion. Write

    U = [[alpha,r],[c,D]],  tau=1+|alpha|^2,
    V_z = D + z c r/(1-z alpha),  |z|=1.

For |alpha|<1, V_z is unitary. For any equal-cardinality I,J among the remaining labels, put d_IJ=det D[I,J] and e_IJ=det U[{0} union I,{0} union J], using the deleted label first. The bordered determinant identity gives

    det V_z[I,J] = (d_IJ-z e_IJ)/(1-z alpha).

Consequently

    Tr_0 R(U)/tau
      = |1-alpha|^2/(2 tau) R(V_1)
        + |1+alpha|^2/(2 tau) R(V_-1),

where R(U)[I,J]=|det U[I,J]|^2. If |alpha|=1, c=r=0 and deletion directly gives R(D). This is an exact positive recursion in every dimension.

It is ordinary partial trace. Rank-one postselection has a different output: already Tr_2[(I tensor K)Swap]=K. A rank-one K cannot be normalized into the one-site Grace class, whose normalized element is I. The trace theorem therefore does not justify conditioning a product spinor and applying smaller-dimensional MOC.

### Normal-compression defect, with phase-dependent repair cost

Let gamma_1,...,gamma_n be any finite complex numbers, v a unit vector, and E the compression of D_gamma to v-perp. Diagonal phases commuting with D_gamma make v real, so a real orthonormal frame for v-perp gives

    D_gamma = [[z,u^T],[u,E]],  u=a+i b, E=X+iY,

in the new basis. Both X,Y are real symmetric. Normality gives

    [X,Y] = b a^T-a b^T.                                      (1)

Its rank is at most two in EVERY dimension. With p_i=v_i^2 and C the ordinary real covariance matrix of the planar points (Re gamma_i,Im gamma_i),

    ||[X,Y]||_F^2 = 2 det C
      = 2 sum_{i<j<k} p_i p_j p_k area(i,j,k)^2.               (2)

Here area is the determinant of the two edge vectors, twice the usual signed triangle area. Proof: a,b are the projections of D_Re(gamma)v and D_Im(gamma)v, so their 2x2 Gram matrix is C. The squared norm of their skew outer product is 2 det C. Cauchy–Binet after centering proves the triangle expansion.

For every pole s for which the indicated inverses exist, block inversion gives

    P(D_gamma-sI)^(-1)P - (E-sI)^(-1) = k_s k_s^T / delta_s,
    k_s=(E-sI)^(-1)u,
    delta_s=z-s-u^T(E-sI)^(-1)u.                              (3)

Thus each resolvent compression defect has complex rank at most one, and its directional real part has real rank at most two. The identity extends as an identity of rational matrix functions; no assertion at an undefined pole is required. A Möbius function is an affine combination of a constant and one resolvent, so it has the same rank-one defect. A sum of m simple poles has defect rank at most m, with repeated poles obtained by differentiation.

For quadratic functional calculus the direction is shared:

    P D_gamma^2 P-E^2 = u u^T.                               (4)

For any kappa in C, the only possibly nonzero eigenvalues of Re(kappa u u^T) are

    lambda_± = (T ± sqrt(T^2+2|kappa|^2 ||[X,Y]||_F^2))/2,
    T=Re(kappa u^T u).                                       (5)

Indeed the trace is T and the product of the two eigenvalues is -|kappa|^2 det C. Formula (5), including zero-rank limits, gives the exact least trace of a PSD additive repair as -lambda_-. It retains the support phase. Replacing kappa by |kappa| too early discards information that the permutation support budget may need.

N095 in the volume proves the dimension-four reciprocal-pencil identities and its normal-completion analysis. Equations (1)–(4) extend that calculation directly to all n; (5) makes the phase-dependent quadratic repair cost explicit.

## 2. Exact obstruction to a fixed defect plane

Take h=(1,2,3,4,5)^T, Q=I-2hh^T/55, and

    gamma=(0,1,i,2+i,-1+2i).

Q is rational orthogonal. In Q^T D_gamma Q, delete its first coordinate and form E,u as above. The checker proves exactly:

* [Re E,Im E] has rank two and squared Frobenius norm 40849568/1107225625;
* each resolvent defect at poles 3,4,5,6 has rank one;
* the four vectors (E-sI)^(-1)u at those poles span ALL four complex dimensions.

Therefore a rank-two normality commutator does not imply a common two-dimensional correction space, even for an actual finite normal completion. A route based on one fixed rank-two scalar compression would fail at this bridge. The family of correction vectors is a Krylov/resolvent family, not one fixed plane.

## 3. Directional compensation with the coherent rational defect

The proposed route is a support-dependent induction through normal compressions, using (3) and the Loewner divided-difference kernel rather than replacing a compression by its eigenvalues. For f(x)=(ax+b)/(cx+d),

    (f(x)-f(y))/(x-y) = (ad-bc)/((cx+d)(cy+d)).                (6)

Its rank-one separated structure is the same rank-one structure as (3). This permits exact bookkeeping of a pole's coherent correction without increasing the determinant degree or requiring spectra to lie on a circle. General rational interpolation introduces several pole vectors, whose cross terms must remain coupled.

The next proof obligation is a directional compensation inequality: at a support maximum, the permutation slacks must pay for the negative parts of the SAME coherent correction matrix, including cross-pole terms. Formula (5) solves the one-quadratic-correction cost exactly. Separate polewise norms are only sufficient bounds and can exceed the true permutation budget; N095 already gives an exact example where independent maxima after an optimal shared repair overspend that budget. Thus the intended inequality must optimize the correction and the matching allocation jointly.

There is a concrete way to see the information needed by the trace recursion. Retain, for each I,J,

    H_IJ = [[|d_IJ|^2, d_IJ conjugate(e_IJ)],
            [e_IJ conjugate(d_IJ), |e_IJ|^2]].                (7)

This is a rank-one PSD 2x2 matrix before spectral evaluation. The transfer boundary values are

    A_z=|1-z alpha|^2 |det V_z[I,J]|^2
       =|d_IJ-z e_IJ|^2.

The four phases z=1,-1,i,-i reconstruct trace H and its offdiagonal:

    trace H=(A_1+A_-1)/2,
    d conjugate(e)=-((A_1-A_-1)+i(A_i-A_-i))/4.               (8)

They DO NOT determine the difference of the two diagonal entries. The examples (d,e)=(2,1) and (1,2) have identical boundary quadratics. An interior datum A_0=|d|^2, or oriented completion information, is indispensable. Complementary-minor identities couple these missing branches across I,J, so choosing branches independently is invalid.

This is a precise enlarged two-component object for one deletion, but it is not yet a closed positive class under repeated spinor conditioning. Spectral evaluation of (7) uses complex coefficients and destroys PSD order. Repeated deletion can also raise completion defect rank. The viable bridge is a joint inequality on the polarized data (7), constrained by the original normal completion and matching slacks, rather than four independent smaller scalar hull inequalities. Such an inequality remains unproved here. It could imply unrestricted MOC by deleting one coordinate at a time without imposing a fixed rank bound.

## 4. Literature and archive mechanisms checked

I read the full seven-page primary text Brändén–Wagner, arXiv:0809.3225, including the actual proofs of Propositions 3–4 and Theorem 6. Proposition 4 equates Grace-like matching symbols, stability of their plus symbols, and stability preservation. It supplies a composition theorem for stable symbols, not a convex-hull maximum theorem for arbitrary complex evaluations. Its proof uses Möbius covariance and separation by a circle, which does not allow arbitrary spectral configurations to be replaced by separated or real ones.

N061 proves the tangent cone of normalized Grace operators at I is the cone of nonnegative transposition generators. Its proof uses the first-order Rayleigh difference on c_i=c_j=0, divisibility by every remaining c_k, and multiaffinity. Divisible Grace evolutions therefore have a common permutation law. An arbitrary path of actual unitary kernels need not be divisible; using this theorem to integrate all kernels would contradict the exact common-law obstructions.

N014 proves the all-n rank-one-idempotent/complex-bilinear Clifford equivalence, including the converse finite spectral chart. The Gram matrix is complex bilinear, not PSD. N016 gives a genuine all-n real-Gram support stratum but assumes eta z_id is positive real in its positive-Gram branch. N059 proves forest-gate common laws and two-exceptional-spinor transport. Neither supplies positive gluing after a cycle closes. N015 compresses a real rank-two Cayley update to four dimensions, but explicitly leaves a 2x2 Gram positivity inequality and coherent four-index gluing open. N073's holomorphic face argument is valid for affine weight slices, not curved feasible sets merely possessing a complex tangent. These arguments were read beyond their abstracts/status paragraphs.

The number-system proofs give exact affine/module analogues, not real convexity. Particularly useful: all-n descent without an integral trace projection; field/chain-ring similarity ranges; restricted-product care in finite-adele ranges; dense Gaussian-rational exact unitaries; and quantitative open classes around genuine common block pairs. The quaternionic notes correctly separate the signed Hermitian Moore theorem from the unsigned Study determinant on normal matrices. None removes the complex phase cancellation in the original target.

`stream.txt` begins with a claimed all-size rank-two rectangular compression proof using an invisible imaginary tangent. Its full proof is referenced only through a ChatGPT library URL not contained in the workspace. The local text gives the proposed Hessian mechanism, not enough detail to check its real-frame reduction and degeneracies. It remains an unverified proof candidate in this extraction, not an input to the lemmas above. It explicitly identifies rank-three compression as the next obstruction. Later stream entries are historical summaries, variants, and requests; their claims of novelty or completion are not mathematical proofs.

## 5. Historical inventory and reading coverage

Counts and paths in this section describe the investigation's initial scan, before later workspace cleanup. The [archive guide](../../archive/README.md) locates the former root handoffs, stream, generation specification, and preserved build records.

| Class assigned here | Inventory and treatment |
|---|---|
| `docs/full_text` | 64 files, 16,985,717 bytes at initial scan: 62 TXT, one README, one JSON manifest. Giant volume 14,754,344 bytes. Full structural scan of 3651 PDF pages using preserved form feeds and searches for Grace, compression, Clifford, purification, maximum principle, and all-dimensional claims. |
| `docs/pdfs` via extraction manifest | 77 original paths collapse to 59 distinct PDF hashes and 4287 unique pages. Every manifest PDF/text path exists. I did not render all PDF pages. Three one-page diagrams `PicGramDual`, `PicGramSpec`, `PicGramSpecDual` contain no embedded text; their TXT files contain a page break and separate visual descriptions exist. Other mathematical diagrams can also lose information under text extraction. |
| Duplicate text | `MOC_Categorical_Followup` and its `-ea850f7d5c` version have identical TXT SHA-256; likewise `MOC_Research_Results` and `-ad96b73c10`. The three empty diagram texts also hash identically. Different PDF hashes can therefore have identical extracted text. |
| `docs/references` | Six TeX files, 244,541 bytes, all HMSV eight-point invariant sources. Main sources are 0809.1233 and 1103.5255; four smaller files are auxiliary figures/sections. Inventoried and title-matched to extraction; not reread in full because categorical/invariant geometry has a separate owner. |
| `docs/volume`, `code/volume` | One 15,445-byte dependency note read in full; both source-processing Python files read. They protect literal code and repair formatting, not generate mathematical proof. Dependency note explicitly separates elementary necessary cubic/Hessian identities from the HMSV scheme-theoretic converse. |
| `docs/number_systems`, `code/number_systems` | Eleven Markdown notes, 89,730 bytes, read in full; eight Python programs, 36,484 bytes, inventoried by entrypoint. Read the block and prime checkers in full; other checker/plot bodies not fully read or rerun. The prime checker writes beside itself, so I did not execute it under the task's two-path write restriction. |
| `contextdex/checkpoints` | Five files, 61,639 bytes. Full adversarial assessment and twenty-moonshot ledger read; remaining three structurally scanned, not independently replayed. |
| `contextdex/agents` | Nine handoffs, indexed by sections and status language, not fully reread. They concern dimension-four face closures, failed lift tests, and paused historical states. These are provenance, not new instructions or all-n arguments. `.agents` itself is empty. |
| Generation/data | `CreativeSynthesis.json.txt`: 218,271-byte dispatch/schema document; parsed all top-level/master fields and inspected opening protocol. It is a research-generation specification, not a proof. `data/layout.json` is an original-path/hash/curation map; inspected its schema. `data/certificates` contains 137 files, `data/figures` two. Code/research includes generators, exact certificates, numerical probes, plots, and pycache; do not count those as independent mathematics. |

The volume pages read as complete argument segments were principally PDF pp98–108, 218–227, 236–242, 732–738, and the holomorphic face argument around pp653–655, together with its opening index and dependency note. This is roughly forty proof pages, not a complete read of 3651 pages. The rest received structural/mathematical search coverage only. Primary-paper openings were classified across the arXiv extractions; apart from Brändén–Wagner, their full proofs remain unread here. In particular I did not reread the long Grassmannian crystal, flow-equivalence, invariant-ring, SOS, positive-map, and POVM papers. The giant volume's source/data appendix, which dominates the page count, was not line-by-line read. Build trees, Lean dependencies, pycache, and generated result duplication are grouped rather than inflated into independent evidence.

## Verification

Run `python code/research/next_archive_mechanism.py`. It writes only stdout. All exact assertions passed on the rational dimension-five fixture, including arbitrary finite complex spectra in the Schur/signed-affine determinant identity, normality, (1)–(5), four rank-one resolvent defects, and the rank-four defect-vector span. The proofs of the all-n statements above are the displayed block algebra; one fixture is a convention and false-bridge test, not universal evidence.

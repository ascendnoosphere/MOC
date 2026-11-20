# Real-lift moment lines: a useful open chart and a degenerate warning

**Status:** the [independent audit](real_lift_moment_strata_independent_review.md) is **VALID**, with both wording clarifications implemented. These elementary chart tests do not prove actual-profile positivity or MOC. A [subsequent structural theorem](CORANK_TWO_LIFT_EXACTNESS.md), whose [independent original-source audit](corank_two_lift_exactness_independent_review.md) is VALID, establishes the universal rank-two bound on the Hessian-rank12 secant chart. See [the full joint-certificate problem](JOINT_CERTIFICATE_RANK.md).

## 1. The exact rank-two moment problem

Let K be a real14by2 basis of the Hessian kernel of the real Fourier cubic Phi at f, and let

    B : Sym2 -> R14,
    B(uu^T)=grad Phi(Ku),       d=grad Phi(f).

Assume rank B=2. First test d in image B exactly. If it is not, no real critical-point lift exists. If it is, all symmetric moment solutions are

    M(t)=M0+tW,      0!=W in ker B.

The constructive lemma in `JOINT_CERTIFICATE_RANK.md` proves that a real critical-point lift exists if and only if this line contains a PSD matrix. This remains an exact feasibility question; a small numerical residual is not a substitute.

A change of kernel basis acts on W by an invertible real congruence, so its definite, indefinite or singular inertia type is intrinsic.

## 2. Definite kernel direction: no SDP is needed

**Proposition.** If ker B is spanned by a definite W, every d in image B has a rank-at-most-one PSD preimage. If d!=0, it also has a rank-one negative-semidefinite preimage. For d!=0, the two endpoints are distinct.

**Proof.** Change the sign of W so W>0 and write

    M0+tW = W^(1/2) (N+tI) W^(1/2),
    N=W^(-1/2) M0 W^(-1/2).

Let lambda_min<=lambda_max be the two eigenvalues of N. At t=-lambda_min the middle matrix is PSD and singular. At t=-lambda_max it is NSD and singular. Both preimages have the prescribed B-image because W is in ker B. If the eigenvalues coincide, M0 is a scalar multiple of W, hence d=0. Thus for d!=0 they are distinct nonzero rank-one endpoints. QED.

This is a finite exact construction using a two-by-two generalized eigenvalue problem, not an inference from a finite sample. In particular, on this chart the only remaining moment obstruction is the **linear** condition d in image B.

For a homogeneous cubic, the identities

    H_f y=0, grad Phi(y)=grad Phi(f)

are equivalent to grad Phi(f+i y)=0. Hence the PSD endpoint gives a conjugate pair f±i y of complex critical points. The NSD endpoint has the form -vv^T; it gives grad Phi(Kv)=-grad Phi(f), and therefore

    grad Phi(f±Kv)=0.

Thus on this definite-direction chart, a nonzero compatible target has both a conjugate critical-point decomposition and a real critical-point decomposition. This concerns the critical locus; it is not a positivity statement for the original determinant support gap, nor a new finite spectral parametrization theorem.

### Exact rent: the actual spectral example

For

    a=(-1-2i,2+2i,-1+2i,0), b=(-2-i,-2+i,1,2+2i), eta=1,

the exact matrices K and B in the retained verifier `../../code/research/verify_joint_certificate_rank.py` have

    W = [[2152993/103345, 422661/103345],
         [422661/103345,                 1]]

spanning ker B. Its lower diagonal entry is1 and its determinant is strictly positive, so W>0. Exact augmented rank confirms d is in image B. The PSD endpoint is (284,24)(284,24)^T. The other endpoint is NSD, as the proposition predicts. The main verifier recomputes these statements from the Fourier cubic, not only from the printed matrix.


### A phase-orbit identity, without a new genericity assumption

If an actual complex critical point is w=f+i y and g=grad Phi(f), then for any real r,s put f'=r f+s y and y'=-s f+r y. Quadratic polarization and H_f y=0 give

    grad Phi(f')=(r²+s²)g=grad Phi(y'),
    H_f' y'=0.

Thus changing the spectral support phase at fixed |eta| leaves the full fourteen-coordinate gradient unchanged. Equivalently f'+i y'=(r-is)w, so this is also compatible with homogeneity of the critical equations. It permits reuse of the target gradient while inspecting different support directions for a fixed pair of spectra. It does not imply the Hessian kernels or contact permutations are unchanged, and does not prove a support inequality. The main verifier checks the full symbolic r,s identity at the exact actual example as a concrete regression; the proof above is by general cubic polarization.

## 3. Other direction types must not be discarded

If W is indefinite, det(M0+tW) is a quadratic with negative leading coefficient. The PSD portion, if nonempty, is bounded. An exact test uses the real determinant roots together with the two diagonal inequalities; the rank-one reduction guarantees a PSD endpoint if any PSD point exists. Repeated roots, M=0 and identically special polynomials must be handled by the actual non-strict inequalities, not by generic sign assumptions.

If W is singular semidefinite and nonzero, change its sign and make an invertible congruence so W=diag(1,0). Write

    M0=[[a,b],[b,c]].

Then the line contains a PSD matrix exactly in the following cases:

- c>0: choose t>=b²/c-a; equality gives a rank-one PSD endpoint;
- c=0 and b=0: choose t>=-a; the zero matrix is allowed;
- c<0, or c=0 and b!=0: no PSD point.

These conclusions follow immediately from the principal minors and include the degenerate boundary. Under the domain-coordinate congruence M=S M' S^T, replace B by B'(M')=B(S M' S^T); the target d is unchanged. This is a reparametrization of the same moment equation and preserves existence. A separately specified codomain-coordinate change would also transform d, but none is needed here.


## 5. Scope of the improvement

These results replace a PSD solve by an explicit generalized-eigenvalue/linear test on the definite-direction chart and give a correct boundary test on singular directions. The subsequent structural theorem proves rank B<=2 on the entire Hessian-rank12 secant chart; it does not cover higher-corank charts. We have not proved that every actual kernel direction is definite or that these critical-point identities dominate the simultaneous dual objective.

The exact reproducer is `../../code/research/verify_joint_certificate_rank.py`. These are chart-level results, not a solution of unrestricted MOC.

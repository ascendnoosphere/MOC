# Universal real-lift exactness on the corank-two secant chart

**Status:** a new structural theorem derived from the original HMSV contraction, not from numerical sampling or the squared Hessian determinant alone. The [independent original-source audit](corank_two_lift_exactness_independent_review.md) is **VALID**, including singular secant points; all three presentation clarifications are implemented. **Not a proof of unrestricted MOC4.**

This closes the previously open rank-three-restriction possibility on the Hessian-rank12 chart. See the preserved [oracle derivation](corank_two_lift_structure_oracle.md), the [audited joint-rank lemma](JOINT_CERTIFICATE_RANK.md), and [audited moment strata](REAL_LIFT_MOMENT_STRATA.md).

## 1. Objects and exact original-source inputs

Let Phi be the already audited Fourier cubic in14coordinates; write G=grad Phi and H_f=Hessian Phi(f). Over C put

    X=affine cone over M8={G=0},
    S=affine cone over Sec(M8).

X is irreducible of dimension6 and S irreducible of dimension12. The original HMSV contraction gives

    dimension closure G(S) <=10.

The exact source facts used here are:

- `external/m8_hmsv/0809.1233v1/8pts-090708.tex:245–255`: all14partial derivatives generate the ideal of the singular affine cone X, over Q and hence in characteristic zero.
- `external/m8_hmsv/1103.5255v1/8pts-032711.tex:864–867,919–954`: the duality map contracts Sec(M8) dominantly onto N8'. Crucially the proof constructs a diagram of **affine morphisms**, with addition X×X->S and gradient G as the bottom map, commuting up to a nonzero scalar. The cone over N8 has dimension10, so its projected cone has dimension at most10.
- Same source `:1190–1201`: dimension Sec(M8)=11. This dimension argument does not depend on the later multiplicity or septic claims.
- `HMSV_COMPATIBILITY.md`: the full audited invertible coordinate bridge transports these facts to this actual Fourier cubic.

The suppressed septic proposition is **not used**. Knowing only that det H restricts to a square would not give the minors argument below.

## 2. The uniform restriction-rank theorem

**Theorem.** For every f in S with rank H_f=12, and every14by2basis K of ker H_f, write

    G(K(u,v))=B_f (u²,uv,v²)^T.

Then rank B_f<=2. This includes singular points of S on this chart, not only generic smooth points, and does not require det B_Fourier!=0.

**Proof.** At a general smooth point of S, the derivative of G restricted to its12-dimensional tangent space has rank at most10. Thus the full H_f has at least a two-dimensional kernel and rank at most12 there. All13by13minors are polynomial functions; irreducibility and generic vanishing show that they vanish **everywhere on S**.

Now fix any f in S with rank H_f=12, including a possible singular point. Choose an invertible P=(U,K) for which

    P^T H_f P = [[C,0],[0,0]],       C invertible12by12.

Hold this P fixed and consider x -> P^T H_x P. All its13by13minors vanish on S by rank invariance (equivalently Cauchy–Binet). For h in the Zariski tangent space T_fS, the derivative of the minor using the first12rows/columns and one additional row i and column j is

    det(C) (K^T H_h K)_ij.

That minor vanishes on S; its derivative on T_fS is therefore zero. Consequently

    K^T H_h K=0 for every h in T_fS.

As dim T_fS>=12, the linear map h -> K^T H_h K has rank at most2. If b0,b1,b2 are the columns of B_f, cubic polarization gives

    K^T H_h K = [[2<b0,h>,<b1,h>],
                 [<b1,h>,2<b2,h>]].

Here <b,h>=b^T h is the complex bilinear pairing, not a Hermitian pairing. This is the adjoint of B_f up to invertible coordinate scalings, proving rank B_f<=2 and the stronger inclusion

    image B_f subset (T_fS)^perp.                 QED.

The use of the Zariski tangent space is deliberate: no differentiable path through a singular point is assumed.

## 3. Consequences for actual data and exceptional restriction ranks

For actual spectra let w be the complex Fourier product vector, including eta. Then G(w)=0 and G(conjugate w)=0. The real vector f=Re w lies in S as their midpoint. In particular, the proof also gives the stronger universal necessary condition rank H_f<=12 for **every** actual spectral input: a corank-one Hessian cannot occur. The restriction-map/PSD-exactness theorem then applies whenever equality holds, regardless of the Fourier B-determinant chart used for score-height recovery. Higher-corank strata remain outside that exactness theorem.

On this chart g=G(f) is nonzero. Otherwise f is in X, and H_f kills T_fX of dimension at least6, forcing rank H_f<=8.

- If rank B_f=2, the conormal inclusion forces dim T_fS=12, so S is smooth there. Image B_f=(T_fS)^perp. Since Phi vanishes on S, g is in that conormal plane and therefore in image B_f: **linear compatibility is automatic**.
- If rank B_f=1, first test whether g is in its image, then a single binary quadratic sign condition remains.
- If rank B_f=0, no real lift exists because g!=0.
- A singular actual point on this chart, if one exists, must have rank B_f=1 and dim T_fS=13. We do not assert that this exceptional stratum occurs or exclude rank one at smooth points.

Combining the theorem with the independently audited rank-reduction lemma yields:

> On the entire real secant/Hessian-rank12 chart, the PSD moment relaxation B_f(M)=g is exact for the complex-critical-point real-lift question.

This does **not** say every secant point passes that relaxation. Higher Hessian-corank strata are not covered by the uniform theorem. It also does not automatically reconstruct finite spectral charts from an arbitrary accepted critical-locus lift.

## 4. An exact binary-quadratic algorithm

For rank B_f=2 choose n in image B_f independent of g and solve for binary quadratics q,r such that

    G(K(u,v))=g q(u,v)+n r(u,v).

The real lifts are exactly

    r(u,v)=0,       q(u,v)=1.

The nonzero quadratic r has at most two real projective zero directions. For each, include roots at infinity and repeated roots; discard directions where q<=0; return both scalings y=±K(u,v)/sqrt(q(u,v)) for every positive direction. This finds all real lifts, at most four on the rank-two chart. For rational input it uses only quadratic equations and square roots, so coordinates have degree at most4.

For rank one, if compatible write G(K(u,v))=g q(u,v); a lift exists precisely when q has a positive direction. Rank zero rejects. These tests retain all restriction-rank degeneracies; they do not test higher Hessian-corank strata.

The definite-direction result in `REAL_LIFT_MOMENT_STRATA.md` now has a useful stronger reading on this chart: if rank B_f=2 and its one-dimensional symmetric kernel is definite, compatibility is automatic and a real critical-point lift exists. No universal definiteness assertion is made.


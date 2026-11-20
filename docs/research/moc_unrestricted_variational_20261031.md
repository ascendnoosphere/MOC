Rank-two phases and support-preserving pivots
31 October 2026

The target is unrestricted MOC: for arbitrary complex spectra and unitary U,
det(D_a+U D_b U*) should belong to the convex hull of all assignment products.
The calculations below retain the original determinant. They give a complete
parameterization of reducing phase moves and a sharp test for rank-one
rounding. The remaining global rounding inequality is stated explicitly;
it is not inferred from the finite experiments.

Write B=U D_b U*, M=D_a+B and F(U)=Re(eta det M).

1. Complete projector-phase fibers, including singular M

For an orthogonal projector P of rank r put W_P(t)=I+(exp(it)-1)P.
Then F(W_P(t)U) is a real trigonometric polynomial of degree at most
min(r,n-r). In a basis adapted to P, its diagonal blocks are fixed; its
two off-diagonal blocks have respectively
the forms A12+exp(it) B12 and A21+exp(-it) B21. A determinant term uses equally
many entries from the two off-diagonal blocks. This number is at most both r
and n-r. The assertion uses no inverse or nonsingularity assumption.

For rank one this is c+a cos(t)+b sin(t). Consequently a stationary point
with a negative semidefinite full Hessian is globally maximal along EVERY
rank-one projector phase. Checking all rank-one phases therefore does not
repair the Walsh obstruction in moc_pair_maximum_moonshot.txt.

For rank two, stationarity at zero gives

 f(t)=c+a cos(t)+b sin(t)+d cos(2t)-(b/2) sin(2t).

Exactly,

 f(0)-f(t)=(1-cos(t))[a+2d+2d cos(t)-b sin(t)].

Thus zero is a global maximum on this whole fiber exactly when

 a+2d >= sqrt(4d^2+b^2).

Equivalently the real symmetric matrix

 [ a+4d   b ]
 [   b    a ]

is positive semidefinite. In derivatives at zero the same matrix is

 [ -f''             f'''/3            ]
 [ f'''/3           (-4f''-f'''')/3   ].                 (1)

This is an exact finite-jet certificate for an entire rank-two phase fiber.
In particular, if h=-f''>0, global maximality implies
f'''' <= 4h-(f'''^2)/(3h). If h=0 it requires f'''=0 and f''''<=0.
The Hessian condition alone omits this additional inequality.

2. All reducing projector phases have an explicit parameterization

Fix a coordinate unit vector e=e_i and a B eigenvector u=U[:,j], with
rho=e* u and |rho|<1. Choose any unit scalar lambda, and set

 x=u-lambda e,
 N=x* x=2-2 Re(conjugate(lambda) rho),
 z=-(1-lambda conjugate(rho))/(1-conjugate(lambda) rho).

Let Q be any rank-(r-1) orthogonal projector on span(e,u)^perp. Put

 P=x x*/N+Q,       W=I+(z-1)P.                            (2)

Then |z|=1, P is a rank-r orthogonal projector, and W u=lambda e. Indeed,
Q u=0 and z-1=-N/(1-conjugate(lambda) rho). Conversely every nontrivial
rank-r projector phase taking u to a scalar multiple of e has this form:
P u is proportional to x, so x belongs to its range; the other range
directions are orthogonal to u and x, hence to both e and u.

The complete parameter space is therefore T times Gr(r-1,n-2). For n=4,
r=2 this has only three real parameters: lambda and a point of CP^1.
The numerical reducing-move search below optimizes this complete family,
rather than sampling unconstrained projectors and hoping to hit a reduction.

Since B is normal, the transformed matrix has a reducing coordinate e_i:

 det(D_a+W B W*)=(a_i+b_j) det(D_(a without i)+B_reduced),  (3)

where B_reduced is normal with spectrum b without j. Under MOC(n-1), every
endpoint in (3) lies in the original assignment hull. Multiplication by the
possibly complex scalar a_i+b_j preserves the real convex combination.

3. A sharp rank-one pivot criterion at a stationary point

For Hermitian X let

 H(X)=-d^2/dt^2 F(exp(itX)U)|_(t=0),

and let its polarized bilinear form have the same letter. At a stationary
point it annihilates every diagonal Hermitian matrix and every U D U* with
D real diagonal, including mixed terms with any X. This follows by
differentiating the exact left and right phase invariances; the correction
between product coordinates and exponential coordinates is multiplied by
the vanishing first derivative.

Set X=e u*+u e*, Y=i(e u*-u e*) and

 G_ij=[ H(X)       H(X,Y) ]
      [ H(X,Y)     H(Y)   ].

For the rank-one instance of (2), write lambda=exp(i phi). The entire
rank-one phase has Fourier degree one, so its exact endpoint support loss is

 F(U)-F(WU)
 =v(phi)^T G_ij v(phi) / [2 |1-conjugate(lambda) rho|^2],  (4)

where v(phi)=(cos(phi),sin(phi)) up to an irrelevant simultaneous sign.
Indeed, x x*=u u*+e e*-(lambda e u*+conjugate(lambda)u e*); the first two
terms are annihilated by H. Also
(1-Re z)/N^2=1/[2|1-conjugate(lambda)rho|^2].

At a local maximum G_ij is PSD. There is an equal-support rank-one pivot
for this pair exactly when det G_ij=0. Thus a claim that a Hessian null
direction automatically rounds a column must locate a null direction in
one of these specific two-dimensional subspaces; an arbitrary null vector
does not suffice.

There is a stronger uniform identity for determinant supports: at EVERY
stationary point, G_ij is a scalar matrix. Here is its explicit mechanism.
Use a harmless phase of u to make rho=r real, let s=sqrt(1-r^2), and use
the orthonormal basis [e,f,H], where u=r e+s f. With w=-s e+r f write

 A=diag(a,A0),       B=R(r) diag(b,B0) R(r)*,

where R(r) has 2-by-2 block [[r,-s],[s,r]]. Both A0 and B0 are normal
restrictions. Replace r by ANY rho in the closed unit disk and s by
sqrt(1-|rho|^2), keeping A0 and B0 fixed. This is a disk of normal matrices
with the ORIGINAL spectra, whose boundary has e as a reducing coordinate.

Partition the residual matrices on f plus H:

 A0=[alpha  x; w0 D],       B0=[beta y; z C],       K=D+C.

For invertible K set

 u0=alpha-x K^-1 w0, v0=beta-y K^-1 z,
 p=x K^-1 z,        q=y K^-1 w0,
 D0=(a+v0)(u0+b)-p q,
 D2=(b-v0)(u0-a)+p q.

An exact 2-by-2 Schur expansion gives, for the ENTIRE disk,

 det(A+B(rho))
 =det(K)[D0+|rho|^2 D2-(a+b)(rho p+conjugate(rho)q)].      (5)

The coefficient identity extends through singular K, since the left side
is polynomial and the disk coefficients are its uniquely determined
polynomial coefficients. No Hermitian assumption is made on K or on the
effective scalars u0,v0,p,q.

Consequently every real support on this disk is

 f(rho)=C+kappa |rho|^2-2 Re(L rho),
 kappa=Re(eta det(K) D2).

At an interior stationary point rho=r this becomes exactly

 f(rho)=F(U)+kappa |rho-r|^2.                              (6)

At a local maximum kappa<=0. In the rank-one rounder (2), the residual f
phase is mu=z/lambda=(r lambda-1)/(lambda-r), so its disk boundary point
is rho_boundary=conjugate(mu). Exactly,

 |rho_boundary-r|^2=(1-r^2)^2/|1-r lambda|^2.

Comparing (6) and (4), for every phase lambda, proves

 G_ij=c_ij I_2,       c_ij=-2 kappa_ij(1-|U_ij|^2)^2.      (7)

Thus equal-support rank-one rounding is equivalent to kappa_ij=0. At an
ACTUAL maximum that single equality makes the WHOLE CS disk a support
plateau, with an immediate reducing endpoint on its boundary. One possible
uniform completion would force a zero kappa_ij at every irreducible actual
maximum; the Walsh saddle shows that Hessian negativity by itself does not
force it. Equation (5) gives an explicit object on which to test rank-two
global conditions rather than appealing to an unspecified null direction.

The scalar has a compact source formula. Let tau_ij exchange the two labels
a_i and -b_j, i.e. replace (a_i,b_j) by (-b_j,-a_i), holding U fixed. At a
stationary point, with p_ij=|U_ij|^2,

 c_ij/2 = p_ij F_U(a,b)+F_U(tau_ij(a,-b)).

Equivalently, since the determinant is multiaffine in a_i,b_j,

 c_ij/2=(1+p_ij)F_U
  -Re eta[(a_i+b_j)(partial_ai d+partial_bj d)
           -(a_i+b_j)^2 partial_ai partial_bj d].

Indeed, exchanging the labels changes M to
M-(a_i+b_j)(e_i e_i*+u_j u_j*). In the CS formula it sends (D0,D2) to
(-D2,-D0) and reverses the linear term. Stationarity says that the real
linear term equals2|rho|^2 kappa; the formula follows without division.
Thus the identity remains valid at singular M.

Its unweighted sum is exactly the usual swap-gap budget:

 (1/2) sum_ij c_ij
 =sum_(within-A or within-B transpositions tau) [F_U-F_U(tau(a,-b))].

For an elementary proof, use x=(a,-b). The polynomial d_U(x) is multiaffine,
homogeneous of degree n, and invariant under a common translation of all2n
labels. The two-variable exchange identity gives

 (I-tau_kl)d=(xk-xl)(partial_k-partial_l)d
               +(xk-xl)^2 partial_k partial_l d.

Summing, Euler's identity and sum partial_k d=0 give
sum_(all transpositions) tau d=n(n-2)d. Subtract the within-A and within-B
terms and use sum p_ij=n. At an actual maximum all terms on the right are
nonnegative. This explains why merely summing the nonnegative CS curvatures
cannot exclude the strict branch: it reproduces pair-swap information.
A successful weighting must retain cross-source structure or stronger
global-fiber information.

For completeness, the rank-one cosine coefficient can be computed without
differentiating exponentials. When M is nonsingular let C=M^-1, d=det M,
and for a unit vector x put

 alpha=x* D_a x, h=x* C x, u=x* D_a C x,
 v=x* C D_a x, w=x* D_a C D_a x, T=alpha h+u v-h w.

The two-column determinant lemma gives exactly

 det(D_a+W_x(z) B W_x(z)*)
 =d[1+(z-1)(v-T)+(z^-1-1)(u-T)].                         (8)

Hence the cosine coefficient is Re(eta d[u+v-2T]). Formula (4) itself needs
no inverse and remains valid at singular M by the fiber-degree argument.

4. The Walsh obstruction is stronger than a coordinate-pair trap

For the exact data a=(1,-1,-3i,3i), b=(-3,3,-i,i), eta=i and Walsh U/2,
the original full Hessian sum of six squares gives, for ALL sixteen pairs,

 G_ij=36 I_2.

Equation (4), with |rho|=1/2, implies

 F(U)-F(WU)=18/|1-conjugate(lambda)rho|^2 >=8.

Thus every rank-one phase that actually rounds a column strictly loses
support: F(U)=24, while its best rank-one reducing endpoint has support16.
Nevertheless every complete rank-one phase through U is maximized there.
The rank-two phase from the earlier exact cubic construction reaches a
permutation with support48. This separates three statements that must not
be conflated: rank-one fiber maximality, rank-one reducing equality, and
coordinated rank-two ascent.

The verifier independently expands (8) as a quartic polynomial in all eight
real coordinates of an arbitrary projector vector x and checks it against
the Hessian sum of squares. It also checks the full sine coefficient is
zero, all sixteen matrices G_ij, the two-column determinant lemma, the
unrestricted Schur identity (5), and the boundary distance identity in (7).

5. A uniform rank obstruction and a useful low-rank reduction

For any rank-r phase W,

 W B W*-B=(W-I)B W*+B(W*-I),

so its rank is at most2r. If corank(D_a+B)>=2r+1, every such phase has
determinant zero. In particular, corank>=3 permits ANY rank-one reducing
pivot while preserving the complex determinant0. Under MOC(n-1), (3)
therefore proves MOC for that stratum, without any maximality assumption.
A least-dimensional counterexample can have no support maximizer in that
corank>=3 stratum.

No fixed rank-r test can replace actual global maximality uniformly in n.
For n>=2r+2 take

 A=diag(1,...,n),       B=J-A,

where every entry of J is one. Both are Hermitian, A+B has rank1, and ALL
rank-r phase fibers have determinant identically zero. Nevertheless a cyclic
coordinate permutation Pi gives

 det(A+Pi B Pi*)=1-n(n-1).

Indeed, Pi J Pi*=J and A-Pi A Pi*=diag(1-n,1,...,1), so the one-column
determinant lemma gives the displayed integer. The support eta=-1 increases.
This example has simple spectra and a dense eigenbasis for B: if Bv=lambda v
and s=sum v_i, then (lambda+i)v_i=s. No lambda=-i is possible; otherwise s=0
forces v=0. Every eigenvector thus has every coordinate nonzero, and each
eigenspace has dimension one. Symmetry gives simple eigenvalues.

At n=6,r=2 the explicit ascent determinant is -29. This does not refute a
rounding theorem: these flat singular points do admit equal-support pivots.
It rules out using complete rank-two fiber tests as global-max certificates.

6. The exact bridge still needed

A sufficient all-n induction mechanism would be the following statement:

 At every actual support maximum, there is a nontrivial reducing endpoint
 of the form (2) with equal support, using r=1 or2.

For a contradiction proof the required assertion is weaker: assume the
actual global maximum is STRICTLY above all assignment supports and force
either a flat CS disk, another equal-support reducing move, or a rank-two
ascent. This keeps harmless nonmonomial maxima outside the target. A failed
all-U test below the assignment bound would only reject the stronger
one-step domination formulation below.

Even the stronger, directly testable all-U inequality

 F(U) <= max_(i,j,lambda,Q) F(W_(i,j,lambda,Q) U)           (9)

would suffice, by (3) and induction. Neither (1) nor Hessian negativity alone
proves (9): a nonnegative fiber defect need not vanish at a reducing phase.
The role of the actual spectral coefficients remains essential. A common-
minor functional chosen independently of spectra cannot be substituted.

The finite experiments use actual complex a,b and the complete n=4,r=2
family. Twelve initial Haar, polished, and perturbed-Walsh tests all had a
nonnegative best reducing gain, up to roundoff at permutation ties. The same
rank-two parameterization, now using CP^(n-3), found nonnegative reducing
gains in seven n=5 and four n=6 tests.
A separate spectral epigraph adversary fixes
the nonclassical toric or Drury mixer and maximizes separation from sampled
reducing endpoints, then adds the best optimized endpoint as a new cut.
An unconstrained run reached flat support costs. Later runs require a
nonzero variance across all24 permutation supports and separation of all
eight spectral labels (a,-b). Solver residuals and feasibility are retained;
an unsuccessful solver is not a certificate. These searches test (9), not
the entire unrestricted conjecture, and no finite search proves (9).

In the last constrained pass, seven toric and five Drury epigraph candidates
were tested. Every optimized reducing move improved the candidate. One
converged feasible toric candidate with positive separation from all sampled
endpoints was rejected by the newly optimized endpoint; this demonstrates
why a finite sampled endpoint set cannot certify the bridge. Some epigraph
solves failed their convergence or feasibility checks. No positive numerical
candidate against the complete-family inequality (9) was retained.
An independent floating endpoint audit checked all23 selected moves; their
largest reducing-coordinate residual was6.5e-12. The support gradients,
vertex-variance gradient and spectral-separation gradients were separately
checked by central finite differences. These are implementation checks,
not global optimization certificates.

Reproduction:

 python code/research/moc_unrestricted_variational_rounders.py --exact-only
 python code/research/moc_unrestricted_variational_rounders.py --seconds 45 --cases 12 --starts 2
 python code/research/moc_unrestricted_variational_rounders.py --seconds 40 --cases 8 --starts 2 --n 5 --seed 202610311659
 python code/research/moc_unrestricted_variational_rounders.py --seconds 40 --cases 8 --starts 2 --n 6 --seed 202610311700
 python code/research/moc_unrestricted_variational_rounder_adversary.py --seconds 45 --samples 16 --mixer toric
 python code/research/moc_unrestricted_variational_rounder_adversary.py --seconds 45 --samples 16 --mixer drury

Outputs are under build/moc_unrestricted_20261031/variational/:
rounders_exact.json, rounders.json, rounder_adversary_toric.json and
rounder_adversary_drury.json; cross-dimensional tests are in rounders_n5.json
and rounders_n6.json, and selected-endpoint validation is in
rounders_endpoint_audit.json. The existing ranktwo.json contains the previous
unconstrained complete-fiber searches.

Primary source checked during this pass: the publisher abstract of
J. I. Mulero-Martinez, A variational framework for determinantal inequalities
of normal matrices: Successes and obstructions, LAA740(2026),19-38,
https://doi.org/10.1016/j.laa.2026.03.019. It retains the general conjecture
and allows nonmonomial support maximizers. The publisher full text returned
403; no claim about its uninspected proofs is used above.

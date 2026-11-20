## Round 046 — Audit and sharpen the root's universal scalar (8,8) reduction

For arbitrary complex rays, normalization lives in Herm2, a real space of dimension four. The compressed matrix lies in M2(C). The nondegenerate real quadratic Re(η det Z), for η≠0, has signature (4,4): a complex linear change diagonalizes the complex quadratic, and each complex square contributes one positive and one negative real direction.

With s active ray weights, the affine tangent has dimension at least s−4. At a minimal-support maximizer, the first derivative vanishes and the restricted quadratic is negative semidefinite. Its rank is at most four by the negative index of the ambient form. If s>8, it therefore has a nonzero null vector. Along that direction the objective is exactly constant, not merely stationary to second order. Trace positivity makes the feasible weight segment bounded, so an endpoint removes a ray.

Apply this argument successively to the two frames. A strict violation of the original fixed halfspace survives, while every reduced spectral matching vertex is one of the original vertices. Hence a scalar counterexample in any finite sizes would imply one with at most eight rays on each side.

This is a valid reduction to **(8,8) for scalar positivity**, with the coplanar refinement (6,6) when both sides are real in suitable bases. It does not preserve all moments or justify a common-law/Bell reduction to eight outcomes. The distinction matters because the determinant is quadratic in the ray weights.


## Round 059 — Star plaquette cosines have a finite global phase-consistency test

The anchored-minor identity

\[
\det X[\{i,k\},\{j,l\}]
=u\det U[\{1,i,k\},\{1,j,l\}]
\]

follows by expanding X=uV−cr. Complementary unitary minors determine its squared modulus. Therefore p and anchored q determine each plaquette cosine, not only its triangle-inequality range.

There is a further coherence condition. On a 3×3 star with all entries nonzero, row and column phase gauges make the first row and column positive. Only four phases θ22,θ23,θ32,θ33 remain. The four plaquettes using row 1 and column 1 determine their cosines. Each phase has at most two choices modulo 2π. Hence all remaining plaquette constraints can be checked among at most 16 sign choices, using their phase differences and alternating sums.

This is necessary and sufficient for realization of the prescribed moduli and all plaquette cosines by a complex star matrix: necessity follows from the gauge; sufficiency follows by explicitly filling its four entries for a successful sign choice. It is not yet sufficient for an anchored unitary. One must additionally impose Xr*=−c and the two Gram identities from Round 058. The observation nevertheless rules out treating all local cosine intervals as independent free parameters, and replaces a continuous phase search by a finite check on the generic star stratum.


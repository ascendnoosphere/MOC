# Orbit, reciprocal profiles, and disk-elimination experiments

Statuses refer to Cycle 02 paths 04, 08, 09 and 11 and the corresponding Cycle 01 proposals. Symbolic proofs and fixture diagnostics are separate. Finite checks are not used to prove a general inequality.

## 04. Triple SDP and actual orbit ties

The checked Lean result is stronger than the proposed rank-one slack support test in one respect: all three objective matrices have identical off-diagonal entries when the basis and one genuine 3-cycle are certified optima. Subtract the common matrix; its contribution is the trace in every orthonormal frame. The objective is then a diagonal assignment objective. The dual slack proof uses a zero sum of nonnegative selected diagonal slacks, not enumeration of frames. It depends on actual orbit ties and dual feasibility. Qutrit projective simulability reference: Oszmaniec et al., DOI [10.1103/PhysRevLett.119.190501](https://doi.org/10.1103/PhysRevLett.119.190501).

Sharp exact fixture: for a 3-cycle (p), let (S_j) be the orthogonal projector on the unique coordinate outside ({j,p(j)}), and take (H_j=-S_j,Y=0,lambda_j=0). Every value is at most zero and both those assignments equal zero; slacks are nonzero and have rank exactly one. At the other extreme all (H_j) may be the same Hermitian matrix, with zero slacks and objective identically constant, including a dense choice of basis. These are SDP fixtures, not certified terminal determinantal witnesses. Search for existence of an actual triple tie at a rank-moment terminal witness is unresolved. A numerical search imposing every local constraint was not run: no exact characterization or witness for the terminal stratum was available to instantiate the search without silently changing it to ordinary orbit criticality.

## 08. Four-dimensional orthogonal fixture and scalar direction

For the supplied `1/41` orthogonal mixer, the separator is supported on
((A_1A_2B_0,+1),(A_1B_0B_1,-1),(A_2B_1B_2,+1),(B_0B_1B_3,+1)).
The general classification of any individual scalar spectral evaluation is (w_S=Re(etaprod_{iin S}z_i)), with complex reciprocal labels. Restrict to rows (A_1,B_2,B_3) and columns (A_2B_0,A_2B_1,B_0B_1). These index sets are disjoint, so the corresponding coefficients are the real part of an outer product, with rank at most two: (Re(u v^T)=Re uRe v^T-Im uIm v^T). But the separator restricts to an upper triangular matrix with all three diagonal entries one and entry ((1,3)) equal to minus one. Thus it has rank three and *cannot be that spectral direction*. This is a symbolic feasibility rejection, not a check of every candidate spectrum. Nor does it exclude a different spectral direction, a separator modulo affine identities, or a positive combination of spectral directions. The general dense SO(4) scalar stationarity goal remains open. The companion overlap experiment verifies the underlying orthogonal fixture separately.

## 09. Möbius zeros and disk barriers

Regular common fractional maps preserve the labeled zero graph. Therefore the multiplicities, row/column degrees, and Hall quantities computed from this graph cannot change under regular normalization. Singular maps require a separate limit with the common determinant factor.

The new transfer uses a direct energy argument associated with exterior feedback (compare Redheffer DOI [10.1002/sapm19624111](https://doi.org/10.1002/sapm19624111)). The Schur-complement comparison background is Cottle DOI [10.1016/0024-3795(74)90066-4](https://doi.org/10.1016/0024-3795(74)90066-4). Center the normal partner at the flat-pair circle center. If the centered partner is strictly contractive at the circle radius, and the shifted spectator labels are at or outside that radius, the inactive pivot is invertible and the active effective matrix is also strictly contractive at that radius. This yields zero flat-pair couplings by the exact Gram-matrix factorization, checked in Lean. The norm condition is on the entire original block, not on the eigenvalues of the effective operator.

Adversarial symbolic family, radius one and center zero: couple one active and one spectator coordinate by the real symmetric block `[[1−δ, δ/2],[δ/2,−1+δ]]`, with spectator label (1). For (0<delta<1), the square of that block is (((1-delta)^2+delta^2/4)I), strictly below (I). The pivot is (delta); the active effective scalar is (1-5delta/4), strictly within the unit disk even as the pivot becomes arbitrarily ill-conditioned in the presence of a second spectator with pivot one. Zero padding of the original block supplies targeted instances at orders 4, 5 and 6 with spectator labels 1. Thus no uniform lower bound on the pivot is required. As an independent exact check against replacing singular-value exclusion by eigenvalue exclusion, the old matrix `[[2,3],[0,2]]` has both eigenvalues 2, while its Gram matrix minus the identity equals `[[3,6],[6,12]]`, which has the nonzero kernel vector ((-2,1)). The theorem does not guarantee that arbitrary spectra admit a suitably arranged circle and actual tied flat pair.

## 11. Reciprocal projective coordinates; spinor balance

Lean recovers the ratio of a tested edge to a fixed nonzero pivot, even
when the tested edge is zero. It cancels a common nonzero companion
product. If two matching profiles are related by a nonzero complex scale,
the ratio identity gives a single common scale and an opposite translation
of the original spectral lists. Each edge-to-pivot comparison requires a
nonzero companion.

Frame balance alone does not make a frame tight or force rank two. Take
identical two-sided lists with every vector equal to the first coordinate
vector. The balance holds and the kernel has rank one. For any order
$n\ge 3$, replace one vector per side with the second coordinate vector.
The kernel then has rank two, but the balanced frame operator is
$\operatorname{diag}(n-1,1)$, not a multiple of the identity. Using both
signs of a coordinate vector gives antipodal duplicates with the same
frame contribution. None of these fixtures certifies stationarity at a
strict-excess terminal witness.

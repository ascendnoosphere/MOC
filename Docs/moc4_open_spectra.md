# Spectral stability of the order-four Marcus–de Oliveira inclusion

## Statement

For ordered spectra a,b in C⁴, write zπ=∏ᵢ(aᵢ+bπ(i)) and d(U)=det(Dₐ+U Dᵦ U*). A base pair has the **singleton property** if, for every U, a permutation law λ recovers d(U) and has Pr[π(i)=j]=|Uᵢⱼ|². The order-four Hermitian-side theorem in the accompanying work supplies this property whenever a is real. A common pole-free Möbius transformation transports the same law, so one concyclic spectrum also suffices.

**Theorem.** Suppose a base pair has the singleton property. Suppose its 24 permutation products are distinct, span a two-dimensional polygon, and no exposed edge contains a third product. Then an open neighborhood of the pair in C⁴×C⁴ satisfies MOC for every relative eigenbasis U. For the explicit example below the neighborhood contains a closed polydisc of radius 10⁻⁸ in all eight spectral coordinates.

This result uses the singleton property only at the center of the neighborhood. The perturbed pairs can have two nonconcyclic spectra.

## Signed determinant identity

Put βπ=sgn(π)∏ᵢ Uᵢ,π(i)/det U and cπ=Re βπ. For equally sized I,J, Laplace expansion followed by the complementary-minor identity gives

    Σ_{π(I)=J} βπ = |det U[I,J]|².

In particular the real coefficients c sum to one and have singleton marginals |Uᵢⱼ|². Expansion of zπ by choices of a and b at its four sites gives d(U)=Σπ cπ zπ. Indeed the complex coefficients β give this identity by direct expansion of det[(aᵢ+bⱼ)Uᵢⱼ]/det U. All coefficients of every spectral monomial are real subset marginals, so replacing β by c preserves the identity. The coefficients c depend only on U, and |cπ|≤∏ᵢ|Uᵢ,π(i)|.

Orient each polygon edge (p,q) counterclockwise. Define its real slacks and scalar gap by

    vτ = Im( conjugate(zq−zp) (zτ−zp) ),
    G(U) = Im( conjugate(zq−zp) (d(U)−zp) ).

Then G(U)=Στ cτ vτ. At the base, G(U)=Στ λτ vτ as well. Its two endpoint slacks vanish and all other slacks are positive. Small complex spectral perturbations keep all these strict inequalities, hence preserve the polygon's edge labels and orientation. Primes below denote the perturbed slacks and gap.

## Equality at the base

Let δ be the smallest positive base slack for this edge. At equality its recovering law is supported on p,q, so the bistochastic matrix |U|² is a mixture of their two permutation matrices. A mixture concentrated at one endpoint makes U monomial. For a strictly intermediate mixture, a cycle of length at least three in p⁻¹q would give two rows with exactly one common nonzero column, violating unitarity. The only remaining relative types in order four are one transposition and two disjoint transpositions.

For two disjoint transpositions, relabel columns so p is the identity. Then U has two nontrivial independent 2×2 blocks. The two-dimensional determinant in each block is the segment mixture at its two permutations. Multiplying the two mixtures represents d(U) with positive weight on both single-transposition permutations as well as on the endpoints. Those two other products have strictly positive edge slack, ruling out equality.

For a single transposition the support is precisely one 2×2 block and two 1×1 blocks, after relabeling. Every such U produces a point on the edge by the 2×2 identity, and all points of the edge occur.

## Stability on a transposition edge

Let S be the union of the two endpoint permutation supports. Let Q=Σ_{(i,j)∉S}|Uᵢⱼ|². At the base, Q is the expected number of assignments outside S under λ. A permutation has at most four such assignments, and the endpoints have none. Consequently G(U)≥δ Q/4.

Every permutation τ different from the two endpoints crosses the corresponding block partition. It uses at least two entries outside S, since each permutation preserves total in-flow and out-flow across each block. Thus the product estimate on c and arithmetic-geometric mean give |cτ|≤Q/2. There are 22 excluded permutations. If e=maxτ|v′τ−vτ|, the exact signed identity gives

    G′(U) ≥ Q(δ/4−11e).

Therefore e≤δ/44 is a uniform sufficient condition for this edge, with no restriction on U.

## Quantitative estimate near the endpoints of any other edge

Relabel one endpoint to the identity. Let vτ be any nonnegative list of edge slacks with v_id=0, let δ₁=min_{i<j} v_(ij)>0, and let M=maxτ vτ. Define Q=Σ_{i≠j}|Uᵢⱼ|² and ρ=max_{i≠j}|Uᵢⱼ|. These definitions can use the perturbed edge slacks directly. Then

    Στ cτ vτ ≥ Q(δ₁/2−17Mρ).

To prove the estimate, put wᵢⱼ=(|Uᵢⱼ|²+|Uⱼᵢ|²)/2 for i<j. Substitute the two corresponding singleton identities for the transposition coefficient c_(ij) into the edge gap. Its transposition contribution becomes Σ_{i<j} wᵢⱼ v_(ij), which is at least δ₁Q/2. The new coefficient multiplying cτ for any τ moving at least three labels is

    vτ − (1/2) Σ_{i:τ(i)≠i} v_(i,τ(i)).

Its absolute value is at most 2M. There are 17 such permutations and each has |cτ|≤ρQ/2 by the product bound on three off-diagonal entries. This proves the estimate.

Apply it to each endpoint of a nontransposition edge. At the base all its transposition-neighbor slacks are strictly positive. On sufficiently small spectral perturbations, δ₁ stays bounded below and M stays bounded above. Fixed neighborhoods of the two monomial tori therefore obey the perturbed inequality uniformly. On their compact complement, the classification of base equality proves that the base gap has strictly positive minimum. Uniform continuity preserves positivity there. Intersect the neighborhoods obtained for the finitely many edges. This proves the theorem.

## A closed polydisc with explicit constants

Use zero-based labels. Take

    a=(−3,−1,2,4),       b=(6−5i,−6+3i,2+4i,−7).

The counterclockwise edge cycle is

    1302, 1320, 1230, 2130, 2103, 2013,
    0213, 0231, 0321, 0312, 3012, 3102.

The labels on every edge differ by exactly one transposition. For the twelve edges the smallest nonendpoint slacks, evaluated by the integer oriented-area formula above, are

    57600, 78750, 78750, 85680, 18576, 8880,
    204, 204, 143104, 270400, 1285440, 194240.

The squared diameter of the 24 vertices is 25,457,650, less than 6000². Each base factor has modulus less than 12. For ε=10⁻⁸, perturb each individual eigenvalue by any complex number of modulus at most ε. All factors at both endpoints of the perturbation have modulus at most 13, and each factor moves at most 2ε. Telescoping a product of four factors shows that each vertex moves by at most R=18000 ε, since 8·13³<18000. The two differences in each oriented area move by at most 2R each, hence

    maxτ |v′τ−vτ| ≤ 4R(6000+R)
                   = 2700000081/625000000 < 204/44.

All nonendpoint slacks remain strictly positive. The transposition-edge estimate applies to all twelve edges, proving MOC throughout the closed polydisc and for every U.

One explicit pair with both spectra nonconcyclic is

    a′=(−3+10⁻⁹ i,−1,2,4),      b′=(6−5i,−6+3i,2+4i,−7).

The last three elements of a′ are distinct real numbers; their only generalized circle is the real line. Its first element is nonreal. The cross-ratio (b₀−b₂)(b₁−b₃)/[(b₀−b₃)(b₁−b₂)] is (−17−6i)/65, also nonreal. The [spectral-neighborhood verifier](../Code/verify_moc4_open_spectra.py) checks all integer and rational numerical assertions with the Python standard library.

## Relation to earlier work

The supplied archive already contains a local-to-open theorem at repeated-spectrum centers (a,b,c,c) in [the local-to-open proof](theorems/finite_and_spin_geometry/dual_local_to_open_theorem.md). The present statement applies at simple-spectrum bases with the singleton property and provides explicit constants at the example. Kovačec, “The Marcus–de Oliveira conjecture, bilinear forms, and cones,” Linear Algebra and its Applications 289 (1999), 243–259, DOI 10.1016/S0024-3795(97)10004-0, explicitly identifies the Hermitian-side order-four problem. Shitov, Izvestiya: Mathematics 89 (2025), 862–869, DOI 10.4213/im9292e, gives a different sufficient spectral criterion. The present supplement makes no historical priority claim.

# Exact certificate for an all-unitary spectral family

## Statement and scope

For every unitary matrix U of order four and every pair of complex numbers t,z,

A(t)=diag(0,1,2,t),  B(z)=diag(0,1,z,2+z)

satisfy the Marcus–de Oliveira inclusion. More strongly, for each U there is one probability distribution p_pi(U) on S_4 such that

    det(A(t)+U B(z) U*) = sum_pi p_pi(U) product_j(a_pi(j)(t)+b_j(z))

identically for all complex t,z. This is an all-unitary spectral class, not merely a fixed relative unitary result. No novelty claim is made. The theorem does not prove MOC for arbitrary spectra.

Both spectra can be simple and noncocircular. For example, take Im(t) nonzero and z=i. The points 0,1,2,t cannot lie on one generalized circle, and 0,1,i,2+i do not lie on one generalized circle.

## Coordinates and exact certificate

For any polynomial f(t,z) of degree at most one in t and at most two in z, use the six evaluation coordinates in this exact order:

    f(0,0), f(1,0), f(0,1), f(1,1), f(0,2), f(1,2).

These six values determine f by polynomial interpolation. In the implementation the outer loop is z=0,1,2 and the inner loop is t=0,1.

For pi in S_4 define the real integer vector

    V_pi = (1, z_pi(0,0), z_pi(1,0), z_pi(0,1),
                  z_pi(1,1), z_pi(0,2), z_pi(1,2)),
    z_pi(t,z) = product_{j=0}^3 (a_pi(j)(t)+b_j(z)).

There are 24 vectors, 19 distinct input vectors, and their affine hull in the last six coordinates has dimension six. The homogeneous 7-by-24 matrix has rank seven. The polytope P=conv{V_pi} has 27 facets, represented by integer covectors h with h dot V_pi >= 0. A facet certificate includes a rational nonnegative decomposition

    h dot V_pi = sum_{I,J: |I|=|J|} lambda_(I,J) 1{pi(J)=I}

valid for all 24 permutations. Every lambda is nonnegative.

The complete matrix, all 27 integer facets, and their lambda coefficients are stored in facets_gamma_result.json. All index sets and permutations in code use indices 0,1,2,3. There are no numerical tolerances in the proof verifier.

## Why the certificate proves the theorem

Write

    alpha_pi(U) = sgn(pi) product_j U_pi(j),j / det(U).

These coefficients need not be nonnegative, but the determinant expansion gives

    sum_pi alpha_pi = 1,
    det(A(t)+U B(z) U*) = sum_pi alpha_pi z_pi(t,z).

For equal-cardinality index sets I,J, the complementary-minor identity for a unitary matrix gives

    sum_{pi: pi(J)=I} alpha_pi = |det U_(I,J)|^2.

Indeed, expanding the restricted permutation sum yields the product of the I,J minor and its complementary minor, with the usual complementary-minor sign. Jacobi's identity converts the complementary minor into det(U) times the conjugate of the first minor, with the same sign.

At all six interpolation nodes, A(t) and B(z) are real diagonal matrices. The sum A(t)+U B(z) U* is Hermitian and its determinant is real. Let Y(U) be the homogeneous vector consisting of 1 and these six real determinants. Then

    Y(U) = sum_pi alpha_pi(U) V_pi.

For every certified facet h, its indicator decomposition therefore implies

    h dot Y(U) = sum_(I,J) lambda_(I,J) |det U_(I,J)|^2 >= 0.

Since the certified facet list is complete, Y(U) belongs to P. Thus there are nonnegative real p_pi(U), summing to one, with Y(U)=sum_pi p_pi(U)V_pi. Polynomial interpolation extends the resulting equality at six nodes to the full identity in arbitrary complex t,z. This proves the stated inclusion.

The proof uses signed coefficients only to transfer finite linear identities to squared minors. Positivity comes from the separate facet certificates and then from polytope membership. It does not assume a nonnegative distribution reproducing every squared minor.

## Why facet completeness is exact

The verifier independently reconstructs all 24 vectors using integer arithmetic. For each proposed facet it checks nonnegative values on every input point, and exact rank six of the homogeneous vectors on that facet. Thus each proposal is a genuine facet of P. It checks that the 27 facet vertex sets are distinct.

For each proposed facet, the verifier exhaustively enumerates all five-point subsets of its input points. In an injective affine chart of that facet, every affinely independent five-point subset determines a possible supporting hyperplane. Exact rational row reduction and sign tests find all its ridges. Every ridge contains five affinely independent vertices, so this enumeration misses none.

In total the verifier checks 9,432 candidate ridge bases and obtains 134 distinct ridges. Every ridge is contained in exactly two distinct listed facets. A ridge of a polytope is contained in exactly two facets, so the list is closed under facet adjacency. The facet adjacency graph of a full-dimensional polytope is connected; hence the nonempty closed list is the entire facet list.

One elementary justification of adjacency connectivity is to connect relative interior points of two facets by a generic path on the polytope boundary. The path can avoid all faces of codimension at least three and crosses only ridges, giving a path through adjacent facets.

## Reproduction

Run:

    python verify_all_u_family.py

Only Python's standard library is used by the verifier. Discovery used SciPy, but no SciPy output is trusted without exact checks. The certificate verifier checks the facet/minor identities, full dimension, facet ranks, distinctness, and exhaustive ridge closure.

Expected counts: affine dimension 6; 24 input vectors; 19 distinct input vectors; 27 facets; 134 ridges; 9,432 candidate ridge bases.

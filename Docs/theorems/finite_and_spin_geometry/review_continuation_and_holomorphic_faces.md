## 1. The valid spectral set is closed

For a spectral parameter p=(a,b) in C^(2n), write

    d_U(p)=det(D_a+UD_bU*),
    z_pi(p)=product_i(a_i+b_pi(i)),
    h(p,eta)=max_pi Re(eta z_pi(p)),  |eta|=1.

Define V_n to be the parameters for which Re(eta d_U)<=h for every U and eta. The functions involved are continuous and U(n) times the support circle is compact. Therefore V_n is closed. Its complement is open, since one strict separating witness remains a witness under sufficiently small spectral perturbations.

The maximum violation is always nonnegative because a permutation unitary gives equality for a maximizing permutation. Thus V_n is the zero set of this nonnegative continuous maximum-violation function. A boundary point may have additional equality witnesses even if the neighboring valid points do not.

## 2. A verified local continuation principle

Fix p_0 in V_n and a phase eta_0. Suppose every equality unitary belongs to one of finitely many proper block families S. Assume each such family is MOC-valid for nearby spectra, the objective has identically zero normal derivative on S for all spectra, and its Hessian is strictly negative on the normal space at the equality points under consideration.

These assumptions imply a neighborhood of (p_0,eta_0) in which the support inequality holds for every U.

Here is the complete compactness argument. Each S is a closed smooth submanifold of U(n). Near its compact equality subset, use a tubular chart U=exp(K)U_0, with U_0 in S and K normal. Strict negativity at the equality subset remains uniform for nearby U_0, small K, and small parameter perturbations. The exactly vanishing linear term and Taylor's integral remainder give

    Re(eta d_exp(K)U0(p)) <= Re(eta d_U0(p)) <= h(p,eta).

Outside these finitely many tubular neighborhoods, the base support gap is strictly positive by compactness; uniform continuity preserves it. Repeating this argument at each base phase and using a finite cover of the phase circle gives an open spectral neighborhood.

The zero-normal-derivative assumption is automatic for a coordinate block family. For block diagonal M, adj(M) is block diagonal. A normal unitary variation makes the first variation of UD_bU* off-block, so tr(adj(M) delta M)=0. The adjugate statement remains true at singular matrices because it is a polynomial identity.

The important quantifier is that this covers all equality witnesses at one base parameter. A finite cover of the support circle does not cover all spectral parameters.

## 3. Audit of the scalar-plus-rank-two base point

The note dual_local_to_open_theorem.md takes A_0=diag(a,b,c,...,c). Its ordered-pair vertices are

    g_ik=(a+beta_i)(b+beta_k) product_(j not i,k)(c+beta_j).

The exact oriented-row law is valid. For orthonormal r,s, let q_ik=|r_i s_k-r_k s_i|^2. Its fractional edge orientation has outgoing marginal |r_i|^2 and incoming marginal |s_i|^2. The required cuts follow from

    sum_(i<k in S) q_ik
    = ||r_S||^2 ||s_S||^2 - |<r_S,s_S>|^2
    <= ||r_S||^2.

The determinant expansion therefore is a convex combination of the g_ik.

When the g_ik are distinct and no three are collinear, an exposed face has at most two labels. Its equality loci are exactly the types stated in that note. In the only potentially ambiguous type F={(i,k),(j,l)}, with distinct first and second labels and no reversal, a law with masses theta and 1-theta forces r,s to have the corresponding two-point supports. One overlap between those supports makes orthogonality force theta(1-theta)=0. If the supports are disjoint, q_ik=theta^2 while the orientation law gives q_ik=theta. Again theta is 0 or 1.

At r=e_i,s=e_k, the independent second-order expansion of the support gap is

    (h-G_ki)|K_ik|^2
    + sum_(j not i,k)(h-G_jk)|K_ij|^2
    + sum_(j not i,k)(h-G_ij)|K_kj|^2,

times the square of the path parameter. The exact indexing of K depends on whether the row frame or its adjoint is varied; the moduli and the displayed ordered-pair replacements are unchanged. There are no mixed quadratic terms: a one-step tangent variation either swaps the two exceptional labels or moves one of them into the complement. Every displayed replacement is outside F in this face type, so every coefficient is strictly positive.

For shared-label and reversed faces, the inequalities in the original note directly bound the squared normal distance to, respectively, a 1+(n-1) or a 2+(n-2) block family. The proof therefore satisfies the local principle in Section 2. In dimension four its lower-dimensional block hypotheses are available, and the claimed open neighborhood is a genuine theorem, subject only to the explicit general-position assumption stated there.

## 4. Commuting contacts cannot cause a generic first failure

Assume at p_0 that all n! full permutation values are distinct and no three are collinear. Suppose U_0 is a commuting equality witness. These assumptions imply that both spectra are simple; after relabeling and removing diagonal phases, U_0=I.

For a skew-Hermitian K with zero diagonal, the determinant along exp(tK) has the expansion

    d_exp(tK)=z_id+t^2 sum_(i<j)|K_ij|^2(z_(ij)-z_id)+O(t^3).

One can obtain each diagonal term by the exact two-row rotation formula. All mixed second-order terms vanish at a diagonal sum; equivalently, every second-order closed index walk is a two-cycle. Thus the support Hessian is diagonal in the complex off-diagonal entries of K, with coefficients twice the transposition support gaps.

If the exposed face contains only z_id, every such gap is positive. If it contains z_id and another value z_tau, every gap is still positive unless tau is a transposition. In that exceptional case there is exactly one zero pair direction. Include the entire corresponding 2-by-2 mixing block in S; all normal directions have strict negative Hessian. This family is solved by the elementary dimension-two formula and remains solved under every spectral perturbation. Section 2, applied locally near U_0, excludes any nearby violating witness.

Consequently, if p_k outside V_n tends to a generic p_0 in V_n, choose violating (U_k,eta_k) and pass to a convergent subsequence. Its limit (U_0,eta_0) is an equality witness at p_0 and U_0 cannot commute with A_0 and B_0. It is a noncommuting global support maximum. Its first derivative in every unitary direction vanishes and its Hessian is negative semidefinite.

The first-order equation may be written

    eta_0 [B_0,adj(A_0+B_0)] is Hermitian.

This follows by differentiating against every skew-Hermitian K. The commutator may equivalently be replaced, with the appropriate minus sign, by the commutator with A_0.

This is a precise necessary obstruction for continuation through generic spectral points. It does not exclude the obstruction.


## 6. Holomorphic rigidity inside an open valid region

Now suppose p_0 lies in the interior of V_n and the permutation hull is in the same general position. Fix U. If d_U(p_0) lies at a unique exposed vertex z_pi(p_0), the strict support gap to all other vertices persists locally for the same phase. Hence

    Re(eta(d_U-z_pi))<=0

on a complex neighborhood, with equality at p_0. The harmonic maximum principle forces the holomorphic difference to be constant there, and its value at p_0 is zero. The polynomial identity theorem gives d_U identically equal to z_pi for every spectral parameter.

If d_U(p_0) lies on an exposed edge [z_pi,z_tau], put

    H=(d_U-z_pi)/(z_tau-z_pi).

The denominator is nonzero nearby. All other normalized vertices stay strictly in the same open half-plane bounded by the real axis. Validity gives a fixed sign for Im(H) throughout a complex neighborhood, and Im(H)=0 at p_0. Therefore H is a constant real number t in [0,1]. Clearing the denominator yields the global polynomial identity

    d_U=(1-t)z_pi+t z_tau.

The weights are constant for this fixed U. They are not arbitrary functions of the spectra.

## 7. Two-permutation identities force one mixing block

Suppose 0<t<1 in the preceding identity. Relabel pi as the identity. Comparing the singleton coefficients gives

    |U_ij|^2=(1-t)delta_ij+t delta_(j,tau(i)).

If tau has a cycle of length at least three, two consecutive rows in that cycle overlap in exactly one nonzero column. Their inner product cannot vanish, contradicting unitarity. Thus tau is a product of disjoint transpositions.

If it has at least two such transpositions, choose I containing one label from each of two distinct transposition blocks. The singleton support pattern forces U to be block diagonal across these blocks. Its principal two-minor then has squared modulus (1-t)^2. The asserted two-permutation profile gives instead 1-t. These differ for 0<t<1. Therefore tau is a single transposition, and U is a single 2-by-2 unitary block together with monomial factors. The cases t=0 and t=1 are monomial.

Sections 6 and 7 classify generic boundary equality within an open valid spectral region. They do not classify a new equality witness at the boundary of that region, where the maximum-principle hypothesis of a full complex neighborhood is absent.

## 8. A holomorphic minimum-face lemma

Let P={t>=0:At=b} be a nonempty compact real polytope, with rank(A)<=d. Let X be a complex-linear-coordinate map on the real t variables taking values in C^m, and let F be holomorphic on an open set containing X(P). Then Re(F(X(t))) has a maximizer with at most d+m positive coordinates, provided F extends holomorphically along the affine lines used below. A polynomial F always satisfies this condition.

Choose a maximizer t of minimum support S, of size s. The tangent space T to its active face has dimension at least s-d. If X has a nonzero kernel vector on T, moving along that vector leaves F unchanged until a coordinate reaches zero, contradicting minimality.

Otherwise X is injective on T. If s-d>m, its real image L in C^m has dimension greater than m. Since dim_R(L)+dim_R(iL)>2m, the intersection L intersect iL contains a nonzero vector. Hence L contains a complex line. The two real preimages of that line span a feasible local disk about t. On the disk, Re(F) is harmonic and has an interior maximum. It is constant on the disk. The identity theorem extends this constancy along a real diameter as far as the affine line is defined, so one can reach a face with a deleted coordinate. This is again a contradiction.

Thus s<=d+m. The argument uses an actual complex line in the tangent image; a single direction with zero Hessian is insufficient.

## 9. Application and an adaptive refinement for MOC updates

For U=I+Y(V-I_r)Y*, let W_i=y_i*y_i be the Hermitian rank-one frame atoms, so sum W_i=I_r. In the exact spinor normalization, let P_i be trace-one complex 2-by-2 idempotents and set

    N(t)=sum_i t_i P_i tensor W_i,
    P={t>=0:sum_i t_i W_i=I_r}.

After removing zero rows, P is compact: its trace equation bounds every t_i by r/tr(W_i). Let d=dim_R span{W_i}. Hermitian real-linearly independent matrices are also complex-linearly independent, so their complex span has dimension d.

Choose a fixed matrix P_0 in the complex affine span of the P_i and let q=dim_C aff{P_i}<=3. The frame constraint makes P_0 tensor I_r constant; the variable part of N(t) uses at most qd complex coordinates. The determinant support objective is the real part of a holomorphic polynomial in those coordinates. Section 8 gives a maximizer with at most

    (q+1)d <=4d

labels. Rescale the retained frame rows by sqrt(t_i). The normalized determinant support does not decrease; every reduced normalized permutation vertex extends to an original vertex by fixing the deleted labels. Therefore a strict counterexample descends to the retained labels.

The universal consequences are at most 4r^2 labels for complex frame rows and at most 2r(r+1) for real frame rows. For a rank-two update these are 16 and 12. If the idempotents have complex affine span at most two or one, the bounds improve to 3d or 2d, respectively.

This scalar reduction does not preserve the entire V-dependent trajectory. The older 7d positive-deletion reduction preserves N exactly and hence preserves that whole trajectory. The two statements have different conclusions and neither should be substituted silently for the other.

## 10. Normal completion audit

Let E=X+iY be an arbitrary complex symmetric 3-by-3 matrix, with X,Y real symmetric. Write [X,Y]=[j]_cross, where [j]_cross acts by cross product with j.

If j=0, E is normal and may be padded by any scalar. If j is nonzero, choose real a,b in j-perp with equal norm, orthogonal to each other, and a cross b=j. Rotating their common oriented orthonormal frame changes the scalar

    j^T(Xb-Ya)

as A cos(theta)+B sin(theta). It therefore has a zero. For such a choice, Xb-Ya lies in span(a,b). Choose unique real c,d satisfying

    Xb-Ya-cb+da=0.

Then the real symmetric matrices

    Xtilde=[[c,a^T],[a,X]],  Ytilde=[[d,b^T],[b,Y]]

commute: their bottom-right commutator is [X,Y]+ab^T-ba^T=0 and the off-block commutator is precisely the displayed equation. Thus Xtilde+iYtilde is a normal complex symmetric 4-by-4 completion of E. Its off-diagonal vector u=a+ib satisfies u^T u=0.

This proof is complete. It says that normal-completion existence imposes no restriction on an arbitrary complex symmetric 3-by-3 compression. It supplies no comparison between the eigenvalue budgets of two different normal completions. Such a comparison would be a separate theorem.


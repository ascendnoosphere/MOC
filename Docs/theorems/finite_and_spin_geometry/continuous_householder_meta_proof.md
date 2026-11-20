# A complete scalar-versus-common-law meta-proof for rank-one unitary updates

This note proves MOC for every relative unitary U=I+(e^{iθ}-1)vv* in every dimension. It also characterizes exactly when this unitary has one probability law reproducing all squared minors. The scalar Householder result and the four-versus-five common-law boundary are established territory: Drury's 1999 paper, *OMC for Householder reflections*, reports those results. This note is an independent explicit derivation, not a historical novelty claim.

Primary publisher record: https://www.sciencedirect.com/science/article/pii/S0024379599001731 . Its abstract states Householder MOC and failure of the Merikoski–Virtanen strengthening in dimension five. The 2025 paper https://www.mdpi.com/2227-7390/13/5/711 explicitly recalls Drury's four-dimensional result. The full 1999 text was not available through the current reader, so no claim about its proof method is made.

## 1. Exact rank-one formulas

Put p_i=|v_i|², sum_i p_i=1, and s=sin²(θ/2). Write M(U) for the vector of all squared minor moduli, M_pi for the corresponding permutation profile. Then

\[
\boxed{M(U)=(1-4s\sum_{i<j}p_ip_j)M_{id}
+4s\sum_{i<j}p_ip_jM_{(ij)}.}
\tag{1}
\]

This is a signed identity; its identity coefficient can be negative. For a principal minor indexed by I, det U[I,I]=1+(e^{iθ}-1)p_I, so its squared modulus is 1-4s p_I(1-p_I). If I,J differ by one label, say i and j, the minor has squared modulus 4s p_ip_j. If they differ by two or more labels, the relevant off-diagonal update has rank one and the minor vanishes. These are exactly the entries of the right side of (1).

For the scalar determinant, put m_i=a_i+b_i, z_id=product m_i and P_i as in the finite-witness note. The two by two matrix N(p)=sum_i p_iP_i has trace one. The compression identity gives

\[
\boxed{d(U)/z_{id}=1-4s\det N(p).}
\tag{2}
\]

Indeed, with z=e^{iθ}, det(I+(z-1)N)=z+(z-1)²detN; divide by z. Formula (2) extends through zero m_i after clearing denominators.

## 2. All common laws are triangle packings

For any three distinct labels, the following exact profile relation holds:

\[
M_{(ij)}+M_{(ik)}+M_{(jk)}-M_{id}
=M_{(ijk)}+M_{(ikj)}.
\tag{3}
\]

On the affected three labels, this is the singleton identity and its complement identity; it therefore holds for every minor size, including when additional labels are fixed.

Conversely, the zero disjoint two-minors of U force every permutation in a positive common law to be the identity, a single transposition, or a single three-cycle. A cycle of length at least four has two edges with four distinct endpoints, as do two disjoint nontrivial cycles. Such edges map a two-element set to a disjoint two-element set, which would give positive mass to a zero minor. Every other permutation has at most one nontrivial cycle, of length two or three.

The profile M(U) is symmetric under transposition of its row and column subset indices. Thus any candidate law may be averaged with its inverse law, giving equal weights to the two orientations of each three-cycle.

Set w_ij=4s p_ip_j. Let t_ijk be the common weight assigned to each orientation of the three-cycle on {i,j,k}. The off-diagonal singleton entries force

\[
u_{ij}=w_{ij}-\sum_{k\ne i,j}t_{ijk}\ge0,
\]

where u_ij is the transposition weight. Total probability then forces the identity weight to be

\[
u_{id}=1-\sum_{i<j}w_{ij}+\sum_{i<j<k}t_{ijk}.
\]

Relations (1) and (3) show that these conditions are sufficient for all minors, not only the singletons. Consequently:

\[
\boxed{M(U)\text{ has a common permutation law}\iff
\max\left\{\sum_{i<j<k}t_{ijk}:t\ge0,
\ \sum_{k\ne i,j}t_{ijk}\le w_{ij}\right\}
\ge\sum_{i<j}w_{ij}-1.}
\tag{4}
\]

This is an exact fractional triangle-packing characterization in every dimension.

## 3. The four-label packing closes by seven elementary squares

It suffices first to take θ=π, so s=1. Put

\[
\delta=4\sum_{i<j}p_ip_j-1=1-2\sum_i p_i².
\]

If delta≤0, (1) is already positive. Otherwise the packing in (4) must have mass at least delta.

For four labels, index a triangle by its omitted vertex. The packing constraints become t_i+t_j≤c_ij, where c_ij=4p_kp_l for the complementary pair {k,l}. The dual is a fractional edge cover of K4: y_ij≥0 and sum_{j≠i}y_ij≥1, minimizing sum c_ij y_ij.

Its extreme minimal covers are the three perfect matchings and the four three-edge stars. Here is a short justification. At an extreme point, a connected component of the graph of positive edges is a star with unit edge weights, or an odd cycle with weights one half. A component with a cycle must have as many active vertex equations as edges; this forces a single odd cycle, and any tree attached to it would have a leaf edge of weight one forcing another positive edge to vanish. A tree component can have at most one slack vertex; leaf elimination then makes it a star. Four covered vertices cannot contain a separate odd cycle, so only the seven stated covers remain.

For a matching, its cost minus delta is

\[
4(p_ip_j+p_kp_l)-\delta
=\{2(p_i+p_j)-1\}²\ge0.
\]

For a star in the dual, the complementary cost is 4 times the sum of pair products among three p's. Its cost minus delta is

\[
4\sum_{j<k:\,j,k\ne i}p_jp_k-\delta
=(1-2p_i)²\ge0.
\]

Duality gives a triangle packing of mass at least delta. Scale it down to total delta if necessary. Relation (3) absorbs the entire negative identity coefficient, leaving nonnegative transposition and three-cycle coefficients.

This proves a common law for every four-dimensional Householder reflection. Padding smaller dimensions by zero coordinates proves the same for n≤4. Formula (1) is affine in s, so M(U_θ)=(1-s)M_id+sM(U_π), proving the whole phase-update family.

## 4. A sharp simple obstruction from five labels onward

Take p_i=1/n and θ=π. A positive common law could move at most three labels in every supported permutation. But its singleton entries require the expected number of moved labels to be

\[
\sum_i(1-|U_{ii}|²)=4-4/n.
\]

This exceeds three exactly when n≥5. Thus the common law fails for every uniform Householder reflection of dimension at least five.

For a general rank-one phase update, the same argument gives the necessary inequality 4s(1-sum p_i²)≤3. No sufficiency conclusion is asserted from this inequality alone.

## 5. A quadratic support lemma

Let q be a real quadratic function on a simplex and suppose the negative index of its quadratic form is at most k. Then q has a maximizing point with support at most k+1.

Choose a maximizer of minimum support m. On the tangent space of its active face, of dimension m-1, the first derivative vanishes and the quadratic form is negative semidefinite. If m-1>k, this restriction has a nonzero null vector. Along that tangent line both its linear and quadratic variations vanish identically, so q is constant until the simplex boundary is reached. That deletes a support coordinate, contradicting minimality.

The quadratic hypothesis is essential: a vanishing Hessian direction of a quartic need not be a constant direction.

## 6. Complete all-dimensional scalar proof

Fix arbitrary spectra and support direction eta, initially with every m_i nonzero. Write

\[
P_i=\tfrac12(I+\nu_i\cdot\sigma),\qquad
\nu_i\cdot\nu_i=1,qquad \nu_i\in\mathbb C³,
\]

with the complex bilinear dot product. Since N(p) has trace one,

\[
\det N(p)=\tfrac14\{1-(\sum_i p_i\nu_i)\cdot(\sum_i p_i\nu_i)\}.
\]

Put zeta=eta z_id. The scalar support objective in (2) is

\[
\boxed{f(p)=(1-s)\operatorname{Re}\zeta
+s\operatorname{Re}\{\zeta(\sum_i p_i\nu_i)\cdot(\sum_i p_i\nu_i)\}.}
\tag{5}
\]

For zeta≠0, the real quadratic form Re(zeta nu·nu) on C³≅R⁶ has signature (3,3): multiplying nu by a complex square root of zeta reduces it to sum x_j²-sum y_j². Its pullback to the p variables therefore has negative index at most three.

The preceding lemma supplies a maximizing p* with at most four nonzero entries. Let S be those labels. The corresponding unitary is identity off S. Its determinant is the product of the untouched m_i times a determinant of dimension at most four. Apply the positive common law proved in Section3 on S, with support direction eta times that external product. Each resulting matching is a permutation of the full label set fixing its complement. Therefore

\[
f(p)\le f(p^*)\le\max_{\pi\in S_n}\operatorname{Re}(\eta z_\pi).
\]

This holds for every support direction eta, proving MOC for every rank-one phase update in every dimension. Cases eta=0 or s=0 are immediate, and vanishing m_i follow by continuity.

The scalar argument does not require a common law. The maximizing four-label face depends on the actual complex spectra and the chosen support direction. It preserves the scalar bound, not a single spectrum-independent coefficient distribution.

## What this does and does not extend

The general rank-r update has a determinant of degree at most 2r in its frame weights. For r=1, the Pauli quadratic has a controlled negative index and null Hessian directions are exactly flat, yielding the four-label reduction. For r=2, the determinant is quartic. The rank-two fourth-order example in `continuous_pair_fibers.md` shows that Hessian flatness does not imply actual flatness even on valid spectral data. A proof for general r therefore needs an additional mechanism controlling those higher-order directions; the scalar face reduction above alone does not establish unrestricted MOC.

# Spectral rigidity at the reflection from the real two-plane obstruction

Let \(F(U)=\Re\{\eta\det(D_a+UD_bU^*)\}\) for finite complex spectra of order four. Suppose \(h=F(I)=\max_\pi F(P_\pi)\), and put \(g(U)=h-F(U)\). Consider the Hermitian rank-two reflection

\[
R=\frac13\begin{pmatrix}
1&-2&0&2\\
-2&-1&2&0\\
0&2&1&2\\
2&0&2&-1
\end{pmatrix}.
\]

**Theorem.** If \(g(R)=0\), then there are nonnegative weights \(w_1,\ldots,w_4\), at most two nonzero, such that

\[
g(U)=\sum_{i=1}^4w_i|U_{i,\pi_0(i)}|^2
\quad\text{for every }U\in U(4),\qquad
\pi_0=(13)(24).
\]

In particular the full scalar support inequality holds for these spectral data and this support direction, on every unitary, and the cubic covector of the two-plane action at this reflection vanishes.

## Proof

Every unitary squared-minor profile belongs to the affine span of permutation profiles, by the determinant expansion and complementary-minor identity. Thus a scalar cost is identified by its values on the twenty-four permutation profiles.

The complete facet description of the order-four common-minor permutation polytope is established in COMMON_MINOR_POLYTOPE.md. Because \(g\) is nonnegative at every permutation and vanishes at identity, its restriction to that affine span is a nonnegative linear combination of the facets active at identity. This is the finite-dimensional normal-cone form of the polytope's complete facet description.

Every active facet has nonnegative value at \(R\), as follows either from the transpose theorem or by the exact enumeration here. There are twenty-six active mixed facets. Exactly two of them have value zero at this \(R\); all the others are strictly positive. Among the basic squared-minor facets, the only zeros are

\[
\rho_{1,3},\quad \rho_{2,4},\quad \rho_{3,1},\quad \rho_{4,2}.
\]

Since \(g(R)=0\), its nonnegative facet decomposition can use only these six zero-slack generators. The exact certificate checks that their common-zero permutation vertices are precisely

\[
\{\pi\in S_4:\pi(i)\ne\pi_0(i)\text{ for all }i\}.
\]

There are nine such vertices. It also verifies that the six generators span a five-dimensional space, matching the complete derangement-zero cost space.

It follows that all nine of these permutations attain the support height \(h\). Relabel columns by \(\pi_0\). They become the ordinary derangements, and the actual spectral class is preserved under this relabeling. The theorem in dual_derangement_secant_rigidity.md now gives

\[
g(U)=\sum_iw_i|U_{i,\pi_0(i)}|^2,\qquad
w_i\ge0,\quad |\{i:w_i>0\}|\le2.
\]

This proves the stated global support inequality.

At the displayed reflection, every selected entry \(R_{i,\pi_0(i)}\) is zero. The derivative of its squared modulus is consequently zero in every matrix direction. Thus the support has zero derivative at this reflection on the entire unitary group. The exact endpoint-gradient relation from continuous_full_rank_two_geometry.md identifies this derivative, on the chosen two-plane, with the adjugate transform of the cubic covector. That transform is invertible on two-by-two Hermitian coordinates, so the cubic covector vanishes.

## Why this matters and what it does not prove

The nonspectral facet in continuous_final_obstructions.md touches both identity and this reflection, yet escapes along their real two-plane circle. The theorem proves that this precise zero-gap escape cannot survive the actual complex spectral restrictions. It closes a contact case by combining the continuous tangent cone with the categorical spectral equations.

Only this reflection and its symmetry copies are classified here. Arbitrary reflection strata, positive gaps, and the unrestricted complex conjecture are not settled.

The standard-library exact certificate is code/theorems/finite_and_spin_geometry/root_zero_gap_reflection_face.py with its JSON companion. It checks the reflection identity, every active mixed-facet slack, all basic zeros, the nine common-zero permutations, and the rank-five span. Its mathematical inputs are the already audited full facet theorem and derangement rigidity theorem.

# The four-dimensional common-minor polytope

## Exact result and scope

Let \(R(U)_{I,J}=|\det U[I,J]|^2\), where \(|I|=|J|\), and let
\(\mathcal P_4\) be the convex hull of the 24 profiles of permutation matrices.
The affine hull has dimension 13. Its facets consist of:

* 16 inequalities \(R_{i,j}\geq0\) at level one;
* 18 distinct inequalities \(R_{I,J}\geq0\) at level two, after complementary pairs are identified;
* 48 relabelings, under independent permutations of rows and columns, of
  \[
  R_{3,3}+R_{2,4}+R_{12,13}-R_{13,23}\geq0.
  \tag{1}
  \]

The notation in (1) uses one-based matrix labels, not bit masks. All actual
unitary profiles lie in this affine hull and have nonnegative entries.
Consequently an actual profile has a single positive permutation law for
all of its graded minors if and only if it satisfies the 48 inequalities
in the last family.

This is a statement about the stronger **common permutation law**. A
violation of one of these inequalities is not a counterexample to scalar
Marcus–de Oliveira. No claim of historical novelty for this polytope
description is made here.

## Exact certificate

`code/theorems/finite_and_spin_geometry/root_common_hull_exact.py` constructs all 24 vertices as integer vectors.
The 13 independent coordinates are the bit-mask pairs

\[
(3,3),(5,5),(6,6),(2,2),(1,1),(4,4),(8,8),
(8,4),(14,13),(4,1),(13,7),(6,9),(3,10).
\]

Together with a leading constant coordinate, their rank is exactly 14.
For each candidate facet, Fraction row reduction produces its primitive
integer normal. The program then checks all 24 inequalities and that the
active augmented vertices have rank 13. It also computes the full
\(S_4\times S_4\) orbit of (1), verifies that its 48 active vertex sets are
distinct, and matches every nontrivial candidate facet with that orbit.
The verifier computes the complete integer normals and vertex values.

The initial candidates came from floating-point convex hull enumeration.
Their validity alone would not establish completeness. The separate
`code/theorems/finite_and_spin_geometry/root_common_hull_boundary.py` supplies a completeness certificate with
integer arithmetic:

1. Its 9,050 abstract boundary simplices form a connected, orientable
   complex in which every codimension-one simplex has exactly two
   incident top simplices.
2. The orientations propagated through this graph cancel the formal
   boundary exactly.
3. Every simplex maps affinely into one of the 82 certified supporting
   faces of the actual convex hull.
4. Bareiss determinants with integer entries check the geometric
   orientations against the interior point equal to the vertex average.
   There are 6,846 nondegenerate simplices, all with the same outward
   orientation. The remaining 2,204 have zero determinant.

Here is why those facts establish completeness. Mapping the oriented
abstract simplices into the convex boundary produces a closed
top-dimensional geometric chain. Degenerate simplices contribute zero
top-dimensional chain. Every nonzero contribution has positive outward
orientation, so the chain is nonzero. On the connected, oriented boundary
of a full-dimensional convex polytope, the multiplicity of a closed
top-dimensional chain is constant away from its lower-dimensional faces.
Thus its support is the whole boundary. As every simplex lies in a listed
facet, an unlisted facet is impossible. Equivalently, this is the standard
degree argument for a closed oriented chain mapped to a sphere: its
positive local degree is constant and cannot vanish on a missing open
facet.

The boundary verifier checks the geometric determinants and simplex incidences, retaining degenerate simplices in the formal boundary cancellation.

## A concrete remaining structural bridge

For a real orthogonal \(O\), consider the following disjunction:

\[
R(O)\in\mathcal P_4
\quad\text{or}\quad
\exists\text{ monomial unitary }M:\operatorname{rank}(O-M)\leq2.
\tag{2}
\]

This disjunction is **unproved**; the second alternative is not asserted for every orthogonal matrix.
The facet classification reduces the proposed implication to a representative facet, using row and column relabeling.

For a fixed generic completion chart, four real coefficients
\(q_0,q_1,q_2,q_{12}\) give the discriminant

\[
\Delta=4(q_0q_1-q_2q_{12})^2
 -(q_0^2+q_1^2-q_2^2-q_{12}^2)^2.
\]

It factors as minus the product of four signed sums of the \(q\)'s. Thus
the proposed implication has an entirely explicit semialgebraic form on
\(SO(4)\). Exceptional charts and vanishing minors need separate treatment
or a justified closure argument. Even a proof of (2) would still require
a scalar MOC theorem for the resulting rank-two unitary perturbations.

## Verification commands

```bash
python3 code/theorems/finite_and_spin_geometry/root_common_hull_exact.py
python3 code/theorems/finite_and_spin_geometry/root_common_hull_boundary.py
```

These exact checks certify the finite polyhedral theorem, not the unproved scalar implications above.

# What the independently marked crossed cuts do and do not prove

## Deterministic classification (paper; Lean verifies the local steps)

A deterministic doubly stochastic degree-k table is a bijection F of
k-subsets. For every k-set J, incoming column j outside J, and row i
inside F(J), a crossed transport must have an outgoing edge. The only
possible destination column sets replace one r in J by j. Their image
must retain every row of F(J) except i and must omit i. Each r can
serve at most one i. Both choices range over k labels. Consequently
each r is used and the removals on the output side are distinct.
`crossedLocal_of_transport` and `exists_crossed_removal_bijection`
verify these statements without enumeration.

In particular F preserves Johnson adjacency. Since F is a bijection
and the edge set is finite, its inverse preserves adjacency too.
The automorphism theorem for Johnson graphs says F is induced by a
permutation of the ground set, possibly followed by complementation
when N=2k. See G. A. Jones, *Automorphisms and regular embeddings of
merged Johnson graphs*, Theorem 2,
[DOI 10.1016/j.ejc.2004.01.012](https://doi.org/10.1016/j.ejc.2004.01.012).
That external classification is not imported into Lean here. In the
middle layer, a fixed incoming j for a complement-twisted F always
removes the *same* output row, the image of j, independently of r.
For k≥2 this contradicts the checked removed-row bijection.
The boundary k=1,N−1 layers are already point- or complement-point
assignments, and k=0,N are trivial.

Independent marking is essential. When N=2k the plain complement
table does pass every *aligned* crossing with row mark equal to column
mark j. Couple J avoiding j to J−r+j for every r in J, using weight 1/k.
Each destination has k possible sources, by the omitted spectator
outside its target set. Both side inclusions therefore hold for this
non-permutation assignment. The aligned example is a paper argument.

## Actual fractional table in every N>4

The flat Householder matrix is U=I−(2/N)11*. Its two-by-two minors
with disjoint row and column sets vanish, since their entries are
all the same. A positive law with these pair marginals could only
use permutations with at most three moved labels. Four moved labels
force a pair disjoint from its image: pick one moved point and then
another outside that point and its predecessor and successor.

But the pair marginals force every singleton marginal. The incidence
identity is
`sum_{l != j} 1[i in sigma({j,l})] = 1+(N−2) 1[sigma(j)=i]`.
The expected number of moved labels must therefore equal
N times (1−(1−2/N)^2), which is 4−4/N>3. The contradiction is checked
in `flatReflectionUniform_no_positive_pair_law`. The earlier order-five
symbolic obstruction uses the same structural mechanism. Drury's
Householder method: [DOI 10.1016/S0024-3795(99)00173-1](https://doi.org/10.1016/S0024-3795(99)00173-1).

Reindexing rows and columns independently gives every crossed transport
for this actual unitary via `independentCrossedTests_of_unitary`.
Consequently the crossed-cut polytope for the pair table has all
integral points induced by permutations but is larger than their
convex hull. This is not a spectral counterexample.

## High-rank synthetic gap (the rank consequence is a paper proof)

For a permutation sigma let m(sigma) count moved labels and let
d(sigma) count doubletons disjoint from their images. Use the explicit
gap g(sigma)=3−m(sigma)+(N−3)d(sigma). This is nonnegative: m≤3 is
immediate; otherwise d≥1 and m≤N. On the flat Householder table, its
signed expectation is 3−(4−4/N)=4/N−1<0. The disjoint-pair penalties
contribute zero. [UniformCrossingObstruction.lean](MOC/UniformCrossingObstruction.lean) checks nonnegativity, the signed expectation and nonspectral realizability. This is a linear objective on pair incidences since
singleton incidences are determined by pairs and normalization.

Every 3-cycle is a contact for this synthetic gap. It moves exactly
three labels and has no doubleton disjoint from its image. Fix one
anchor a and use the cycles a→i→j→a for all ordered pairs i≠j away
from the anchor. For such a cycle, the singleton marker for i→j
is one, and its value is zero on every other cycle from this family.
Taking differences from one chosen pivot gives
(N−1)(N−2)−1 independent marker differences. By the checked exact
marker equivalence, the rank of the corresponding matching-product
difference functions has the same lower bound. In particular this
synthetic contact geometry exceeds the project's terminal 2N−3
rank threshold when N>4.

The gap is **not** a spectral objective: if it were H−Re(eta P_sigma),
its nonnegativity would bound the matching support by H, and the
negative signed expectation would violate MOC for this Householder
matrix. That matrix is already proved to satisfy MOC for every pair
of spectra by the Householder theorem. Thus contact rank and all
crossed constraints do not suffice for *arbitrary* nonnegative
objectives. Spectral realizability is necessary for such a proof.

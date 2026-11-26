# Projection leaf deletion

The Marcus–de Oliveira conjecture compares the determinant of a sum
of two normal matrices with the products of sums of matched
eigenvalues. To reduce this comparison to smaller matrices, delete a
coordinate on which one matrix acts by a scalar. The other matrix
can mix that coordinate with the remaining coordinates.
[Conjecture and proof tree](../README.md)

## Determinant reduction

Take any finite set of remaining coordinates. Let the first matrix
have the form $sI+kP$. Here $I$ is the identity matrix, $s$ and $k$
are arbitrary complex scalars, and $P$ is an orthogonal projection.
Thus $P^2=P$ and $P^*=P$, where the star denotes conjugate transpose.
Write

$$
P=\begin{pmatrix}p&q^*\\q&J\end{pmatrix},
qquad
M=sI+kP+\begin{pmatrix}r&0\\0&B\end{pmatrix}.
$$

The deleted coordinate is first. Its diagonal entry $p$ in $P$ is
real. The column $q$ gives its entries in the remaining coordinates,
and $J$ is the compression of $P$ to those coordinates. The opposite
scalar is $r\in\mathbb C$. The remaining square matrix $B$ can be any
complex matrix.

For $p>0$ define $P_1=J-qq^*/p$. For $p<1$ define
$P_0=J+qq^*/(1-p)$. A branch with weight zero can use $J$. The
determinant satisfies

$$
\det M
=p(s+k+r)\det(sI+kP_1+B)
+(1-p)(s+r)\det(sI+kP_0+B).
$$

The two scalar factors are the eigenvalue sums for the deleted
coordinate. The coefficients $p$ and $1-p$ are nonnegative and have
sum one. They depend only on $P$. The positive-weight branches
retain orthogonal projections.
Their ranks are the rank of $P$ minus one for $P_1$, and the rank of
$P$ for $P_0$. At $p=0$ and $p=1$, the column $q$ is zero.
[Determinant reduction](../Lean/MOC/ProjectionLeafPivot.lean#L110) ·
[Weight bounds](../Lean/MOC/ProjectionConditioning.lean#L68) ·
[Selection projection](../Lean/MOC/ProjectionConditioning.lean#L154) ·
[Rejection projection](../Lean/MOC/ProjectionConditioning.lean#L176) ·
[Selection rank](../Lean/MOC/ProjectionConditioning.lean#L266) ·
[Rejection rank](../Lean/MOC/ProjectionConditioning.lean#L280) ·
[Endpoints](../Lean/MOC/ProjectionConditioning.lean#L81)

```mermaid
flowchart TD
    Input["Orthogonal projection P and scalar block r on the deleted coordinate"]
    Input --> Weights["Proved: 0 ≤ p ≤ 1"]
    Weights --> Select["If p > 0: assign s+k, use P₁, and give weight p"]
    Weights --> Reject["If p < 1: assign s, use P₀, and give weight 1−p"]
    Select --> Sum["Combine both terms, with zero weight at an absent branch"]
    Reject --> Sum
    Sum --> Equality["Proved: the sum equals det M"]
```

The determinant proof uses addition in the first row and the
affine dependence of a determinant on a rank-one update. It permits
singular matrices in every block.
[Bordered determinant formula](../Lean/MOC/ProjectionLeafPivot.lean#L45) ·
[Rank-one update](../Lean/MOC/Pencil.lean#L15)

The correction can change the entry with row $i$ and column $j$ only
when both entries of $q$ at $i$ and $j$ are nonzero. Thus a partition
block that contains the deleted coordinate can keep its remaining
coordinates as one block after the update.
[Entry formula](../Lean/MOC/ProjectionConditioning.lean#L199)

The two projection updates have a probability interpretation. On a
finite set of coordinates, a determinantal probability measure for
an orthogonal projection has one conditional subspace for inclusion
of a coordinate and one for exclusion. The matrix proof here uses
the projection equations directly.
[Lyons, Proposition 6.3](https://rdlyons.pages.iu.edu/pdf/bases.pdf#page=18)

## Two overlapping projection blocks

Partition the coordinate set into $X$, $H$, and $Y$. The first
summand has a two-level normal block on $X\cup H$ and is diagonal
on $Y$. The second summand is diagonal on $X$ and has a two-level
normal block on $H\cup Y$. Each two-level block has the form $sI+kP$,
with its own orthogonal projection $P$ and complex scalars $s$ and $k$.
The levels of that block are $s$ and $s+k$. All three coordinate sets
can have any dimension.

Fix the two projections. Use a high-level label once per dimension
of the range of its projection. Use a low-level label once per
remaining dimension of its block. Assign a private label to each
diagonal coordinate outside the block. One probability law on
permutations represents the determinant of the sum for every choice
of the levels and the private values. This gives inclusion in the
convex hull for any ordering of the eigenvalues with multiplicity.
[Spectral labels](../Lean/MOC/ProjectionBlockSpectralLabels.lean#L39) ·
[Common law](../Lean/MOC/OverlappingProjectionBlocks.lean#L636) ·
[Determinant inclusion](../Lean/MOC/OverlappingProjectionBlocks.lean#L671)

```mermaid
flowchart TD
    Input["Two overlapping two-level blocks and disjoint private coordinate sets"]
    Input --> Private["A private coordinate exists"]
    Input --> Shared["No private coordinate remains"]
    Private --> Condition["Use each positive-weight projection branch"]
    Condition --> Delete["Delete the coordinate and its two matched labels"]
    Delete --> Combine["Extend each child permutation and combine the laws"]
    Shared --> Base["Use the common law for a two-valued spectrum"]
    Combine --> Law["Proved common law for all levels and private values"]
    Base --> Law
```

If a private coordinate exists, apply projection deletion to the
other summand. The update preserves zero rows at its private
coordinates. The child traces supply the new multiplicities. A
positive-weight branch has a spectral label for its selected level.
Add the two matched labels to each child permutation. The induction
decreases the order at each deletion. If there is no private
coordinate, both spectra have at most two values. The law for one
two-valued spectrum gives the base.
[Determinant step](../Lean/MOC/OverlappingProjectionBlocks.lean#L446) ·
[Induction](../Lean/MOC/OverlappingProjectionBlocks.lean#L608) ·
[Base common law](../Lean/MOC/TwoValues.lean#L285)

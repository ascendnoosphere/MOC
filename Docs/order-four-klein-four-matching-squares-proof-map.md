# Normal Klein-four matching squares

[Proof map index](README.md) · [Order-four proof map](order-four-proof-map.md) · [Conjecture](../README.md)

For two complex spectra of order four, a support cost subtracts
the real projection of each matching product from a common upper
bound. An index is a contact if its cost is zero. The normal
Klein-four contact set contains the identity and the three double
transpositions. If all four indices are contacts, the cost is a
finite sum of squares of real functions from the 14-dimensional
matching space. This includes repeated spectra and additional
contacts. [Spectral theorem statement](../Lean/MOC/FourKleinSpectralSquares.lean#L259)

```mermaid
flowchart TD
    Contacts["Actual support cost with normal Klein-four contacts"]
    Chart["Ten-coordinate matching chart"]
    Ordinary["Both absolute-sum bounds hold"]
    Mixed["One absolute-sum bound fails"]
    Source["Actual inverse quadratic has four complex squares"]
    Prism["No strictly negative five-dimensional prism compression"]
    Threshold["Mixed budget at or below the strong threshold"]
    Squares["Real matching sum of squares"]
    Contacts --> Chart
    Contacts --> Source
    Chart --> Ordinary
    Chart --> Mixed
    Source --> Prism
    Ordinary --> Squares
    Mixed --> Threshold
    Prism --> Threshold
    Threshold --> Squares
```

The ten coordinates give three rectangle groups and two cycle groups.
Each rectangle has values $\beta_i\pm p_i\pm q_i$, so nonnegativity
gives $\beta_i\ge |p_i|+|q_i|$. The two cycle baselines add to
$\sum_i\beta_i$. The ordinary certificate allocates this total
between the two groups if each baseline bounds the sum of absolute
sign coordinates in that group.
[Chart](../Lean/MOC/FourKleinMatchingChart.lean#L74) · [Ordinary certificate](../Lean/MOC/FourKleinMatchingSquares.lean#L79)

The spectral source gives a quadratic form in nine real matrix entries.
The signed matching polynomial equals the prism in the cofactor entries.
For an invertible matrix, the determinant factor converts these
cofactors to inverse coordinates. A shift by a real scalar matrix
extends the identity across singular coordinates. In the actual
spectral form, the real part of four complex linear squares represents
the prism. Every linear map from a real space of dimension five has a
nonzero vector that sets the four imaginary parts to zero.
[Cofactors](../Lean/MOC/FourKleinInversePencil.lean#L130) · [Extension](../Lean/MOC/FourKleinSpectralSquares.lean#L181) · [Four-square obstruction](../Lean/MOC/FourKleinNegativeCompression.lean#L135)

When one absolute-sum bound fails, coordinate changes put the cost in
one mixed cap. Write its critical budgets as $a^2,b^2,c^2$ with
$a\ge b,c\ge0$, and let $t>0$ be its mixed budget. If
$t>a(b+c)-bc$, an explicit plane has a strictly negative form.
Completion of squares joins this plane to the three diagonal
directions of the prism. The argument includes the case $b=c=0$.
[Negative plane](../Lean/MOC/FourKleinNegativeCompression.lean#L52) · [Five-dimensional compression](../Lean/MOC/FourKleinPrism.lean#L61)

The absence of this compression gives $t\le a(b+c)-bc$. A convex
combination of a diagonal Gram matrix and the rank-one Gram matrix of
$(a,-b,-c)$ gives the mixed certificate. The formula allows equality at
the threshold. [Mixed certificate](../Lean/MOC/FourKleinMatchingSquares.lean#L152) · [All chart cases](../Lean/MOC/FourKleinChartSymmetry.lean#L339)

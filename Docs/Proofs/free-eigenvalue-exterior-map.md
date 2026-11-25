# One free eigenvalue and exterior shifts

[Conjecture](../../README.md#proof-tree) · [All-order routes](all-order-proof-maps.md) · [Order five](order-five-proof-maps.md)

For two normal matrices, the Marcus–de Oliveira conjecture places the
determinant of their sum in the real convex hull of all products
obtained by matching their eigenvalues. The real coefficients in a
convex combination are nonnegative and sum to one.

The research note *An arbitrary fifth eigenvalue* gives two separate
targets. One target fixes nine eigenvalues in order five and leaves the
last one free. The other adds one scalar to an arbitrary diagonal
partner of a Hermitian matrix.

## One law for a free eigenvalue

~~~mermaid
flowchart BT
    C["One law for every free entry"]
    Y["Joint hull of two complex coefficients"]
    S["One real pivot gives positive coefficient costs"]
    I["Interlacing injection law"]
    D["Exact facet and neighborhood certificates"]
    C <-->|iff| Y
    I --> S
    S --> D
    D -.->|unreplayed certificate| Y
~~~

Let the first list be $h=(-2,-1,0,1,2)$, and let the first four
partner entries be $(i,2+3i,3-i,-2+2i)$. A determinant with the fifth
partner entry $w$ is affine in $w$. One probability law for every $w$
is equivalent to a convex representation of the pair of complex
coefficients. The existing Lean reduction gives at most five
assignments when the joint hull test holds.
[One-entry equivalence](../../Lean/MOC/SpectralMinorDecomposition.lean#L139)

For two real lists of lengths $n+1$ and $n$, suppose each shorter
entry lies between consecutive entries of the longer list. The
new proof gives a convex combination of injection products in the
space of functions of the entire complex partner list. Thus the
injection weights are fixed before any partner entry is chosen.
The result includes equal consecutive endpoints. This is the
interlacing step used to lift a lower-order law at a real pivot.
[Uniform interlacing law](../../Lean/MOC/InterlacingCommonLaw.lean#L108) · [Scalar real-pivot case](../../Lean/MOC/HermitianByNormalFourProof.lean#L100)

The joint hull claim for the displayed center still needs the exact
facet replay. The note gives the size of its certificate as 201
facets, 404 ridges, and 2,663 positive-cost summands. The radius
$10^{-2000}$ also needs the reversible-direction and coordinate
certificate for the moving spectra. The source for these two
finite certificates was unavailable in the workspace.

## Exterior shifts

~~~mermaid
flowchart BT
    R["Euclidean inverse and remainder bounds"]
    C["Stationarity for a projected diagonal"]
    K["Operator-norm block compression and block inverse"]
    B["A support maximum preserves every separated partition"]
    G["Collinear block partition for each direction"]
    H["Determinant hull within each collinear block"]
    P["Exterior determinant inclusion"]
    R --> B
    C --> B
    K --> B
    B --> P
    G -.->|needs Lean proof| P
    H --> P
~~~

Let $Y$ be a complex square matrix. If $\|Y\|<|z|$, where the matrix
norm is the Euclidean operator norm, then $zI+Y$ is invertible. Its
inverse has norm at most $1/(|z|-\|Y\|)$. The remainder
$R(Y)=Y^2(zI+Y)^{-1}$ gives the exact expansion
$z^2(zI+Y)^{-1}=zI-Y+R(Y)$. For $\|Y_1\|,\|Y_2\|\le L<|z|$ and
$d=|z|-L$, its Frobenius variation is bounded by
$(2L/d+L^2/d^2)\|Y_1-Y_2\|_{\mathrm F}$.
[Inverse bound](../../Lean/MOC/HermitianExteriorShift.lean#L76) · [Expansion](../../Lean/MOC/HermitianExteriorShift.lean#L115) · [Remainder norm](../../Lean/MOC/HermitianExteriorShift.lean#L138) · [Frobenius estimate](../../Lean/MOC/HermitianExteriorShift.lean#L300)

At a nonsingular support maximum, let $H$ be the Hermitian summand,
$B$ the partner diagonal, and $Y=H+B$. For direction $\eta$, put
$v=\eta\det(zI+Y)/z^2$. Then $H$ commutes with the real projected
diagonal of $vB$ minus the Hermitian part of $vR(Y)$. The term with
$H$ and the scalar term commute with $H$ and cancel from this
equation. [Stationarity](../../Lean/MOC/HermitianExteriorShift.lean#L169)

For a given partition, let $H_0$ be the part of $H$ inside the blocks
and $F=H-H_0$. Suppose distinct blocks have projected separation
at least $g$. If the perturbation has operator norm at most $K$,
$\|H_0\|\le M$, and its Frobenius variation from a block-diagonal
reference is at most $J\|F\|_{\mathrm F}$, then
$2K+2MJ<g$ forces $F=0$. Keeping only diagonal blocks does not increase
the operator norm. The inverse of an invertible block-diagonal matrix
has the same block partition, so the Hermitian part of the reference
remainder has zero entries between distinct blocks.

Let $\eta\ne 0$ be the support direction and let $H$ maximize its support.
Suppose $\|H\|\le M$, $M+\|B\|\le L$, and $d=|z|-L>0$. If
$2L^2/d+2M(2L/d+L^2/d^2)<g$, then there is a complex number $u$ of
modulus one for which $H$ preserves every partition with separation
at least $g$ in the projection $\mathrm{Re}(ub_i)$. The order-five
scalar inequality at $|z|\ge 123$ is in the source. The full determinant
conclusion still needs a collinear partition for each projection and
an application of the affine-line theorem to its blocks.
[Block compression](../../Lean/MOC/HermitianExteriorShift.lean#L394) · [Support maximum](../../Lean/MOC/HermitianExteriorShift.lean#L608) · [Exact threshold arithmetic](../../Lean/MOC/HermitianExteriorShift.lean#L691) · [Affine-line theorem](../../Lean/MOC/DruryHermitianPencil.lean#L385)

The new Lean source awaits kernel verification.

# One free eigenvalue and exterior shifts

[Proof map index](README.md) · [Conjecture](../README.md#proof-tree) · [All-order routes](all-orders-proof-map.md) · [Order five](order-five-proof-map.md)

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
[One-entry equivalence](../Lean/MOC/SpectralMinorDecomposition.lean#L139)

Suppose the conjecture holds in smaller orders. If the mixer column
for the free eigenvalue meets at most two distinct values in the
other spectrum, the reciprocal compression is normal at each
regular parameter. Continuity covers the exceptional values. One
nonnegative law on at most five permutations then works for every
value of the free eigenvalue. Exact rational checks included singular
and repeated free values. The new Lean source awaits verification.
[Smaller-order reduction](../Lean/MOC/GroupedEigenvalueMoments.lean#L40) · [Common law](../Lean/MOC/GroupedEigenvalueMoments.lean#L88)

For two real lists of lengths $n+1$ and $n$, suppose each shorter
entry lies between consecutive entries of the longer list. The
new proof gives a convex combination of injection products in the
space of functions of the entire complex partner list. Thus the
injection weights are fixed before any partner entry is chosen.
The result includes equal consecutive endpoints. This is the
interlacing step used to lift a lower-order law at a real pivot.
[Uniform interlacing law](../Lean/MOC/InterlacingCommonLaw.lean#L108) · [Scalar real-pivot case](../Lean/MOC/HermitianByNormalFourProof.lean#L100)

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
    T["Positive triangle gap for the partner spectrum"]
    G["Collinear blocks in the projected direction"]
    H["Affine-line determinant hull within each block"]
    A["Join the block hulls at a support maximum"]
    P["Determinant inclusion for each exterior shift"]
    R --> B
    C --> B
    K --> B
    T --> G
    B --> A
    G --> A
    H --> A
    A --> P
~~~

Let $Y$ be a complex square matrix. If $\|Y\|<|z|$, where the matrix
norm is the Euclidean operator norm, then $zI+Y$ is invertible. Its
inverse has norm at most $1/(|z|-\|Y\|)$. The remainder
$R(Y)=Y^2(zI+Y)^{-1}$ gives the exact expansion
$z^2(zI+Y)^{-1}=zI-Y+R(Y)$. For $\|Y_1\|,\|Y_2\|\le L<|z|$ and
$d=|z|-L$, its Frobenius variation is bounded by
$(2L/d+L^2/d^2)\|Y_1-Y_2\|_{\mathrm F}$.
[Inverse bound](../Lean/MOC/HermitianExteriorShift.lean#L81) · [Expansion](../Lean/MOC/HermitianExteriorShift.lean#L120) · [Remainder norm](../Lean/MOC/HermitianExteriorShift.lean#L143) · [Frobenius estimate](../Lean/MOC/HermitianExteriorShift.lean#L305)

At a nonsingular support maximum, let $H$ be the Hermitian summand,
$B$ the partner diagonal, and $Y=H+B$. For direction $\eta$, put
$v=\eta\det(zI+Y)/z^2$. Then $H$ commutes with the real projected
diagonal of $vB$ minus the Hermitian part of $vR(Y)$. The term with
$H$ and the scalar term commute with $H$ and cancel from this
equation. [Stationarity](../Lean/MOC/HermitianExteriorShift.lean#L174)

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
at least $g$ in the projection $\mathrm{Re}(ub_i)$.
[Block compression](../Lean/MOC/HermitianExteriorShift.lean#L399) · [Support maximum](../Lean/MOC/HermitianExteriorShift.lean#L613)

For a noncollinear triangle on partner values $x,y,w$, let $A$ be its
unsigned area. The gap must satisfy $g(|y-x|+|w-x|)\le 2A$ for each
ordered triangle. A positive gap exists for every finite spectrum.
Half a common lower bound on the triangle altitudes is one choice.
Join two labels when their projected values differ by less than $g$.
Each connected group lies on one affine line. Distinct groups have
projected separation at least $g$. This construction also covers
repeated spectral values.
[Positive gap](../Lean/MOC/HermitianExteriorShift.lean#L836) · [Altitude bound](../Lean/MOC/HermitianExteriorShift.lean#L1043) · [Collinear groups](../Lean/MOC/HermitianExteriorShift.lean#L762)

Diagonalize the Hermitian summand within each group. The affine-line
theorem places each block determinant in its matching hull. Products
of the block convex weights give one convex representation of the full
determinant at a support maximum. The directional hull test then gives
the determinant inclusion for every unitary mixer. The exact support
inequality follows if $|z|>2L+8L^2/g$. Consequently, each fixed pair of
spectra where one spectrum is real has an exterior disk bound that
works for every mixer.
[Affine-line theorem](../Lean/MOC/DruryHermitianPencil.lean#L385) · [Exterior inclusion](../Lean/MOC/HermitianExteriorShift.lean#L987) · [Explicit radius](../Lean/MOC/HermitianExteriorShift.lean#L1060) · [Uniform radius](../Lean/MOC/HermitianExteriorShift.lean#L1189)

For the real spectrum $(-2,-1,0,1,2)$ and the partner spectrum
$(0,1,-1,i,-i)$ before the shift, take $M=2$, $L=3$, and $g=1/(2\sqrt2)$.
An exact check covers all ordered triangles. The determinant inclusion
holds for every unitary mixer when $|z|\ge 123$.
[Order-five arithmetic](../Lean/MOC/HermitianExteriorShift.lean#L1090) · [Order-five inclusion](../Lean/MOC/HermitianExteriorShift.lean#L1168)

The new Lean source awaits kernel verification.

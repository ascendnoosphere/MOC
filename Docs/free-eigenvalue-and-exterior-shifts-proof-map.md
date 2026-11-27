# One free eigenvalue and exterior shifts

[Proof map index](README.md) · [Conjecture](../README.md#proof-tree) · [All-order routes](all-orders-proof-map.md) · [Order five](order-five-proof-map.md)

For two normal matrices, the Marcus–de Oliveira conjecture places the
determinant of their sum in the real convex hull of all products
obtained by matching their eigenvalues. The real coefficients in a
convex combination are nonnegative and sum to one.

The one-entry route requires one probability law for every value of
a free eigenvalue. The law may depend on the fixed entries and the
unitary matrix that changes the eigenbasis. The exterior shift route
adds a common scalar to all the entries of one list and gives
determinant inclusion for shifts outside a disk.
[Exact one-entry route at a fixed order](../Lean/MOC/ProofRoutes.lean#L113) · [Exterior radius](../Lean/MOC/HermitianExteriorShift.lean#L1188)

## One law for a free eigenvalue

~~~mermaid
flowchart BT
    C["One law for every free entry and every complex first list"]
    Y["Joint hull of two coefficients for every complex first list"]
    H["Joint hull with a real first list<br/>Open"]
    S["One real pivot gives positive coefficient costs"]
    I["Interlacing injection law"]
    D["Joint hull for every mixer at the specified order-five lists<br/>Open"]
    C <-->|iff| Y
    I --> S
    Y -->|"Restrict the first list to real values"| H
    S -.->|"open comparison for complex free entries"| H
    H -->|"Specialize the lists"| D
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
other spectrum, the reciprocal compression is normal whenever the
free entry is distinct from the other partner entries and cancels no
eigenvalue in the first list. Continuity covers the exceptional
values. One probability law on at most five permutations then works
for every value of the free eigenvalue.
[Smaller-order reduction](../Lean/MOC/GroupedEigenvalueMoments.lean#L40) · [Common law](../Lean/MOC/GroupedEigenvalueMoments.lean#L88)

Let $a$ and $\alpha$ be real lists of lengths $n+1$ and $n$. Suppose
$a_j\le\alpha_j\le a_{j+1}$ for each $j$. For every complex list $b$
of length $n$, the product $\prod_j(\alpha_j+b_j)$ is a convex
combination of the products $\prod_j(a_{f(j)}+b_j)$ over injections
$f$ from the shorter index set to the longer index set. The weights
work for every $b$.
The result includes equal consecutive endpoints. This is the
interlacing step used to lift a lower-order law at a real pivot.
[Uniform interlacing law](../Lean/MOC/InterlacingCommonLaw.lean#L108) · [Scalar real-pivot case](../Lean/MOC/HermitianByNormalFourProof.lean#L104)

If the Hermitian spectrum is simple, the injection law for a principal
compression assigns each omitted eigenvalue the squared modulus of its
component at the deleted coordinate. To get this mass, evaluate the law
with every partner value equal to the negative of the eigenvalue. All
products except the ones that omit this eigenvalue vanish.
[Omission mass](../Lean/MOC/HermitianNormalPencil.lean#L107)

Let $p$ be a real partner position with $b_p$ distinct from all other
partner entries and $a_i+b_p\ne0$ for each Hermitian eigenvalue $a_i$.
Fix a direction. For each $i$, choose an upper bound on matching
projections over permutations that send $p$ to $i$. The smaller-order
Hermitian–normal theorem bounds the determinant projection by the
average of these upper bounds with weights $|U_{ip}|^2$. The result
requires a simple Hermitian spectrum. Lean checks the mass and the
directional bound. The joint coefficient comparison for arbitrary
complex free values remains open.
[Real-pivot bound with prescribed weights](../Lean/MOC/HermitianNormalPencil.lean#L171)

The real-pivot branch has a real first list. Its open joint hull
comparison is a restricted case of the general one-entry route.

When two groups are allowed positive mass, evaluation at the negative
of one Hermitian value leaves only the other group. If both such real
evaluations belong to their prescribed scaled group hulls, the two
group points reproduce the intercept and slope. They then work for
every complex value of the free entry. A separate deletion proves
pointwise inclusion when the free column meets at most two Hermitian
eigenvalues and the smaller-order Hermitian–normal inclusion holds.
[Two real evaluations](../Lean/MOC/HermitianNormalPencil.lean#L309) ·
[Two supported Hermitian values](../Lean/MOC/SpectralSupportDeletion.lean#L252)

The joint hull at the displayed order-five lists for every unitary
mixer is open in Lean. A neighborhood result also needs a bound on
how the joint hull changes when the lists and mixer change.

## Exterior shifts

### Generic assignment sums

The Lean source for the generic and uniform assignment theorems
awaits a build check.

Fix any first list $a$ with pairwise distinct complex entries. In every
finite order $n$, there is an open dense set of partner lists
$b\in\mathbb C^n$ with the following property. For each such $b$ there
is one radius $R(a,b)>0$. For every complex shift $|z|>R(a,b)$ and
every unitary mixer, the conjecture holds for $(a_i+z)_i$ and $b$.
The set of partners is open and dense with $a$ held fixed.
[Open dense partner set](../Lean/MOC/GenericExteriorShift.lean#L97) · [Uniform exterior radius](../Lean/MOC/GenericExteriorShift.lean#L155)

Fix two complex spectral lists $a,b$ of order $n$. For each permutation
$\sigma$, let $s_\sigma=\sum_j a_{\sigma(j)}b_j$. Suppose these sums
are distinct and no three lie on one real affine line in the complex
plane. Then there is one radius $R>0$ such that the determinant inclusion
holds for the lists $(a_i+z)_i$ and $b$ for every complex $z$ with
$|z|>R$ and every relative unitary matrix. The radius depends only on
the two lists.
[Uniform exterior inclusion](../Lean/MOC/UniformExteriorShift.lean#L67)

The set of all $b$ that satisfy this assignment condition is itself
open and dense. Pair differences and signed triangle areas are
continuous functions of $b$. Choose one direction $v$ whose assignment
values are in general position. The dense pole theorem supplies one
for each simple $a$. Along any real line $b+t v$, each pair difference
is affine in $t$ with nonzero slope. Each signed triangle area is a
quadratic polynomial in $t$ whose leading coefficient is its nonzero
area at $v$. Only finitely many $t$ can violate one of these conditions.
Every neighborhood of $b$ therefore contains a good partner.
[Dense pole theorem](../Lean/MOC/ReciprocalSpectralPerturbation.lean#L121) · [Orientation test](../Lean/MOC/AssignmentOrientation.lean#L38) · [Polynomial roots along a line](../Lean/MOC/PolynomialLineDensity.lean#L15) · [Open dense assignment condition](../Lean/MOC/GenericExteriorShift.lean#L97)

Put $t=1/z$. Divide every matching product by $z^n$ to get
$\prod_j(1+t(a_{\sigma(j)}+b_j))$. The product
$F(t)=\prod_i(1+ta_i)\prod_j(1+tb_j)$ is the same for all
permutations. The identity
$(1+ta)(1+tb)=1+t(a+b)+t^2ab$ gives a polynomial $Q_\sigma$ with

$$
\prod_j(1+t(a_{\sigma(j)}+b_j))=F(t)-t^2Q_\sigma(t),
\qquad Q_\sigma(0)=s_\sigma.
$$

General position bounds the real directional value of the signed
permutation sum for $Q_\sigma(t)$ by the largest matching value in
that direction. This bound holds on one open disk around $t=0$ for
all unitary matrices. The signed weights sum to one, so the common
term $F(t)$ and the common scale preserve the hull inclusion. If the
open disk in $t$ has radius $r$, then $R=1/r$ works for the shifts.
[Polynomial identity](../Lean/MOC/UniformExteriorShift.lean#L47) ·
[Uniform stability](../Lean/MOC/SmallSpectralPerturbation.lean#L663) ·
[Affine transfer](../Lean/MOC/SmallSpectralPerturbation.lean#L810)

### One real spectrum

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
[Inverse bound](../Lean/MOC/HermitianExteriorShift.lean#L81) · [Expansion](../Lean/MOC/HermitianExteriorShift.lean#L120) · [Remainder norm](../Lean/MOC/HermitianExteriorShift.lean#L143) · [Frobenius estimate](../Lean/MOC/HermitianExteriorShift.lean#L301)

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
[Block compression](../Lean/MOC/HermitianExteriorShift.lean#L395) · [Support maximum](../Lean/MOC/HermitianExteriorShift.lean#L609)

For a noncollinear triangle on partner values $x,y,w$, let $A$ be its
unsigned area. The gap must satisfy $g(|y-x|+|w-x|)\le 2A$ for each
ordered triangle. A positive gap exists for every finite spectrum.
Half a common lower bound on the triangle altitudes is one choice.
Join two labels when their projected values differ by less than $g$.
Each connected group lies on one affine line. Distinct groups have
projected separation at least $g$. This construction also covers
repeated spectral values.
[Positive gap](../Lean/MOC/HermitianExteriorShift.lean#L834) · [Altitude bound](../Lean/MOC/HermitianExteriorShift.lean#L1043) · [Collinear groups](../Lean/MOC/HermitianExteriorShift.lean#L759)

Diagonalize the Hermitian summand within each group. The affine-line
theorem places each block determinant in its matching hull. Products
of the block convex weights give one convex representation of the full
determinant at a support maximum. The directional hull test then gives
the determinant inclusion for every unitary mixer. The exact support
inequality follows if $|z|>2L+8L^2/g$. Consequently, each fixed pair of
spectra where one spectrum is real has an exterior disk bound that
works for every mixer.
[Affine-line theorem](../Lean/MOC/DruryHermitianPencil.lean#L385) · [Exterior inclusion](../Lean/MOC/HermitianExteriorShift.lean#L987) · [Explicit radius](../Lean/MOC/HermitianExteriorShift.lean#L1060) · [Uniform radius](../Lean/MOC/HermitianExteriorShift.lean#L1188)

For the real spectrum $(-2,-1,0,1,2)$ and the partner spectrum
$(0,1,-1,i,-i)$ before the shift, take $M=2$, $L=3$, and $g=1/(2\sqrt2)$.
The triangle gap applies to all ordered triangles in the partner list.
The determinant inclusion holds for every unitary mixer when $|z|\ge 123$.
[Order-five arithmetic](../Lean/MOC/HermitianExteriorShift.lean#L1090) · [Order-five inclusion](../Lean/MOC/HermitianExteriorShift.lean#L1168)

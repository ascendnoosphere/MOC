# Local genericity at the sharp contact count

**Scope.** Gap-free isolation is checked in
[GapFreeContactFibre.lean](MOC/GapFreeContactFibre.lean).
The [one-dimensional local openness](MOC/AffineCurveLocalOpen.lean)
and [exact small imaginary shifts](MOC/SharpContactImaginaryShifts.lean)
are also checked. A checked corollary makes all active complex products
pairwise distinct at the sharp count. The multidimensional openness, full discriminant
avoidance, and Jacobian conclusions below are paper arguments.

Fix the mixer and nonzero support direction of a strict witness with
contact set $S$ and pivot $r$. Suppose the witness maximizes contact
count for its mixer and $|S|=2n-1$, where $n\ge 2$. Let $X$ be the
irreducible exact-profile variety of complex dimension $d=2n-2$, let
$x_0$ be the witness profile, and set
$$
F:X\longrightarrow \mathbf C^{S\setminus\{r\}},\qquad
F(x)_q=\eta(x_r-x_q).
$$
The point $x_0$ is isolated in $F^{-1}(F(x_0))$ by gap-free
isolation. In an arbitrarily small neighborhood $N$ of $x_0$
in $X$, the positive real determinant gap and all strict inactive
margins persist. Thus every $x\in N$ with $F(x)\in i\mathbf R^d$
is again a strict witness with exactly $S$ as contacts, for the
same mixer, pivot, and direction.

## Openness and good profiles

The map $F$ is locally open at $x_0$. Apply the no-gap-curve
criterion of [Joiţa–Tibăr, Theorem 3.5, DOI
10.4310/ARKIV.2021.v59.n2.a5](https://doi.org/10.4310/ARKIV.2021.v59.n2.a5)
on an irreducible reduced analytic branch of $X$ at $x_0$.
Such a branch has dimension $d$ because the analytification of
a pure-dimensional complex algebraic variety is pure-dimensional.
For any analytic curve germ $C$ through $F(x_0)$, form the set
$F(x)=y$ in the product of the branch and $C$. Its $d$ equations
cut out a germ of dimension at least one through $(x_0,F(x_0))$
in a space of dimension $d+1$. Projection to the source identifies
that fibre product with $F^{-1}(C)$; it cannot be contained in the
isolated fibre. So $F$ has no gap curve, which is the needed
hypothesis. This is a distinct use of the local-open-mapping theorem,
not the one-dimensional continuation used by the checked contact
transfer, which starts from [Zheng, DOI
10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923).

In particular $F(N)$ contains an open complex ball about $F(x_0)$.
If $Z\subset X$ is any proper algebraic subset, the Zariski closure
of $F(Z)$ has dimension at most $d-1$: on each irreducible component,
the map to the closure of its image is dominant, so pulls the
latter function field injectively into the former. That closure
cannot contain an open subset of the slice $i\mathbf R^d$. Indeed,
a polynomial vanishing on a real box of $(it_1,\dots,it_d)$ vanishes
identically, by the one-variable identity theorem applied in the
coordinates successively. A target in the slice in the ball but
outside the closure of $F(Z)$ lifts to a strict witness in $N$
outside $Z$.

For example, take $Z$ to be the union of the following algebraic bad
sets:

* the singular locus of $X$;
* the closure of the critical locus of $F$ on $X_{\mathrm{reg}}$;
* the zero locus of any permutation product and the equality
  locus of any two distinct permutation products.

The critical locus is proper: dominance in equal dimensions makes
the $d$ coordinates of $F$ a transcendence basis, and their
differentials are independent in the function field in characteristic
zero. Each zero-product locus is proper by the all-ones profile.
For a pair $q\ne q'$, choose $j$ with $q(j)\ne q'(j)$. The monomial
$b_j\prod_{i\ne q(j)}a_i$ occurs in the matching product for $q$
but not $q'$, so each equality locus is proper. Their finite union
is proper by irreducibility.

The resulting sharp-count witness has a full, invertible contact
Jacobian on the smooth exact-profile variety, and *all* its complex
permutation products are nonzero and distinct, including inactive
ones. Such a witness cannot have a repeated eigenvalue within one
spectrum or an opposite pair across the spectra. The replacement has
the same mixer, pivot, and contact set, but may not preserve a
secondary spectral maximization property. This is not a rank claim
at the original witness and does not treat more than $2n-1$
contacts, when the target can have dimension greater than $X$.

## A one-dimensional route to independently varying offsets

For a given nonzero pure-imaginary target direction, $d-1$ polynomial
pins force the differences onto the affine line through $F(x_0)$
in that direction. The finite-curve selection theorem gives a prime
affine curve through $x_0$. Its scalar coordinate along the line
cannot be constant. Otherwise the curve would lie in the gap-free
fibre, contrary to isolation. The local image of that coordinate
contains a small disk about its value: take a small closed ball
about $x_0$ whose boundary avoids the fibre. Restrict the target
disk to avoid images of the boundary and all exceptional regular
cover values except possibly the center. The image of the closed
ball is closed. Its intersection with the punctured target disk
is open by the regular cover and nonempty by density of regular
points. The punctured disk is connected, so it is contained in that
image. In particular small real steps along the chosen
pure-imaginary direction occur in every sufficiently small source
neighborhood. Taking a direction with distinct entries (zero at the pivot)
breaks all active collisions simultaneously. This replaces the
multidimensional openness step for just the active collision
question.

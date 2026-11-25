# Affine analytic continuation for the varying-gap step

**Scope.** Lean checks the entire affine-cover route, without a
projective model. The [unconditional contact reduction](MOC/AffineGapCover.lean)
raises the terminal threshold to $2n-1$ and the
[rank theorem](MOC/SharpContactRank.lean) requires at least $2n-2$
independent contact-difference functions at maximal contact count.
The terminal support bound remains open.

## Direct half-plane route

Let $C$ be a prime finite affine curve and $G$ a nonconstant polynomial
coordinate. The checked construction starts with a finite projection $t$.
Use an old primitive coordinate to recover the original affine
coordinates locally. Reverse the irreducible plane equation for
$(t,G)$. A denominator-cleared Bézout identity excludes the nonsimple
fibers in the reversed equation. A simple root then gives a local
branch $t=t(G)$. Compose it with the old affine chart, and use
uniqueness of the near simple roots in both directions to prove both
inverse identities on the actual curve. The [local gap chart](MOC/AffineGapCharts.lean)
does not replace the curve by points in its plane image.

Finite fibers, properness off finitely many values, and cofinite image
supply a [covering map](MOC/AffineGapCover.lean) on the open base.
The chart proof does not use a change of the original function-field base.
The primitive presentation in the next section is an alternative paper
construction.

On the base remove the finite excluded set $B$. The positive half-plane
minus $B$ is path connected: between any two points, an intermediate
point in the half-plane can be chosen off the finitely many lines through
either endpoint and an excluded point. The resulting two line segments
avoid $B$. Over this positive base, every path component surjects by
path lifting, so there are at most as many components as points of one
fiber. The good points accumulate at every point of $C$ by
[gap density](MOC/AffineGapProper.lean). If $x_0$ has positive gap,
$x_0$ belongs to the closure of one of the finitely many positive path
components. Adding $x_0$ to it preserves preconnectedness. The [continuation theorem](MOC/AffineGapContinuation.lean) checks this closure step explicitly.

Choose a real $c\geq 0$ with all excluded base values on or to the
left of $\Re w=c$. A path in the regular positive base to $1+c$
lifts from any starting point in the chosen component. The simply
connected half-plane $\Re w>c$ admits a global lift starting at that
endpoint. The lift's image is in the same positive component. Its
profile coordinates are holomorphic because they agree locally with
the inverse charts. Lean checks the lifting and the resulting
[contact transfer](MOC/HalfPlaneContactTransfer.lean).

If there is no new contact, every projected deficit on the sheet has
nonnegative real part. For a holomorphic $F$ on the right half-plane
with $\Re F\geq 0$, [Lean proves](MOC/HalfPlaneContactLimit.lean) that
$F(x)/x$ tends to a nonnegative real as $x\to+\infty$. A direct proof
uses the Schwarz lemma: for $0<s\leq x$,
$$
 |F(x)-i\Im F(s)|\leq (x/s)\Re F(s).
$$
First prove this for positive real part by sending $s$ and $F(s)$ to
zero in disk coordinates. The Schwarz lemma bounds the quotient by
$(x-s)/(x+s)$; the triangle inequality gives the stated norm bound.
The real quotients decrease to a finite infimum. The norm bound and
then letting $s\to+\infty$ force the complex quotient to the same
limit. Adding and removing $1$ handles nonnegative real part. For the
broader half-plane angular derivative setting see
[Elliott and Jury, Proposition 2.2, DOI 10.1112/blms/bdr110](https://doi.org/10.1112/blms/bdr110)
([open preprint DOI 10.48550/arXiv.0907.0350](https://doi.org/10.48550/arXiv.0907.0350)).
Their proposition is not an imported Lean premise.

Applying this to every deficit and the base parameter $G(z)=z+c$
gives the limits required by the
[profile obstruction](MOC/HalfPlaneProfileObstruction.lean). No limit
assumption on the pivot coordinate is necessary. If its normalized
value remains bounded frequently, a finer filter converges by
compactness; otherwise its norm tends to infinity. The existing
collinear and singleton tangent arguments cover those two cases.

## Alternative using a Laurent sector

## Affine end lemma

Let C be an irreducible complex affine algebraic curve and g a nonconstant regular function on C. Let F₁,…,Fₛ be regular, and let x₀ ∈ C satisfy Re g(x₀)>0 and all Re Fⱼ(x₀)>0. Suppose that there is no point x ∈ C where Re g(x)>0, all Re Fⱼ(x)≥0, and at least one equality holds. Then there are a positive integer m and a holomorphic map φ from a punctured disk into C with:

1. g(φ(t))=t⁻ᵐ.
2. Each regular affine coordinate of φ has a pole or removable singularity at zero.
3. Re Fⱼ(φ(ue^{iθ}))>0 for all j, small u>0 and |θ|<π/(2m).

The j's here are the previously noncontact labels. The old locked differences stay constant on C, so item 3 extends to nonnegativity for every deficit.

**Proof.** Write A=ℂ[C] and K=Frac(A). Since g is nonconstant on the prime affine curve, ℂ(g)⊂K is a finite separable field extension. A primitive element may be chosen in A by taking a generic ℂ-linear combination of a finite set of coordinate generators (the finitely many pairs of embeddings rule out finitely many hyperplanes). Let u be such an element and let its monic minimal polynomial over ℂ(g) be p(g,Y). Clear denominators in the coefficients and in the representations of all coordinate generators as polynomials in u. Invert one polynomial s(g) including the numerator of the discriminant. Then
 A[1/s(g)] ≅ ℂ[g,1/s(g)][Y]/(p(g,Y)).
Indeed the coordinate representations give surjectivity; after monic division an element of the kernel would give a relation of degree less than deg_Y p over ℂ(g). The polynomial p(w,Y) has a fixed positive number of distinct roots for w outside the finite set B of zeros of s. The implicit function theorem at each simple root and the constant root count make g:g⁻¹(ℂ∖B)→ℂ∖B a finite holomorphic covering.

The finite fibres over B intersect C in a finite set (a nonzero regular function on an irreducible affine curve has a zero-dimensional zero set). Each point of C is a Euclidean accumulation point, by the local complex curve dimension theorem. Thus choose a starting point x₁ outside those fibres near x₀ with all the strict inequalities intact. Join g(x₁) to a positive real R₁ beyond a disk containing B by a path in the right half-plane minus B. Lift it by the covering. Along the lift the minimum of the Re Fⱼ remains strictly positive: otherwise a first zero is exactly the excluded point.

Above the exterior |w|>R, choose the connected covering component containing the end of this lift. A connected m-sheeted cover of the punctured disk is given by t↦tᵐ: identify the exterior with a punctured disk by w↦1/w, use the subgroup mℤ of its fundamental group ℤ, and note that the covering isomorphism is holomorphic because both maps have holomorphic local inverses. Choose the root of unity so that the lifted endpoint lies on the positive t-ray. The positive sector |arg t|<π/(2m) is connected and its gap has positive real part. The same first-zero argument gives strict positivity everywhere in that sector.

Each affine coordinate of C is algebraic over ℂ(g), hence satisfies a monic equation with rational functions as coefficients after excluding finitely many more base values. Those coefficients are O(|g|ᴺ) for some integer N. The Cauchy root bound gives the same polynomial growth for the coordinate, uniformly over branches. Substituting g=t⁻ᵐ gives O(|t|⁻ᵐᴺ), so multiplying by tᵐᴺ makes the coordinate bounded on the punctured disk. Riemann's removable singularity theorem gives the claimed Laurent form with finitely many negative powers. This completes the proof.

One may avoid quoting Newton–Puiseux: this particular substitution-and-growth argument already gives the convergent series needed here. A useful equivalent implementation is to first model the root cover of the localized primitive polynomial, lift a path to the exterior, and only then use its finite monodromy to make every chosen branch single-valued.

## Application to MOC

Take g=G, Fⱼ the unpinned deficits on the affine profile curve, and assume no new contact. Item 3 and the angular lemma show tᵐFⱼ(φ(t))→cⱼ∈ℝ≥0, with cⱼ=0 at old contacts. The common profile coordinate divided by G has finite limit or a pole; the [checked meromorphic endpoint](MOC/ContactMeromorphicSector.lean) handles both cases directly. Therefore the affine end lemma suffices for varying-gap transfer.

A real semialgebraic arc alone cannot replace item 3. With m=1, f(t)=i/t is nonnegative in real part on the positive t-ray, but t f(t)=i. Even strict positivity along this ray does not bound the order: f(t)=1/t². The full angular sector is the source of both the reality and the order bound.

## Sources and exact scope

- Flajolet and Sedgewick, *Analytic Combinatorics*, Theorem VII.5: convergent local Newton–Puiseux expansions of algebraic functions, including infinity by inversion. [Book DOI 10.1017/CBO9780511801655](https://doi.org/10.1017/CBO9780511801655), [author copy](https://algo.inria.fr/flajolet/Publications/book050805.pdf).
- Wall, *Singular Points of Plane Curves*, chapter 2: convergent Puiseux expansions and branch geometry. [Cambridge, DOI 10.1017/CBO9780511617560.003](https://doi.org/10.1017/CBO9780511617560.003).
- Basu and Roy, *Quantitative Curve Selection Lemma*: a bounded-degree real semialgebraic arc near a prescribed closure point, not a holomorphic sector. [Journal DOI 10.1007/s00209-021-02837-0](https://link.springer.com/article/10.1007/s00209-021-02837-0), [open preprint DOI 10.48550/arXiv.1803.00505](https://doi.org/10.48550/arXiv.1803.00505).
- Phạm, *Tangencies and Polynomial Optimization*: characterizes boundedness, attainment, sublevel compactness and coercivity using a semialgebraic tangency variety. It does not produce the sector or resolve the terminal profile geometry. [Journal DOI 10.1007/s10107-022-01869-6](https://link.springer.com/article/10.1007/s10107-022-01869-6), [open preprint DOI 10.48550/arXiv.1902.06041](https://doi.org/10.48550/arXiv.1902.06041).
- [Stacks Project, Tag 02GT](https://stacks.math.columbia.edu/tag/02GT) is background for monic simple-root presentations; the proof above constructs the localization directly.

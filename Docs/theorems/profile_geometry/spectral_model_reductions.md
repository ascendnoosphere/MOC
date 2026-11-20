# The precise proof obligation

For normal matrices A and B with eigenvalues a₁,…,aₙ and b₁,…,bₙ, MOC asserts that det(A+B) belongs to the real convex hull in the complex plane of the n! values ∏ᵢ(aᵢ+bπ(i)). The established low-dimensional benchmark n≤3 and the spectral restrictions in Shitov’s 2025 theorem are described in the [primary paper](https://www.mathnet.ru/eng/im9292).

The obligation investigated here is equivalent to unrestricted MOC in dimension four. It is not, by itself, an all-dimensional theorem.

Let β∈ℂ⁴, let U∈U(4), and put C=U diag(β) U*. For a set I of row indices, C[I] denotes the principal submatrix. Define

```text
D₀ = det C[124] + det C[14]
D₁ = C₁₁ + det C[12]

vπ = ( βπ(1)(1+βπ(2))βπ(4), βπ(1)(1+βπ(2)) ).
```

The universal coefficient-hull obligation CH is

```text
(D₀,D₁) ∈ convℝ{vπ : π∈S₄} ⊂ ℂ² ≅ ℝ⁴.
```

The weights may depend on both β and U. Requiring them to reproduce all squared minors, or to work unchanged for a family of β, introduces additional conditions that are sometimes false.

# Why the obligation is equivalent to MOC in dimension four

## From MOC to the coefficient hull

For fixed t∈ℂ, apply MOC to diag(0,1,M,t) and C, divide by M, and let the real number M tend to infinity. Multilinearity of the determinant gives

```text
lim det(C+diag(0,1,M,t))/M = D₀+tD₁.
```

The permutation products converge to the numbers vπ,0+t vπ,1. Therefore every complex projection D₀+tD₁ lies in the corresponding projected convex hull.

Any real linear functional on ℂ² has the form Re(λ₀z₀+λ₁z₁). When λ₀≠0, choose t=λ₁/λ₀; the projection inequality is exactly the required support inequality. Functionals with λ₀=0 follow by continuity. Real separation in ℝ⁴ proves CH.

## From the coefficient hull to MOC

For generic a₁,…,a₄ and b₁,…,b₄, set

```text
κ = (a₂−a₃)/(a₂−a₁)
βⱼ = −κ(bⱼ+a₁)/(bⱼ+a₃)
t = κ(a₄−a₁)/(a₄−a₃)

Γ = −[(a₂−a₁)(a₄−a₃)/(κ²(a₃−a₁)²)] ∏ⱼ(a₃+bⱼ).
```

The associated normal matrix C has the same eigenvectors as B. Direct determinant algebra gives

```text
det(diag(a)+U diag(b)U*) = Γ(D₀+tD₁).
```

Every permutation product has exactly the same factor Γ. Thus a CH law supplies an MOC law. Approximating repeated eigenvalues and avoiding the finitely many poles extends the result by continuity.

There is also an explicit finite recovery of any strict CH violation. Choose c outside {0,−1,β₁,…,β₄,−t}, and define

```text
â = (0, 1/(1+c), 1, t/(t+c))
b̂ⱼ = βⱼ/(c−βⱼ)

Γc = c³ / [(1+c)(t+c)∏ⱼ(c−βⱼ)].
```

Then

```text
det(diag(â)+U diag(b̂)U*) = Γc(D₀+tD₁).
```

To verify the matrix identity, multiply by cI−C, expand along row 3, and factor c/(1+c) and c/(t+c) from the remaining rows. The surviving determinant is det(C[124]+diag(0,1,t))=D₀+tD₁. The same identity holds at every permutation. Thus a genuine separating functional for CH produces a finite MOC counterexample, not merely a limiting one.

# A completed theorem for the square spectrum

For β=(1,i,−1,−i) and every complex U∈U(4), CH holds. More strongly, there exist nonnegative weights λπ with sum one such that

```text
Σπ λπ vπ = (D₀,D₁)
Σπ:π(3)=j λπ = |u₃ⱼ|²  for j=1,2,3,4.
```

This is a theorem about the normalized CH coordinates. It should not be broadened to a claim about arbitrary pairs merely because one untransformed spectrum is square-shaped.

Write pᵢⱼ=|uᵢⱼ|² and qI,J=|det U[I,J]|². Cauchy–Binet and complementary minors give

```text
D₁ = Σⱼ βⱼ p₁ⱼ + Σ|J|=2 βJ q12,J
D₀ = Σⱼ β[4]\{j} p₃ⱼ + Σ|J|=2 βJ q14,J.
```

Let Pⱼ be the convex hull of the six vπ with π(3)=j. A law preserving row 3 exists precisely when

```text
(D₀,D₁) ∈ Σⱼ p₃ⱼ Pⱼ.
```

## Finite geometry and universal inequalities

The uniform weighted sum (P₁+P₂+P₃+P₄)/4 has 37 facet normals. Its exact enumeration checked all 66,045 four-facet bases, and its 76 vertices are among the 221 distinct conditional Minkowski sums.

For each normal f, define hfj=max{f·vπ : π(3)=j}. The needed inequality is

```text
Σⱼ hfj p₃ⱼ − f·(D₀,D₁) ≥ 0.
```

All 37 inequalities have exact rational certificates. Each deficit is an identity consisting of nonnegative scalar moment terms, nonnegative quadratic forms from genuine unitary Gram matrices, and linear combinations of unitary equalities. Complementary SU(4) Gram terms occur in pairs whose hidden parameter cancels. Their validity is pointwise at every complex unitary, not limited to real orthogonal samples.

The complete certificate collection contains 521 Gram terms, including 115 paired complementary terms, and 448 nonnegative scalar terms. The producer’s verifier checked all rational coefficient identities and signs.

A simple facet illustrates the mechanism:

```text
2p₃₃ − Re(D₀+D₁) = 2p₁₃ ≥ 0.
```

The other inequalities are longer versions of the same principle: an exact support deficit becomes a sum of quantities known to be nonnegative.

## Why all omission probabilities are covered

For positive p₃ⱼ, all weighted sums Σⱼp₃ⱼPⱼ have the same normal fan. Their support function is a positive sum of the four support functions. If that sum is linear on a cone, every summand’s convexity deficit must vanish there, because all coefficients are positive. Hence the domains of linearity are independent of the positive weights. The same 37 normals therefore suffice.

Zero probabilities follow by continuity and compactness of the probability simplex. One may mix the target and weights with a fixed interior conditional point, apply the positive-weight hull description, and take a convergent subsequence of the resulting laws. The mixed point need not itself arise from a unitary.

The moment identities, complex Gram construction, normal-fan argument, and boundary recovery were independently audited. The complete rational arithmetic verification of the 37 identities was carried out by the original verifier.

# A bounded Cayley representation covering every unitary

The coordinate coverage part of the proposed global proof can be proved in every dimension.

For any U∈U(n), there is a diagonal unitary D such that V=DU admits

```text
V = (I+K)(I−K)⁻¹
K* = −K
Kᵢᵢ = 0
|Kᵢⱼ| ≤ 1.
```

The canonical matrix also satisfies a stronger condition. With H=iK,

```text
det(I+TH)² ≤ ∏ᵢ(1+tᵢ²)
for every real diagonal T=diag(t₁,…,tₙ).
```

## Proof

Maximize |det(I+DU)| over the compact torus of diagonal phases. The maximum is positive: the determinant’s Fourier polynomial has a nonzero constant coefficient and a nonzero full-degree coefficient, so it cannot vanish identically. Choose a maximizing D. Then I+V is invertible, and K=(V−I)(V+I)⁻¹ is skew-Hermitian.

For a further phase E=diag(exp(2iθᵢ)),

```text
det(I+EV)/det(I+V)
 = det(diag(cos θᵢ)+diag(sin θᵢ)H)
```

up to a scalar of modulus one. The maximum condition bounds its squared modulus by one. Differentiation at θ=0 gives Hᵢᵢ=0. Taking tᵢ=tan θᵢ yields the displayed canonical inequality. Continuity covers the missing cosine-zero angles.

Taking only tᵢ,tⱼ nonzero and comparing the leading coefficient as their magnitudes grow gives |Hᵢⱼ|≤1. Therefore all entries of K lie in a bounded box.

Multiplying U on the left by a diagonal phase does not change the determinant question when A is diagonal. Thus this representation covers every relevant unitary.

## A more explicit four-dimensional form

Put pᵢⱼ=|Hᵢⱼ|², cᵢⱼk=det H[ijk], and d=det H. For real x,y, define

```text
A = 1−p₁₂xy
B = −p₁₃x−p₂₃y+c₁₂₃xy
C = −p₁₄x−p₂₄y+c₁₂₄xy
E = −p₃₄+c₁₃₄x+c₂₃₄y+dxy
L = [[A,C],[B,E]].
```

The full canonical condition is equivalent to LLᵀ≤(1+x²)(1+y²)I₂ for every real x,y. Keeping only its Hessian or its three-dimensional restrictions is insufficient. An exact counterexample to that truncation is H=(2/3)(J₄−I₄): its lower-dimensional tests pass, but the full condition fails at (15,15,−1,−1).

# The global positivity step still needed

Let A=diag(a), B=diag(b), S=A+B, and U=(I+K)(I−K)⁻¹. Direct multiplication gives

```text
N = S + [A−B,K] − KSK

det(A+UBU*) = det N / |det(I−K)|².
```

For any complex support direction η, put

```text
h = maxπ Re(η ∏ᵢ(aᵢ+bπ(i))).
```

The remaining global assertion is

```text
Re(η det N) ≤ h |det(I−K)|²
```

for all actual spectra, all η, and every canonical K described above.

If the identity permutation is chosen to attain h, the numerator deficit has an exact homogeneous decomposition into degrees two through six. Its quadratic part is

```text
P₂ = 4 Σi<j Δᵢⱼ |Kᵢⱼ|²,
Δᵢⱼ = Re(η(z(ij)−zid)) ≤ 0.
```

The degree-six part is likewise a nonpositive combination of squared moduli. The cubic, quartic, and quintic terms remain coupled; they cannot simply be discarded.


# Algebraic restrictions on actual spectral costs

A general nonnegative assignment cost on permutations need not come from the determinant products. This distinction is essential.

For the fourteen permutations

```text
1234 1243 1324 1342 1423 2134 2143
2314 2341 2413 3124 3142 3412 4123
```

let v(a,b) be the vector of products ∏ᵢ(aᵢ+bπ(i)). There is an explicit homogeneous cubic C in these fourteen coordinates, with 49 nonzero integer terms and coefficient absolute sum 50, such that

```text
∇C(v(a,b)) = 0
```

identically in all eight spectral variables. This identity was checked by exact polynomial expansion, not by sampling. The construction is related to the geometry of eight points studied by [Howard, Millson, Snowden and Vakil](https://arxiv.org/abs/1103.5255); the coordinates, exclusion calculation, and certificates here were verified directly.

Write H(x)=Hess C(x), e=(1,…,1), and Q(x)=DₑC(x). For a real spectral cost c=Re(ηv), the homogeneous cubic polarization identity gives

```text
C(c)=0
det H(c)=0.
```

Indeed write c=x+conj(x), where ∇C(x)=∇C(conj(x))=0. Then H(c)(x−conj(x))=0. If the two points coincide, c itself is singular, and Euler’s identity supplies the necessary degeneracy.

The constant vector e is singular, and the exact translation identities are

```text
C(x+he)=C(x)+hQ(x)
Q(x+he)=Q(x).
```

Therefore every affine spectral cost g=he+Re(ηv) satisfies

```text
P(g)=0,
P(x)=det(Q(x)H(x)−C(x)H(e)).
```

This includes repeated eigenvalues, zero paired sums, and limits of unbounded parameter families.

## Reduction from degree 42 to degree 20

Let B=H(e). Exact identities give rank B=4, Be=0, and H(x)e=Bx. Hence

```text
det(H(x)+tB)=d₀(x)+d₁(x)t+d₂(x)t²+d₃(x)t³.
```

The apparent degree-four term vanishes because e is a nonzero radical vector of the compression of H(x) to ker B.

The invariant factors as P=Q¹¹R, where

```text
R = Q³d₀ − C Q²d₁ + C²Qd₂ − C³d₃.
```

R has degree 20, is unchanged by constant translations, and vanishes on every affine spectral cost. The Q=0 cases follow from a polynomial identity in an integral domain, not from division at zero. An actual spectral choice with Q=20 proves that Q is not identically zero.

## An exact exclusion including degenerations

Define the permutation event cost

```text
f = p₄₄+p₂₂+q12,34−q14,14.
```

Every permutation has f≥0, but a particular unitary reflection has f=−7/529. At the selected fourteen permutation values,

```text
C(f)=Q(f)=1
det H(f−e)=−4
||H(f−e)⁻¹||∞=8
R(f)=−4.
```

Consequently f cannot be any affine spectral cost. A quantitative perturbation argument proves

```text
||g−f||∞ > 1/21604800
```

for every affine spectral cost g, including every limit of such costs. Independent coefficient-level audits checked the universal identities and the radius.

This excludes one specific separating facet and a neighborhood. It does not exclude every separating cone, which is what a global MOC proof would need.

# The real information that polynomial equations lose

For any real homogeneous cubic C, let G=∇C and H=Hess C. A real vector c can be written as c=x+conj(x) with G(x)=0 if and only if there is a real vector d satisfying

```text
H(c)d=0
G(d)=G(c).
```

Recovery is x=(c+id)/2.

The proof is the quadratic polarization identity

```text
G((c+id)/2) = [G(c)−G(d)+iH(c)d]/4.
```

Thus the real and imaginary parts vanish exactly under the two stated conditions. Every actual real spectral cost satisfies these conditions. Recovering a singular point of this one cubic is only one part of recovering the full determinant-product parametrization.


Let β=(1,τ,−1,−τ). Put pᵢⱼ=|uᵢⱼ|², qjk=q12,jk, and rjk=q14,jk. The actual coefficient expansions are

```text
D₀=C₀+C₁τ+C₂τ²
D₁=d₀+d₁τ+d₂τ²

C₀=−r₁₃
C₁=p₃₂−p₃₄+r₁₂−r₁₄−r₂₃+r₃₄
C₂=p₃₁−p₃₃−r₂₄

d₀=p₁₁−p₁₃−q₁₃
d₁=p₁₂−p₁₄+q₁₂−q₁₄−q₂₃+q₃₄
d₂=−q₂₄.
```


## Three continuous inequalities that were proved

For 0≤x≤1, all complex unitaries satisfy

```text
(2+2x)C₀+C₁−2C₂−d₀+d₂ ≤ 4(p₃₂+p₃₃)

(2−2x)C₀−C₁−2C₂−d₀+d₂ ≤ 4(p₃₃+p₃₄)

−C₁−2xC₂−d₀+d₂
 ≤ 2(1−x)p₃₁+4x p₃₃+4p₃₄.
```

Each deficit is affine in x. Six exact endpoint Gram certificates at x=0 and x=1 prove all intermediate values by convex interpolation.

For |τ|=1 and x=Re τ, these inequalities appear to supply the three additional projected-hull inequalities needed beyond thirty valid simultaneous-coefficient facets. The projected hull has 52 facets at the sampled exact parameters 1/4, 1/2, and 3/4. Proving that the same description is complete for every 0<x<1 remains unfinished. No full antipodal-circle theorem is asserted.

The auxiliary coordinates c₁=C₁−2p₃₂+2p₃₄ and c₂=C₂−2p₃₁+2p₃₃ differ by an invertible affine change when the row-3 marginal is fixed; this preserves feasibility and certificate validity.

# Other completed positive theorems

## A restricted curvature theorem

Let A be positive definite Hermitian with simple spectrum, and let B be Hermitian. Suppose the pair is irreducible, rank B≥2, and an orbit point is stationary at positive height for Re(η det(A+iUBU*)). Then its Hessian has a positive direction, so it cannot be a local maximum.

The proof reduces T=A⁻¹ᐟ²BA⁻¹ᐟ² to two eigenvalues using stationarity and irreducibility. Its block Hessian has the form

```text
c₊(tr X₊²−s²) + c₋(tr X₋²−s²),
tr X₊=s, tr X₋=−s, c₊+c₋>0.
```

Every trace-compatible pair of blocks is realizable by a tangent direction. The annihilator obstruction would be a nonscalar diagonal matrix commuting with T, contradicting irreducibility. Elementary block choices then provide positive curvature, except in the excluded rank-one case.

The hypotheses of the restricted curvature theorem are essential. The theorem does not establish an analogous assertion for arbitrary complex A and B, or for rank-one B.

## Every four-dimensional unitary has a two-reflection representation after phases

For every U∈U(4), a diagonal phase D can be chosen so that DU has determinant one and real trace. One concrete one-parameter family is

```text
D(t)=diag(det(U)⁻¹ exp(−3it), exp(it), exp(it), exp(it)).
```

The imaginary part of tr(D(t)U) has mean zero, so it vanishes somewhere. An SU(4) matrix with real trace has a real reciprocal characteristic polynomial; its eigenvalues occur in conjugate pairs. Each pair diag(exp(iθ),exp(−iθ)) is a product of two trace-zero Hermitian involutions. Therefore DU=R₁R₂ with both R₁ and R₂ Hermitian involutions of trace zero.

This proves coverage. A determinant support inequality for R₁ and one for R₂ does not automatically compose into one for R₁R₂. That multiplicative compatibility remains unproved.

## Paired Gram dual certificates

The enlarged SU(4) moment construction has eighteen complementary 3 by 3 Gram blocks depending on one hidden parameter. Every dual certificate independent of that parameter decomposes into old Gram terms and pairs of complementary squares whose parameter charges cancel. This follows by rank-one PSD decomposition and a nonnegative flow between positive and negative charges.

The result is a complete dual template for that relaxation. It is not a proof that every actual spectral support deficit belongs to the template.

## Two exceptional columns and an eight-vertex face

An all-dimensional Gram identity gives the Hall inequalities needed to construct a nonnegative flow for two exceptional spectral columns. The corresponding restricted MOC class is already known; the useful result here is an explicit certificate over the entire earlier moment relaxation.

A separate four-dimensional theorem proves positivity of every affine event cost vanishing on one specified eight-vertex permutation face and nonnegative on all permutations. Its proof is an explicit nine-term nonnegative event decomposition. It covers that face, not the full cone of spectral costs.

## The valid compression reformulation

For each n≥3, MOCₙ is equivalent to a rectangular assertion for det(V*AV+diag β), where A is normal of size n, V is an n by n−1 isometry, and the comparison products use injections into the n original spectral nodes.

This is not induction from MOCₙ₋₁. The compression may be nonnormal, and the comparison set still remembers n parent nodes. An exact nilpotent compression illustrates why replacing it by a normal matrix with the same eigenvalues changes the determinant objective.


# Exact definition of the cubic

The coordinate order is

```text
(1234,1243,1324,1342,1423,2134,2143,
 2314,2341,2413,3124,3142,3412,4123).
```

Define C(x)=Σ c xᵢxⱼxk using the following one-based tuples (i,j,k,c). This complete table fixes the normalization used by all constants in this report.

```text
[
 [1,1,7,1],    [1,2,6,−1],   [1,2,7,−1],   [1,3,7,−2],
 [1,4,7,1],    [1,5,7,1],    [1,6,7,−1],   [1,7,7,1],
 [1,7,8,1],    [1,7,9,−1],   [1,7,11,1],   [1,7,13,−1],
 [1,7,14,−1],  [1,9,14,1],   [2,2,6,1],    [2,3,6,1],
 [2,3,7,1],    [2,4,6,−1],   [2,5,6,−1],   [2,6,6,1],
 [2,6,7,−1],   [2,6,8,−1],   [2,6,9,1],    [2,6,11,−1],
 [2,6,13,1],   [2,6,14,1],   [2,8,11,1],   [2,8,14,−1],
 [2,9,11,−1],  [3,3,7,1],    [3,4,7,−1],   [3,5,7,−1],
 [3,6,7,1],    [3,7,7,−1],   [3,7,8,−1],   [3,7,9,1],
 [3,7,11,−1],  [3,7,14,1],   [3,9,14,−1],  [3,10,12,1],
 [4,5,6,1],    [4,6,14,−1],  [4,7,11,1],   [4,8,14,1],
 [4,10,11,−1], [5,6,9,−1],   [5,7,8,1],    [5,8,12,−1],
 [5,9,11,1]
]
```

Exact integer polynomial substitution verifies that all fourteen gradient polynomials vanish identically. The selected facet vector is (1,1,0,0,0,1,0,1,0,0,1,0,1,0), with C=Q=1 and det H(f−e)=−4.


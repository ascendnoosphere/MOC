# Certificates for determinant inclusion

Let $a,b$ be lists of $n$ complex eigenvalues and let $U$ be a unitary matrix
of order $n$. Write $D=\det(\mathrm{diag}(a)+U\mathrm{diag}(b)U^*)$.
For each permutation $\sigma$ of the indices, set
$P_\sigma=\prod_j(a_{\sigma(j)}+b_j)$. Let $K$ be the real convex hull
of these products. The Marcus–de Oliveira conjecture asks whether $D\in K$
for every such input. Each row gives the scope of the linked result.
[Matching products](../Lean/MOC/Core.lean#L21) · [Hull inclusion](../Lean/MOC/Core.lean#L30) · [Proof tree](../README.md#proof-tree)

## Equivalent tests

Each row gives a universal inequality or certificate to seek.
A proof of any one test proves the conjecture in its stated orders.

| Order | Test | Lean statement |
| --- | --- | --- |
| All | Use Gaussian-integer spectra and a Gaussian-integer matrix $V$ with $V^*V=d^2I$ for a positive integer $d$. Compare integer projections on the four coordinate directions and on the normals to differences of matching products. Each input needs finitely many comparisons. Matrix order and entry size are unbounded. | [Integer comparisons](../Lean/MOC/GaussianIntegerDeterminantTest.lean#L28) · [Unrestricted equivalence](../Lean/MOC/GaussianIntegerDeterminantTest.lean#L184) |
| Every positive order | Fix any $R>0$. For $\lvert a_i\rvert,\lvert b_i\rvert<R$ and every $U$, find a matching with $\lvert1+D\rvert^2\le\lvert1+P_\sigma\rvert^2$. The center is always $-1$. | [Disk test](../Lean/MOC/TranslatedDeterminantPowers.lean#L40) |
| Every positive order | With the same radius restriction, prove $\lvert1+D\rvert^{2k}\le\sum_\sigma\lvert1+P_\sigma\rvert^{2k}$ for every integer $k\ge0$. This symmetric sum has a formula in terms of permanents of matrices of pair sums. | [Power test](../Lean/MOC/TranslatedDeterminantPowers.lean#L112) · [Permanent formula](../Lean/MOC/TranslatedDeterminantPowers.lean#L132) |
| Every positive order | Fix one entry of $b$ as a free complex variable $z$. Write $D(z)=x+zy$ and $P_\sigma(z)=s_\sigma+zt_\sigma$. For each complex direction $\eta$, use at most three pairs $(s_\sigma,t_\sigma)$ with affinely independent slopes over the reals. Their probability weights must average the slopes to $y$ and the projected intercepts to at least $\mathrm{Re}(\eta x)$. Equivalently, enumerate the feasible triples, pairs and singletons and test $x$ in the planar hull of their intercepts. | [Finite intercept hull](../Lean/MOC/FreeEigenvalueSlopeSlice.lean#L205) · [One free entry](../Lean/MOC/FreeEigenvalueSlopeSlice.lean#L251) · [Order equivalence](../Lean/MOC/FreeEigenvalueSlopeSlice.lean#L282) |
| Four | Test first lists $(1,-1,z,-z)$ with $\mathrm{Im}(z)>0$ and $\lvert z\rvert<1$, every second list, and every real orthogonal mixer. A fractional linear map gives the two antipodal pairs. The boundary consists of spectra on a circle or a line. | [Chart](../Lean/MOC/FourAntipodalSpectra.lean#L20) · [Boundary](../Lean/MOC/FourAntipodalSpectra.lean#L100) · [Orthogonal test](../Lean/MOC/FourAntipodalSpectra.lean#L208) |

```mermaid
flowchart BT
    Root["Unrestricted MOC"]
    Int["Integral Gram and projection tests in all orders"]
    Fixed["MOC in a fixed positive order"]
    D["Disk bound for bounded spectra"]
    P["Every power bound for bounded spectra"]
    S["Free eigenvalue slope test"]
    F["MOC at order four"]
    H["Antipodal spectra with orthogonal mixers"]
    Int <-->|iff| Root
    D <-->|iff| Fixed
    P <-->|iff| Fixed
    S <-->|iff| Fixed
    H <-->|iff| F
```

For the disk test, a strict excess of the real part persists after both
spectra are multiplied by a sufficiently small positive real number $t$.
The disk comparison detects the excess in its term of order $t^n$.
For the power test, if the determinant distance exceeds every matching
distance, its $2k$-th power exceeds their sum for some finite $k$.
The required exponent can depend on the input.
[Scaling argument](../Lean/MOC/TranslatedDeterminantPowers.lean#L40) · [Finite power comparison](../Lean/MOC/TranslatedDeterminantPowers.lean#L84)

## All-order structural results

| Method | Result and remaining step | Lean statement |
| --- | --- | --- |
| Forced eigenvalue multiplicity | Write $m_a(c)$ for the number of entries of $a$ equal to $c$. Fix $z\in\mathbb C$ and an integer $k\ge0$. The sum has $z$ as an eigenvalue of algebraic multiplicity at least $k+1$ for every mixer if and only if some $c$ satisfies $m_a(c)+m_b(z-c)>n+k$. If the test fails, a permutation mixer witnesses the failure. The signed polynomial identity gives divisibility for every mixer. | [Matching count](../Lean/MOC/ForcedSpectralMultiplicity.lean#L74) · [Polynomial identity](../Lean/MOC/ForcedSpectralMultiplicity.lean#L117) · [Sharp criterion](../Lean/MOC/ForcedSpectralMultiplicity.lean#L170) |
| Composition of two mixers | Let $U,V$ be unitary. For every permutation $p$, require each choice of indices $f(j)$ with $U_{p(j),f(j)}V_{f(j),j}\ne0$ for every $j$ to use each index once. Fix $a$. Assume $U$ has one matching law for all second lists and $V$ satisfies inclusion at each required relabeling of $a$. Then inclusion holds for $UV$. | [Path test](../Lean/MOC/PermutationPathComposition.lean#L25) · [Signed convolution](../Lean/MOC/PermutationPathComposition.lean#L160) · [Composition](../Lean/MOC/PermutationPathComposition.lean#L236) |
| One shared coordinate | If the two unitary factors act on coordinate blocks with exactly one shared coordinate, only one entry of the second list in the first block must vary. Inclusion for all spectra for each factor suffices. Neither factor needs one law for all spectra. | [Supported determinant formula](../Lean/MOC/PermutationPathComposition.lean#L177) · [Composition with one shared coordinate](../Lean/MOC/SinglePortComposition.lean#L132) |
| Sequence of blocks with one common coordinate | Take any finite ordered sequence of unitary gates extended by the identity outside their blocks. The blocks all contain a fixed coordinate and are pairwise disjoint outside it. If each gate satisfies inclusion for all spectra on its block, the product satisfies inclusion for all spectra. | [Ordered composition](../Lean/MOC/StarPortComposition.lean#L80) |
| Common low-degree coefficients | Fix $U$. One probability law gives the first three coefficients of $\det(I+x(\mathrm{diag}(a)+U\mathrm{diag}(b)U^*))$ for all $a,b$. This supplies the three low-degree bounds in the separate-coefficient route. At order four the remaining coefficient is the determinant. | [Uniform law](../Lean/MOC/Reformulations/SecondCoefficient.lean#L248) · [Remaining coefficients](../Lean/MOC/Reformulations/SecondCoefficient.lean#L293) |

## Order-four and order-five support bounds

In a direction $\eta\in\mathbb C$, write
$H=\max_\sigma\mathrm{Re}(\eta P_\sigma)$ and
$L=\min_\sigma\mathrm{Re}(\eta P_\sigma)$. A contact attains $H$.
The support gap of a matching is $H-\mathrm{Re}(\eta P_\sigma)$.
The conjecture asks for $\mathrm{Re}(\eta D)\le H$ in every direction.
[Support criterion](../Lean/MOC/Support.lean#L52)

| Order and method | Result and remaining step | Lean statement |
| --- | --- | --- |
| Four, width of the hull | Every unitary satisfies $\mathrm{Re}(\eta D)\le H+(H-L)/27$. The resulting enclosure is the hull of the points $P_\sigma+(P_\sigma-P_\tau)/27$. The original bound requires zero excess. | [Width estimate](../Lean/MOC/FourMixedRaySupportBound.lean#L222) · [Hull enclosure](../Lean/MOC/FourMixedRaySupportBound.lean#L249) |
| Four, individual support gaps | The order-four support cone has 48 mixed rays. If a mixed ray has negative value $v$ at $U$, take any matching where this ray has coordinate $r>0$. If the matching gap there is $g$, then $\mathrm{Re}(\eta D)-H\le -vg/r$. A contact on that coordinate gives the required bound. General spectra can have $g>0$. | [Ray lower bound](../Lean/MOC/FourMixedRaySupportBound.lean#L121) · [Coordinate estimate](../Lean/MOC/FourMixedRaySupportBound.lean#L202) |
| Four, canonical gaps at heights from zero through one half | Require the support gap vector to equal the fixed mixed ray with coefficient one plus a nonnegative combination of the thirteen prescribed ordinary rays. If $0\le H\le1/2$ under this normalization, the gap is a sum of matching squares and $\mathrm{Re}(\eta D)\le H$ for every unitary. | [Thirteen rays](../Lean/MOC/FourCanonicalHeightSquares.lean#L17) · [Square certificate](../Lean/MOC/FourCanonicalHeightSquares.lean#L719) · [Unitary support bound](../Lean/MOC/FourCanonicalHeightSquares.lean#L767) |
| Five, transport between disjoint pairs | The squared minors for two disjoint column pairs admit a joint distribution on disjoint row pairs. The resulting inequalities strengthen the assignment bound. A bound that reaches a matching score proves the directional inequality for that input. The universal certificate test is refuted. | [Transport](../Lean/MOC/OrderFiveDisjointPairSupport.lean#L20) · [Dual bound](../Lean/MOC/OrderFiveDisjointPairSupport.lean#L145) · [Refuted test](../Lean/MOC/OrderFiveDisjointPairObstruction.lean#L122) |
| Five, a sharp spectral certificate | For the two specified Gaussian-integer spectra and $\eta=34944-130480i$, every unitary satisfies $\mathrm{Re}(\eta D)\le1\,228\,164\,224$. A matching attains equality. The certificate combines 39 nonnegative minor terms with a disjoint-pair inequality. It applies to this direction and these spectra. | [Spectra and direction](../Lean/MOC/OrderFiveDisjointPairSupport.lean#L215) · [Bound](../Lean/MOC/OrderFiveDisjointPairSupport.lean#L289) · [Attainment](../Lean/MOC/OrderFiveDisjointPairSupport.lean#L322) |

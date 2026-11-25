# Paths 09 and 15: four-clique swap contacts force spectral circles

Let r be a pivot and η a support phase. On a chosen set of labels write Aᵢ=a_(r i), Bᵢ=−bᵢ, z=ηP_r. Assume both lists are injective on these labels and z≠0. Thus each diagonal qᵢ=Aᵢ−Bᵢ is nonzero. The exact swap gap is

    Gᵢⱼ = η(P_r−P_(r (i j))) = z (Aᵢ−Aⱼ)(Bᵢ−Bⱼ)/(qᵢqⱼ).

The contact premise is Re Gᵢⱼ=0 on the chosen edges. No other matching product needs to be nonzero. None of the circle statements below use the upper support inequalities, except the stated zero-height support corollary.

## Four-clique at nonzero height

Suppose the six edges on distinct i,j,k,l are active and Re z≠0. Put

    x = (Aᵢ−Aⱼ)(A_k−A_l)/((Aᵢ−A_k)(Aⱼ−A_l))
    y = (Bᵢ−Bⱼ)(B_k−B_l)/((Bᵢ−B_k)(Bⱼ−B_l)).

Then xy=GᵢⱼG_kl/(GᵢkGⱼl) is real. The complementary cross ratio 1−x is obtained by interchanging j and l, and similarly for y, so (1−x)(1−y) is real. Consequently x+y is real. Comparing imaginary parts in xy shows either x and y are both real or y=conj x: if Im x≠0 then Im y=−Im x and Re y=Re x.

If x,y are real, each quartet lies on a generalized circle. For an explicit certificate choose distinct p,q,r and set k=(q−r)/(q−p). Then the real fractional coordinate k(w−p)/(w−r) is equivalent off r to

    Im[k(w−p)conj(w−r)]=0.

The cleared equation holds at r too. This is a nontrivial real linear combination of |w|², Re w, Im w and 1. If all nonconstant coefficients vanish, k is nonzero real and p=r, a contradiction. This proves the generalized-circle claim, including collinear quartets.

In the other case, normalizing the first three points of each list to 0,1,∞ reconstructs the anti-Möbius match

    Bᵢ = (r₀ conj Aᵢ+s)/(u conj Aᵢ+v).

The determinant Δ=r₀v−su is nonzero, and each denominator is nonzero because the matched Bᵢ is finite. Write Lᵢ=qᵢ(u conj Aᵢ+v). The gap formula now becomes

    Gᵢⱼ = z Δ |Aᵢ−Aⱼ|²/(LᵢLⱼ).

Two gaps to a shared third label show Lᵢ/Lⱼ is nonzero real. Scale the four Möbius coefficients so all Lᵢ are real. But then

    Im[u|Aᵢ|² + v Aᵢ − r₀ conj Aᵢ − s]=0.

If the A quartet is not circular, this equation must vanish identically: a nontrivial equation of that form through four distinct points is a circle or line. Hence u,s are real and r₀=−conj v. This makes Δ real nonzero. The formula for Gᵢⱼ makes it a nonzero real multiple of z, contradicting Re z≠0. This proves the circle claim for A; exchange A and B to prove it for B.

**Consequences.** An order-four complete swap clique at nonzero support height satisfies MOC for every mixer by the independent two-spectral-circles theorem. More generally, if a family of active K4s covers the entire label set and connects through three-label overlaps, their generalized circles glue on each spectrum, because three distinct points determine a generalized circle. The same “fixed three anchors” effect can use only active four-cycles if one spectrum is already known circular, by the product cross-ratio test.

## Complete swap graph at zero height (paper extension)

Assume z≠0, Re z=0, all swaps are active, and the pivot is at the upper support height. If A is circular, all its quadruple cross ratios are real, and their nonzero products with corresponding B cross ratios are real. Thus all B points lie on one generalized circle as well. The two-circles theorem applies.

If A is noncircular, choose a noncircular base quartet. Its conjugate cross ratios give a unique anti-Möbius T on these four matches. Every other A point forms a noncircular quartet with some triple of this base: the distinct generalized circles on triples sharing two base labels intersect only at those labels. Applying the conjugate alternative again gives the same T, because the anti-Möbius maps agree at the three shared points. Thus T matches every label.

As above scale its parameters so u,s are real and r₀=−conj v. Then the column-scaled kernel

    Cᵢⱼ = (Aᵢ−Bⱼ)(u conj Aⱼ+v)
         = u Aᵢ conj Aⱼ + v Aᵢ + conj(v)conj Aⱼ − s

is Hermitian. Its nonzero pivot product is real. With η rescaled by the inverse of the fixed column product, Re z=0 means the rescaled η is purely imaginary. Inverse permutations give conjugate matching products of C, hence opposite projected support values. Upper support height zero then forces every projected value to vanish. The real signed determinant law gives projected value zero for every mixer, so there is no strict witness in this direction. This does not address a zero pivot product.

## Literature scope

The four-point cross-ratio criterion is standard; see Section 2.4 of [Isothermic nets with spherical parameter lines from discrete holomorphic maps](https://doi.org/10.1093/imrn/rnag094). The proof above includes the needed cleared-polynomial criterion rather than assuming it. [Lam, Quadratic differentials and circle patterns on complex projective tori](https://doi.org/10.2140/gt.2021.25.961), [arXiv:1909.07258v2](https://arxiv.org/abs/1909.07258v2), builds structures from edge cross-ratios subject to vertex equations and prescribed Delaunay angles on a triangulated torus. Its theorem does not directly apply to a spectral contact graph. The new step here is the anti-Möbius alternative combined with the determinant swap-gap phase.

[Kovačec's DMUC 26-11 v2, 4 November 2026](https://www.mat.uc.pt/preprints/ps/p2611.pdf) confirms that v1's transposition-polygon upper enclosure is false and analyzes a reverse inclusion under simple connectivity. It does not settle the original MOC. [Mulero-Martínez](https://doi.org/10.1016/j.laa.2026.03.019) develops variational proofs for structured spectra and shows support maximizers need not all be monomial. Stationarity alone does not remove the terminal gap.

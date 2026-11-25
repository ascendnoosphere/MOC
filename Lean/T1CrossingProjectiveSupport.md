# A crossed contact for two projective outliers

This gives an all-order support result and a second proof of the
T1 case of [Denzel Zheng, Appendix E, DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923).
It does not require the facet list or the unpublished supplement.

## The all-order assertion

Use signed spectra \(a,c=-b\) and let
\(P_\sigma=\prod_i(a_i-c_{\sigma(i)})\). Assume the \(2n\) marked points
are distinct. Suppose a supporting line is
\(\operatorname{Re}(\eta z)=0\), so
\(\operatorname{Re}(\eta P_\sigma)\le0\) for every \(\sigma\).
All but one point in each signed spectrum lie on a common generalized
circle. Suppose there is a contact matching the two exceptional
points to one another, and that swapping this assignment with one
other row gives another contact. Then the same supporting line bounds
the determinant for every unitary mixer. This is a conclusion in
the stated direction, not a claim about other supporting lines.

The two contacts give a nonzero real ratio of the switched
two-factor products, since each rotated product is purely imaginary.
The four switched points therefore lie on a generalized circle.
Either all marked points lie on the common circle, in which case
a common real projective chart and the real-spectra theorem apply,
or two distinct circles meet at the two switched ordinary points.
Normalize the common circle to the real line, and send these two
ordinary points to \(0,\infty\) by a real Möbius map. The second circle
then becomes a line through zero; a line through zero other than
the perpendicular is also possible for two circles that cross.
**For the comparison below the second line need not be perpendicular.**

Write the exceptional points as \(a_0=p\omega\), \(c_0=q\omega\),
where \(p,q\) are nonzero real numbers and
\(\omega=e^{i\theta}\) with \(\sin\theta\ne0\).
The ordinary points used in the swap are \(a_1=0,c_1=\infty\).
Use homogeneous brackets, with the infinity bracket for \(c_1\)
taken as \(+1\), absorbing its fixed sign into the support multiplier.
Because the pivot is a nonzero real factor times \((p-q)\omega\),
the new multiplier is \(i\epsilon/\omega\) for some
\(\epsilon\in\mathbb R\setminus\{0\}\).
An unpaired crossing matches \(a_0\) to \(c_j\) and \(a_i\) to \(c_0\).
For finite \(c_j\), its real projected two-factor product is
\[
\operatorname{Re}\left(\frac{i\epsilon}{\omega}
       (p\omega-c_j)(a_i-q\omega)\right)
  =\epsilon\sin\theta\, (pq-a_i c_j).
\]
If \(c_j=\infty\), it equals \(\epsilon\sin\theta\,a_i\).
A matching that pairs the exceptional points has zero projection.
Thus, with the real multiplier \(\epsilon\sin\theta\)
in the comparison, the projected profile is exactly the profile of
pure imaginary outliers \(ip,iq\). This identity also explains why
orthogonality of the original circles is not required.

## Why feasibility forces aligned signs

Let \(R,C\) be the \(k=n-2\) remaining finite rows and columns after
removing both exceptional labels and both ordinary anchors.
Write \(\epsilon'\) for the real scalar
\(\epsilon\sin\theta\). Take a crossing with \(i=1\) and \(j\in C\).
Its two-factor contribution is \(\epsilon'pq\). All partial
matchings of size \(k-1\) between \(R\) and \(C\) appear as its
remaining finite brackets, since one unused row goes to \(\infty\).
Feasibility implies that all these nonzero products have the same
sign. For \(k\ge2\), compare two entries of a fixed column, with a
common matching of \(k-2\) entries avoiding their rows and column.
Their signs agree. The same argument for two entries of a fixed row
shows that all finite spectator differences on \(R\times C\) have
one sign \(\Delta\). For \(k=1\) use the empty product instead. For
\(n\le2\) the order-two support theorem applies.

Next take \(i\in R,j=1\), so \(a_0\) goes to infinity. Match
the ordinary zero row \(a_1\) to any \(c_\ell\in C\).
The sign of the projected product is now that of
\(-\epsilon'a_i c_\ell\Delta^{k-1}\). The first family had sign
\(\epsilon'pq\Delta^{k-1}\). All are strictly negative, so
\(-a_i c_\ell\) and \(pq\) have the same sign. This holds for every
finite crossed pair with both entries nonzero; when \(i=1\)
or \(j=1\), one of the two contributions is zero.

## Two real profiles

Replace the two exceptional homogeneous coordinates by \((0,1)\)
in both spectra to obtain the projective profile \(P^{(0)}\).
Replace both by \((1,0)\) to obtain \(P^{(\infty)}\). Multilinearity
of each bracket gives the exact real part for pure imaginary
outliers:
\[
  \operatorname{Re}P(ip,iq)=P^{(0)}-pq\,P^{(\infty)}.
\]
When the exceptional labels are matched together, all three sides
vanish. Otherwise the mixed terms are purely imaginary, and the
two real coefficients are the aligned pieces just identified.
Thus each of \(\epsilon'P^{(0)}\) and
\(-\epsilon'pq\,P^{(\infty)}\) separately has every permutation
value \(\le0\). Each is a real projective profile. Take any common
real Möbius chart in which all its points are finite. The product of
the homogeneous normalizers is one nonzero factor, independent of
the permutation, so
[Fiedler's real-spectra theorem, DOI 10.1090/S0002-9939-1971-0286814-1](https://doi.org/10.1090/S0002-9939-1971-0286814-1)
bounds each signed determinant evaluation. Linearity now proves the
claim by the
[Merikoski–Virtanen signed determinant law, DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X).
For the projective change of chart the common-factor rule follows
from multiplying the homogeneous brackets; the identity
\([Gx,Gy]=\det(G)[x,y]\) holds for every two-by-two \(G\).

[ZhengT1ProjectiveSupport.lean](MOC/ZhengT1ProjectiveSupport.lean)
checks the finite real chart, the exact real-profile decomposition,
and the determinant inequality from aligned signs in arbitrary
finite order. The circle and matching-sign arguments above are paper
arguments.

## Specialization to T1

Use zero-based row-to-column labels \(0,1,2,3,6,7\) from the preprint.
The rectangle \(0,1,6,7\) has two disjoint swaps and forces height
zero: at nonzero common real part, equality of the two opposite
products gives equal sum and product of their imaginary parts.
This would identify a pair of neighbors differing by one swap,
contrary to distinct spectra and nonzero pair factors.

At zero height all ratios of active products are real. The swaps
\(0,1\), \(0,2\), and \(2,3\) respectively put
\[
(a_2,a_3,c_2,c_3),\quad
(a_1,a_2,c_1,c_2),\quad
(a_2,a_3,c_1,c_3)
\]
on generalized circles. The first and third share three points;
their union and the second also share three points. Consequently
all six spectator points lie on one circle. The contacts \(0,6\)
are the crossed contact pair of the all-order assertion. If
distinctness fails, the checked
[repeated-entry case](MOC/TwoExceptions.lean) or
[opposite-entry case](MOC/FourCoincidence.lean) handles order four.
The [stabilizer law](ZhengT1Stabilizer.md) gives another proof,
using a single common law for the projected profile in order four.

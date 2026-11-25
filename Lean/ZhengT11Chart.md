# Group III: rational chart for T11

This paper result proves the zero-height T11 comparison on the simple,
disjoint chart and leaves the nonzero-height inequality open. Use the row-to-column labels of [Zheng,
Appendices E and G](https://doi.org/10.13140/RG.2.2.36790.25923). The six
contacts are \(0,1,3,5,6,8\). Repeated eigenvalues and vanishing cross
factors are covered by the checked order-four results in
[TwoExceptions.lean](MOC/TwoExceptions.lean) and
[FourCoincidence.lean](MOC/FourCoincidence.lean).

Map three first-spectrum points to \(A_1=\infty\), \(A_2=0\), \(A_3=1\).
Write \(A_0=x\) and the signed second spectrum as \((w,t,c,z)\). Use
infinity factor 1 and adjust the support direction for the common
bracket scaling as in [ProjectiveTransport.lean](MOC/ProjectiveTransport.lean).
Put \(D=P_0-P_1=(x-w)(z-c)\), which is nonzero. All ratios of contact
differences to \(D\) are real. Since \(P_3-P_5=(t-1)D\), the parameter
\(t\) is real. Define
\[
k=(P_0-P_5)/D=\frac{c(z-t)}{z-c},\qquad R=P_0/D.
\]
Here \(k\ne0\). Hence \(c=kz/(z+k-t)\) and \(R=k(z-1)/(z-t)\).
Let \(m=(P_0-P_6)/D\), \(n=(P_6-P_8)/D\) be the remaining
real contact ratios. The one-swap products give
\[
\frac{P_6}{D}=R\,\frac{x-t}{x-w},\qquad
\frac{P_8}{P_6}=\frac{w}{c}.
\]
Consequently
\[
w=c\left(1-\frac{n}{R-m}\right),\qquad
T=\frac{R-m}{R},\qquad x=\frac{Tw-t}{T-1}.
\]
No denominator here vanishes at the original simple disjoint profile:
\(R\) and \(R-m\) are nonzero matching-product ratios, and
\(T-1=(w-t)/(x-w)\). Conversely, away from poles and coincidences, these
formulas preserve all six contacts with \(t,k,m,n\) fixed real and
\(\eta D\) pure imaginary.

At height zero, \(R\) is real because \(\eta D\) is nonzero pure imaginary
and \(P_0\) is a contact. The real fractional-linear map
\(z\mapsto k(z-1)/(z-t)\) is invertible because \(k
e0\) and \(t
e1\),
so \(z\) is real. The reconstruction now makes \(c,w,x\) real as well.
In the normalized chart every product is real, and the support phase
is pure imaginary because \(D\) is real and nonzero. Every projected
matching product is therefore zero. The real signed determinant
expansion gives zero projected determinant for every unitary
([Merikoski–Virtanen, DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X);
[checked identity](MOC/Weights.lean)). This proves the zero-height
comparison. The signed support inequality at nonzero height remains
open in this note.

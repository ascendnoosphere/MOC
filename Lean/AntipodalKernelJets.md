# Singular antipodal centers

The antipodal reduction brings a nearly real strict witness close to spectra
with two values and equal sign multiplicities. At a singular center it is
important to compare determinant and matching products at the same order.
The results below treat fixed mixers and identify the part of a moving
mixer's tangent that enters at corank two.

## Checked in Lean

Let $J,K$ be Hermitian involutions with equal traces, $S=J+K$, and
$H$ any complex matrix. Write $E=\ker S$, $C=E^\perp$, and
$c=\dim E$. The [kernel calculation](MOC/AntipodalKernelJet.lean) gives
$$
 [t^k]\det(S+tH)=0\quad(k<c),\qquad
 [t^c]\det(S+tH)=\det(S|_C)\det(H_{EE}).
$$
Both involutions reduce $E$, and on $E$ they are opposites. In a basis
diagonalizing $S$, their diagonal entries agree off $E$. Their traces
therefore force the restriction $J|_E$ to be traceless, so $c=2r$.
This is the part of the geometry also visible in
[Halmos's two-subspace decomposition, DOI 10.1090/S0002-9947-1969-0251519-5](https://doi.org/10.1090/S0002-9947-1969-0251519-5).
Lean proves it directly and factors the pencil by rows. Neither $S^{-1}$
nor invertibility of $H_{EE}$ is required.

The [center formula](MOC/AntipodalCenterMinor.lean) expresses the entire
center determinant as the common aligned product times one squared
unitary minor in $[0,1]$, including zero. It uses the subset-image
marginal of [Merikoski and Virtanen, DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X),
not the full two-subspace decomposition.

[Matching jets](MOC/DeterminantJetNeighborhood.lean) count zero matched
sums exactly: each canceled sum contributes a factor of $t$.
At the resulting order the coefficient is the product of the remaining
center factors and the canceled-slot velocities. If a finite subfamily
of matching products has no terms below degree $c$, and its degree-$c$
coefficients contain the determinant coefficient in their ordinary
complex-plane interior, the same affine path satisfies the **full hull
inclusion for every sufficiently small complex parameter**. The proof
uses a uniform directional margin for the normalized polynomials.
A boundary coefficient gives no such conclusion.

At corank two, [the orbit tangent formula](MOC/AntipodalMovingCompression.lean)
takes a kernel frame $F$ with signs $+,-$ for $J$, and a
skew-Hermitian tangent $X$. The correction to the compressed
determinant on adding $XK-KX$ is
$-4 |(F^*XF)_{01}|^2$. The module proves the corresponding one-sided
support comparison when the projected reduced determinant is
nonnegative. This is an algebraic statement about the tangent, not a
claim at finite mixer displacement.

## Smaller-order comparison for all fixed-mixer leading jets

The following assembly is a paper argument. The arbitrary-frame step
that reduces the compression to smaller-order MOC is [checked in
Lean](MOC/ReducedTwoFrame.lean). The checked theorem includes the
endpoint with no extra zero vertex when one frame covers its sign
class. The full two-compression leading-jet comparison is not yet checked.

Let the positive and negative spectral multiplicities be $p,q$ in both
summands, with $p+q=n$. For a fixed mixer and affine spectral
velocities, $H=V+W$ with $V$ commuting with $J$ and $W$ commuting
with $K$. The two $r$-dimensional sign spaces in $E$ split
$H_{EE}$ into two compressions: one between the positive $J$ and
negative $K$ spectra, and the other between the negative $J$ and
positive $K$ spectra. Each has the form
$$
 E_1^*\operatorname{diag}(x)E_1 + E_2^*\operatorname{diag}(y)E_2
$$
for isometries of column dimension $r$ into the two sign spaces.

The relevant padded spectral problem has order $N=p+q-r=n-r$.
Embed the two $p$- and $q$-dimensional spaces isometrically in a
common $N$-space, identifying precisely their compressed $r$-frames
and making their complements orthogonal. The sum of the two projections
has determinant $2^r$: it is twice the identity on the shared space
and the identity on its orthogonal complement. With the nonzero
reciprocal spectra $x^{-1},y^{-1}$, padded by zeros, the
[support-frame identity](MOC/RankTwoOverlap.lean) identifies the
determinant with the compressed determinant times the common factor
$\prod_i x_i^{-1}\prod_j y_j^{-1}$.
If some deviations are zero, replace $x,y$ by $x+s,y-s$, with
$s$ outside the finite set of forbidden shifts. This changes neither
the compression nor the sums $x_i+y_j$.

Every nonzero padded matching has exactly $r$ pairs between nonzero
labels. After removing the same common factor it yields a product of
$r$ distinct crossed sums. A zero-zero pair contributes the extra
vertex zero only when both padding counts are positive. Lower-order
MOC therefore bounds each compressed determinant by its $r$-edge
matching hull, with that possible zero vertex.

On $C$, the two involutions have positive multiplicity $p-r$ and
negative multiplicity $q-r$. The checked center formula supplies a
factor $\rho\in[0,1]$ multiplying the aligned reduced product. Multiply
the two convex-combination formulas, and extend the selected $r$
crossings each way by matching the remaining labels within signs.
If $r<\min(p,q)$, a matching with $r+1$ crossings each way realizes
a zero coefficient at order $2r$. It supplies any unused weight
from the two compression comparisons or $\rho$. If
$r=\min(p,q)$, the reduced involutions have only one sign,
$\rho=1$, and one of the padding counts is zero.

Thus MOC below order $n$ suffices for the fixed-mixer leading
coefficient comparison at every singular balanced center. It does
not bound later terms when the first comparison is on the boundary,
does not handle arbitrary moving mixers, and does not force a
hypothetical strict witness to lie in an interior-jet neighborhood.

For corank two, the [cubic analysis](AntipodalCubicAudit.md) proves on
paper that one mixture matches both the quadratic and cubic coefficients.
Lean checks the cubic Schur formula and signed residual cancellation. The
same note gives a symbolic obstruction to a direct mixed-term bound for
moving mixers in corank four. It is not a counterexample to the conjecture.

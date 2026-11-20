# Spectral normalizations for the order-four question

All spectra below are ordered when computing a cross-ratio. For terminology in the request, take $S_{L_3}$ to mean four distinct nonconcyclic points, three collinear, and $S_{G_4}$ to mean four distinct nonconcyclic points with no collinear triple. Here “concyclic” includes four points on a line. Statements about one specified spectrum allow the other to be arbitrary. A single change of variables acts on both spectra. It need not put a chosen triple of each on a line simultaneously.

## Two exact changes of variables

**Equal elementary symmetric functions (D).** In the sum convention replace the matrices by $A+tI,B-tI$. Their sum and each matched factor $a_i+b_j$ stay fixed. In dimension $n$, take $t=(\operatorname{tr} B-\operatorname{tr} A)/(2n)$. Every instance then has equal first elementary symmetric functions. Even the equal-$e_2$ alternative alone suffices to imply general MOC in each dimension $n\ge2$. Indeed,
$$
 e_2(a+t)-e_2(b-t)=e_2(a)-e_2(b)+(n-1)t(e_1(a)+e_1(b)).
$$
Choose $t$ to make this zero whenever the coefficient is nonzero. These pairs are dense. Hull membership is closed because the determinant and all finitely many vertices are continuous and the simplex of probability weights is compact. No bound on $t$ is needed since one returns to the original unshifted pair *before* taking the limit. Thus proving D in either order four or five entails the entire conjecture in that order.

**Fractional linear covariance.** Put $C=-B$ and use the difference $A-C$. For $f(z)=(az+b)/(cz+d)$ with $ad-bc\ne0$, choose the pole off both spectra. Multiplying on the left by $cA+dI$ and on the right by $cC+dI$ gives
$$
 (cA+dI)(f(A)-f(C))(cC+dI)=(ad-bc)(A-C).
$$
Consequently the determinant and each matched product acquire the same nonzero multiplier, $(ad-bc)^n/[\det(cA+dI)\det(cC+dI)]$. The functional calculus preserves the chosen eigenbases. Every convex witness works in both directions. If only the other spectrum meets a pole needed for a construction, perturb it first and use closedness after returning to the original coordinates. [Projective reduction](../research/MOBIUS_REDUCTION.md)

**Simultaneous equality.** Even imposing both equalities in D at once suffices to test general MOC in every order $n\ge2$. Work first with disjoint simple spectra $x=\sigma(A),y=-\sigma(B)$. For a pole $t$ write $h_t(u)=1/(u-t)$ and
$$
 V_x(t)=\sum_i h_t(x_i)^2-\frac1n\left(\sum_i h_t(x_i)\right)^2 .
$$
For any finite nonpole with $V_x(t)=V_y(t)$, take $f=h_t-m$, where $2nm=\sum_i h_t(x_i)+\sum_i h_t(y_i)$. The lists $f(x),-f(y)$ have equal sums. Their sums of centered squares are equal by the variance identity; the change of sign preserves centered squares. Hence their sums of squares agree and Newton's identity gives equal $e_2$. All changes preserve MOC by covariance.

To produce such a normalization, put $V_x-V_y$ over the denominator $\prod_i(t-x_i)^2(t-y_i)^2$. Each pole has genuine double coefficient $\pm(1-1/n)$, so the numerator is nonzero at all $2n$ listed points. If it is nonconstant, any complex root gives the required pole. If it is constant, $V_x-V_y=O(t^{-4n})$. The coefficient of $t^{-4}$ in $V_x$ is $\sum_i x_i^2-(\sum_i x_i)^2/n$, by expanding $h_t$ at infinity. This coefficient agrees for $x,y$, so the affine map $f(u)=u-(\sum_i x_i+\sum_i y_i)/(2n)$ gives both equalities directly. Density handles coincidences after MOC is transported back to the original coordinates.

## Three points on a line and four in general position

**U, AP, AQ.** The affine chart $z\mapsto(z-p)/(q-p)$ sends a line through distinct $p,q$ to the real axis. Hence AQ is empty and AP includes the entire collinear-triple stratum. More strongly, if four distinct points are nonconcyclic, take the generalized circle through the first three. A fractional linear map with pole on this circle away from all spectral points sends the triple to a line and the fourth off it. Thus proving U or AP with arbitrary second spectrum would give the entire order-four assertion for each fixed relative unitary, using density or the known generalized-circle case at the exceptions. Affine normalization by itself gives no determinant bound for the fourth point. [Generalized-circle proof](../MOC4_Hermitian_Proof.md)

**AB and AC.** Interpret the stated bisector as the perpendicular bisector of a pair of the three collinear points. In the chart above let $p,q,r\in\mathbb R$ and $w\notin\mathbb R$. The real fractional linear map $h(z)=(z-p)/(z-q)$ sends the pair to $0,\infty$. Multiply $h$ by a real factor of absolute value $1/|h(w)|$, then apply $v\mapsto(v-1)/(v+1)$. This composition sends the pair to $-1,1$ and $w$ to the imaginary axis. Choose the sign so the third real point stays finite. The intermediate infinity at $q$ is removable in the composition. Hence the pairwise-bisector version of AB also contains representatives of all generic problems. Off the finitely many bisectors of pairs, AC holds on a dense subset of the normalized parameter space, since $w$ is free to move off these lines. If “bisector of the triple” means equidistant from *all three* distinct collinear points, its locus is empty. Additional “symmetry loci” require an explicit definition.

**AN and AO.** For four nonconcyclic points interpret the circle as the circumcircle of the first three noncollinear points. A similarity makes it the unit circle. If the fourth point is outside, apply $z\mapsto1/z$. With the fourth point now $w$ in the disk, the map $z\mapsto(z-w)/(1-\bar w z)$ takes it to the center and preserves the circle. The poles can be avoided in the second spectrum by approximation, and if the fourth point was the center to begin with the similarity alone suffices. A normalized triple of distinct points on the unit circle and its center have a collinear triple precisely when two boundary points are antipodal. Perturb the three boundary arguments slightly to avoid this finite union of constraints. Use the inverse map and closedness to remove that perturbation. Thus the center interpretation of AN with arbitrary second spectrum is sufficient for unrestricted order four. For AO perturbing the fourth point away from the center suffices. If any of the four might serve as center, the finitely many extra circumcenter conditions can likewise be avoided. Four nonconcyclic points have no circle passing through all four.

## A single fixed parabola already suffices

**F, order four.** It suffices to settle the requested inclusion on the one real parabola $P=\{p(t)=t+i t^2:t\in\mathbb R\}$ for every relative unitary outside the spin image. For a generic first spectrum, the preceding fractional linear chart followed by a similarity puts its first three points on $\Re z=1$ and the fourth on $\Re z=-1$. For each target $\epsilon+i y$ on these lines, $\epsilon=\pm1$, put $s=y/(2\epsilon)$. Then
$$
 \frac{p(\epsilon T+s)-iT^2}{T}
   = \epsilon+i y+\frac{s+i s^2}{T}
   \longrightarrow \epsilon+i y.
$$
These approximants are all on the same affine image of $P$ and are distinct for large $T$. On each approximating pair use the inverse affine change on *both* spectra. F for $P$ therefore gives inclusion for the approximating first spectrum and the fixed normalized second spectrum. Take the limit and undo the original chart. The relative unitary stays fixed throughout. Generic pairs are dense. If F is assumed only off the spin image, one can also approximate units in that image by a scalar phase times the same unitary outside $SU(4)$, with exactly the same conjugated matrix. This proves equivalence with full order-four MOC, without proving either conjectural statement. This proof uses the two branches of the parabola seen at large height.

**Order five.** If F is generalized to five distinct first eigenvalues on $P$, even that single-parabola assertion would imply all of order five. For five generic points take a triangle with empty open circumdisk and neither remaining point on its boundary. Such a triangle is the projection of a lower facet of the convex hull of the lifted points $(x,y,x^2+y^2)$. Its supporting plane gives the empty-circle inequality by completing squares, and genericity excludes four coplanar lifted points. Map the exterior of the circumcircle to the upper half-plane by a fractional linear transformation. Its three boundary points become real projective points. The other two become $u=x+iy,v=X+iY$, with $y,Y>0$. A real fractional linear transformation makes their imaginary parts equal. If $y\ne Y$, use $-1/(z-t)$, where $t\in\mathbb R$ solves
$$
 y((X-t)^2+Y^2)=Y((x-t)^2+y^2).
$$
The discriminant is $4yY((X-x)^2+(Y-y)^2)>0$. If $y=Y$ the identity works. For generic data no required pole coincides with one of the three boundary points or the other spectrum. To see this, after fixing the first chart and $u,v$, each forbidden boundary coincidence restricts one of three freely variable real boundary points to a finite set. The initial chart may be chosen finite at all five points. The two parallel lines can now be sent by a similarity to the lines used above. Apply the same limit and closedness argument. This conclusion concerns all five spectral points on one parabola and an arbitrary second spectrum.

## Cross-ratios, ordering, and limits

Use $\lambda=(z_1-z_3)(z_2-z_4)/[(z_1-z_4)(z_2-z_3)]$. For distinct points it avoids $0,1,\infty$. It is real exactly on generalized circles, as seen by mapping three points to $0,1,\infty$ projectively. In particular nonreal cross-ratio occurs in *both* $S_{L_3}$ and $S_{G_4}$. An affine map generally cannot normalize three complex positions; a common fractional linear map can. Its common multiplier is the one derived above.

| Requests | What the cross-ratio proves |
| --- | --- |
| V, Y | With the first three points fixed the fourth varies by a nonconstant fractional linear bijection in $\lambda$. Thus the nonreal values off $\lvert\lambda\rvert=1$ are already dense in the nonconcyclic stratum. Y with arbitrary second spectrum and unitary would imply the general assertion by closure. V retains the unrestricted determinant bound. |
| Z, AA | Each of the algebraic nonreal values and transcendental nonreal values is dense in $\mathbb C$. For instance use $\mathbb Q+i\mathbb Q$ off the real axis for the first, then use countability of algebraic numbers for the second. Hence each requested universal subcase by itself implies full order four. If *both* spectra are restricted in this way, perturb their fourth coordinates independently. |
| W, X, AR | Pure-imaginary, unit-modulus, and orbit-of-$i$ values give smaller sets. $i$ belongs to all three. No determinant inequality follows here for every pair on any of these loci. |
| AS, BJ | The anharmonic orbit consists of $\lambda,1/\lambda,1-\lambda,1/(1-\lambda),\lambda/(\lambda-1),(\lambda-1)/\lambda$. These are exactly the values under permutations, allowing coincidences. For $i$ the orbit is $i,-i,1-i,1+i,(1+i)/2,(1-i)/2$. It and its complement partition the ordered parameter, and each is invariant under relabeling. The complement is dense, so AS by itself suffices for general MOC. |
| BI, BX | The algebraic/transcendental split and the nonreal unit-modulus/non-unit-modulus split are each disjoint and exhaustive on their specified domains. The listed W–AA families together overlap, even for a fixed ordering. Pure-imaginary and unit-modulus tests depend on ordering; for example $1-i$ and $i$ represent the same unordered orbit. A collision may make the defining ratio $0,1,\infty$, or undefined. The original determinant formulation still applies there by continuity. |

**BA, BK, BV, BW.** On four distinct nonconcyclic points, testing whether a collinear triple exists gives an exhaustive disjoint dichotomy under the definitions above. The unit square and a quadruple with a repeated point lie outside this restricted partition. Repeated points in order four leave at most three distinct values, all on a generalized circle. For a pair of spectra with at least one generalized-circle spectrum, the repository's one-sided order-four theorem applies. On the remaining pairs record both types, or distinguish “at least one collinear triple” from “neither spectrum has one.” The no-three-collinear, nonconcyclic configurations are dense in all finite spectral configurations. Each excluded equality is the zero set of a nonzero real polynomial (coincidence, collinearity determinant, or the four-point circle determinant). Consequently a theorem on the entire dense stratum extends through collinear, repeated, finite circle and line limits, including zero eigenvalues. A theorem only on the boundary does not imply inclusion in its interior. [One-sided theorem](../MOC4_Hermitian_Proof.md)

## Every simple spectrum has open sets of partners for all relative unitaries

**Theorem.** Fix *any* four distinct complex numbers $b_j$. In the family of first spectra $a$ obtained by varying a finite circle and four positions on it, an open dense set of parameters gives 24 products $z_p$ with no three collinear. At each such pair $(a,b)$ there is an open neighborhood in the full space $\mathbb C^4\times\mathbb C^4$ on which MOC holds for every relative unitary. In particular this gives partners with two nonconcyclic spectra for **every prescribed nonreal cross-ratio**, including the loci W, X and AR. The partners form an open set, and the statement quantifies over every unitary simultaneously. [Spectral stability theorem](../moc4_open_spectra.md)

**Proof.** Fix three distinct permutations $p,q,r$. There are six choices of a pair of rows to collapse to a common value $t$. Two permutations induce the same assignment on the two remaining rows only if they differ by swapping the collapsed rows. Each of the three pairs of permutations forbids at most one choice of collapse. Choose one of the other row pairs, and label the two remaining rows as the $s$-row and the $u$-row. On this subspace each of the three permutation products has the form
$$
 F_{jk}(t,s,u)=
 \prod_{\ell\notin\{j,k\}}(t+b_\ell)\,(s+b_j)(u+b_k),
$$
with three distinct ordered pairs $(j,k)$. Regard this as a pure tensor of a quadratic polynomial in $t$, a linear polynomial in $s$ and a linear polynomial in $u$. Distinct ordered pairs give nonproportional factors in at least two positions. Indeed a swap changes both linear factors, and changing the unordered pair changes the monic quadratic and at least one linear factor. This uses the distinctness of the $b_j$.

Any three such tensors are linearly independent. To prove it, flatten a linear combination of two along one factor in which they differ. Both factor vectors are linearly independent on that side; their complementary tensors are linearly independent because another factor also differs. A combination with both coefficients nonzero then has matrix rank two and cannot equal the third tensor, which has rank one. No two of the tensors are proportional.

It follows that $(F_p-F_q)/(F_p-F_r)$ is a nonconstant rational function of the three complex variables. On its domain it takes a nonreal value, by restriction to a complex line of nonconstancy and the open mapping theorem. Perturb the three variables if necessary to keep the values nonreal and the three points $t,s,u$ distinct and noncollinear. They lie on a finite circle, as does the collapsed first spectrum $(t,t,s,u)$ up to ordering. Thus the real oriented area of this chosen triple of products is nonzero for some parameters of the form $a_j=c+R e^{i\theta_j}$.

This area is a real-analytic function on the connected parameter space $\mathbb C\times(0,\infty)\times\mathbb R^4$ of $(c,R,\theta_1,\ldots,\theta_4)$. Its nonzero set is open dense, including parameters with distinct positions. Intersect over all triples of permutations. On that open dense intersection every triple has nonzero area, so all 24 products are distinct, their hull has interior and every exposed edge has exactly two products. The concyclic first spectrum supplies the singleton property in the cited stability theorem. Its conclusion allows independent perturbations of all eight coordinates, including perturbations of $a$ off the circle with $b$ held fixed. This proves the claim.

## An exact open neighborhood for W, X and AR

In the sum convention set
$$
 x=(-6,-3,1,2),\qquad b=(-1-i,\ 4-i,\ -1+4i,\ 1).
$$
The ordered cross-ratio of $b$ is exactly $i$. MOC holds for **every** relative unitary when each of the eight coordinates of $(x,b)$ moves by at most $10^{-6}$. Keeping $b$ fixed therefore gives a whole polydisc of second spectra for each of W, X and AR, upon swapping the two matrices. More generally, the same conclusion holds on the intersection of the eight-coordinate polydisc with the desired cross-ratio locus.

Here is the finite certificate for the stated radius. Write $z_p=\prod_j(x_j+b_{p(j)})$, with permutations in zero-based one-line notation. The 24 distinct Gaussian integers have the following counterclockwise cycle of exposed edges. For each edge $p,q$, the second row is the minimum over $r\ne p,q$ of $\Im(\overline{z_q-z_p}(z_r-z_p))$.

| Edge starting at | 0213 | 2013 | 3012 | 3021 | 3201 | 3210 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Minimum slack | 20880 | 35360 | 15900 | 22400 | 7200 | 19200 |

The underlying real spectrum $x$ gives the singleton property used by the spectral stability theorem. Each successive pair in the cycle differs by a transposition, including the edge closing the cycle. The theorem's transposition-edge bound permits perturbing all area slacks by at most $7200/44$. The largest squared factor modulus is $65$, and the squared vertex diameter is $1114640<1060^2$. If every spectral coordinate moves by at most $\epsilon=10^{-6}$, each factor stays below $10$ in modulus and moves by at most $2\epsilon$. Telescoping the four factors bounds each vertex displacement by $R=8\cdot10^3\epsilon$. Bilinearity bounds the change of each oriented area by $4R(1060+R)<7200/44$. All edge inequalities therefore hold for all relative unitaries throughout the indicated closed polydisc. [Stability theorem](../moc4_open_spectra.md) · [Exact arithmetic verifier](../../Code/verify_moc4_open_spectra.py)

For an instance with both spectra in $S_{G_4}$, leave $b$ fixed and take $a_j=x_j+i\eta x_j^2$ with $\eta=10^{-8}$. The second spectrum has no collinear triple by inspection of its four coordinates. The first lies on a parabola, so no three points are collinear. A circle through all four would give the real polynomial $\eta^2 t^4+c_2t^2+c_1t+c_0$ with roots $x_j$ by substitution into the circle equation. Its cubic coefficient vanishes but $\sum_j x_j=-6$. This contradiction excludes concyclicity. Since $36\eta<10^{-6}$, the inclusion follows for every $W$.

These reductions leave a concrete inequality. For arbitrary normalized second spectrum $c$, relative unitary $W$, and unit complex $q$, one still needs
$$
 \Re\!\left(\bar q\det(D_a-WD_cW^*)\right)
 \le \max_{\pi\in S_4}\Re\!\left(\bar q\prod_i(a_i-c_{\pi(i)})\right).
$$
Fractional linear covariance, density, and the cross-ratio partitions alone do not establish this bound. The repository gives particular open sets on which it holds for every relative unitary. [Explicit spectral neighborhood](../moc4_open_spectra.md)

# Regular relative eigenbases and unrestricted order four

Write \(D_a=\operatorname{diag}(a_i)\), \(d(a,b,W)=\det(D_a+WD_bW^*)\), and \(z_\pi=\prod_i(a_i+b_{\pi(i)})\). A regular special unitary has four distinct **eigenvalues**. We use \(G_4\) for a simple quadruple with no collinear triple and no generalized circle through all four points. The density arguments below still apply if this generic condition is imposed on both lists. For \(L_3\) we specify explicitly which list has a collinear triple. Let \(K=\operatorname{Sym}^3(SU(2))\) in its unitary realization.

## Every pair admits a regular representative

Left and right diagonal rephasings of \(W\) preserve \(d\). In fact any \(W\in U(n)\) can be made regular by left diagonal rephasing alone. Here is a constructive proof. If \(\lambda\) is repeated, choose a coordinate vector \(e_i\) whose projection onto its eigenspace is nonzero. Replace \(W\) by \(W_q=(I+(q-1)e_ie_i^*)W\) for \(|q|=1\). With \(P_\mu\) the spectral projections of \(W\), the matrix determinant lemma gives
\[
\frac{\det(xI-W_q)}{\det(xI-W)}
=1-(q-1)\sum_\mu\frac{\mu\,\|P_\mu e_i\|^2}{x-\mu}.
\]
For \(q\ne1\) the pole at \(\lambda\) is simple, so its multiplicity drops by exactly one. For \(q\) sufficiently close to one, initially distinct eigenvalue clusters stay separated and retain their total multiplicities. The cluster at \(\lambda\) therefore gains a distinct eigenvalue. At most \(n-1\) steps suffice. Finally multiply by a scalar phase to set determinant one. Thus for fixed spectra the MOC statement for regular representatives is **equivalent** to the one for arbitrary representatives.

The centralizer in \(SU(4)\) of a regular matrix consists of the determinant-one diagonal phases in its eigenbasis, a maximal torus (AE). Every unitary has \(W^*W=I\), so all four singular values equal one. AF is empty. AG and BT cover every regular unitary and every unitary, respectively. Neither repeated singular values nor regularity imposes a restriction on the original normal pair.

## Reduction to O and CA

For unit \(\eta\) set
\[
g_\eta(a,b,W)=\max_\pi\operatorname{Re}(\eta z_\pi)-\operatorname{Re}(\eta d(a,b,W)).
\]
MOC is equivalent by planar convex separation to \(g_\eta\ge0\) for every \(\eta\). The finite maximum is continuous jointly in spectra, unitary and direction, including ties and zero products (BQ). In particular every strict violation persists on an open neighborhood for a fixed direction.

The \(G_4\) quadruples form a dense open set. Exclude the finitely many collisions, zero oriented triangle areas, and the vanishing of the four-row determinant with rows \((1,\operatorname{Re}a_i,\operatorname{Im}a_i,|a_i|^2)\). Each exclusion is a proper real algebraic set. Perturb both spectra into this open set and take limits. Together with the exact regular gauge this proves that **O implies unrestricted order-four MOC** (AY, AZ); the converse is immediate. This also handles either or both spectra on the boundary, including zero entries and collisions.

Similarly CA is equivalent to unrestricted order four. The orbit of \(K\) under left and right diagonal phases and permutations is compact, with real dimension at most \(4+3+4=11\) in the 16-dimensional group \(U(4)\). This follows by smooth parametrization and the finitely many permutations. Its intersection with \(SU(4)\) has empty interior there as well, since \(\dim SU(4)=15\). Regular elements are open dense (one can perturb eigenphases in a diagonalization and preserve determinant). Hence regular elements outside this compact orbit are dense. Any strict counterexample survives perturbation into CA. For the reverse inclusion, CA only specializes MOC. This argument works for either diagonal-only or monomial gauge.

For **K** in the list of questions, suppose only one spectrum is required to have a collinear triple. This too already implies unrestricted MOC. For any nonconcyclic simple quadruple, select the generalized circle through its first three points. A common fractional linear map \(T\) with pole on that circle, avoiding all the entries of \(a,-b\), carries those three points onto a line and the fourth off it. Replace \(a\) by \(T(a)\) and \(b\) by \(-T(-b)\). The determinant and all products acquire the same nonzero complex factor by the resolvent identity for differences, so hull membership is equivalent. For example, \(T(z)=1/(z-p)\) gives the matrix identity \(X^{-1}-Y^{-1}=X^{-1}(Y-X)Y^{-1}\) with \(X=D_a-pI,\ Y=-WD_bW^*-pI\). The common factor is \((-1)^n/(\det X\det Y)\). Rephase \(W\) to be regular and use density to include exceptional spectra. If triples are required on *both* lists, a shared pole on both chosen circles is an additional condition.

## What perturbation proves

Every regular unitary belongs to the closure of the regular set, as does every block matrix. The same conclusion holds near the spin subgroup. The reverse approximation claimed as a potential strategy in AT and AU does not hold. The spin subgroup with its phase and permutation gauges is closed and has empty interior as above. The coordinate block families after relabeling have a prescribed zero pattern, even after rephasing. Their finite union is closed and misses every entrywise nonzero unitary. In particular some regular elements have positive distance from both families. A perturbative proof starting at either family needs a further estimate along a path to such elements.

Equality at a supporting line can disappear along arbitrarily small regular perturbations (BH). Take \(a_j=j\), \(b_j=5-j\), \(1\le j\le4\), and \(\eta=1\). The identity product is \(5^4\) and uniquely maximizes the products by the arithmetic-geometric mean inequality, since all four factors are positive with sum 20. Replace these entries by \(a_j=j+i\epsilon j^2\) and \(b_j=(5-j)+i\epsilon(5-j)^2\) for sufficiently small positive \(\epsilon\). Strict maximality of the real part survives. Both lists are now in \(G_4\): a line meets this parabola in at most two points, and the intersection polynomial with any circle has degree four, zero cubic coefficient, and therefore cannot have roots \(1,2,3,4\). Take \(W_0\) diagonal in \(SU(4)\) with distinct phases. Then \(d=z_{\mathrm{id}}\). Multiply \(W_0\) on the right by a real rotation of angle \(t\) in coordinates 1 and 2. Direct expansion of that block gives
\[
d=\cos^2(t)z_{\mathrm{id}}+\sin^2(t)z_{(12)}.
\]
For all sufficiently small nonzero \(t\), the unitary remains regular and \(g_1>0\). Thus continuity transfers weak inequalities to limits; it does not propagate equality or give a global inequality from boundary equality checks (AX). For the proposed boundary in BM, regular matrices occur even *inside* the block families. If boundary means approximating a block element by nearby regular elements outside those families, that density follows from their zero patterns and the density of regular elements.

For BN, BO and BP one must specify an equality. Every actual tuple \((a,b,W,\eta)\) with \(g_\eta=0\) already has the normal realization \(A=D_a,B=WD_bW^*\). The preceding diagonal example realizes equality in O. Taking \(W=I\in K\) realizes equality in the spin case. Taking \(\epsilon=0\) realizes equality with line spectra. For two circle spectra one can also take the four fourth roots of unity on each side and use \(W=I\). The identity vertex has absolute value 16, all others have strictly smaller modulus, and the radial supporting line realizes equality. If “equality case” means formal solutions of an auxiliary system of equations, realizability instead requires the system and its constraints to be specified.

## Group and spectral boundaries

BB fails as a disjoint partition. The image under \(\operatorname{Sym}^3\) of \(\operatorname{diag}(e^{it},e^{-it})\) has eigenvalues \(e^{3it},e^{it},e^{-it},e^{-3it}\), all distinct for generic \(t\). It belongs to both \(K\) and the regular set. If \(M_{\mathrm{other}}\) has no specified definition, its coverage cannot be inferred.

For BD, the named symplectic and block groups do not exhaust the maximal connected proper subgroups. The standard \(SO(4)\subset SU(4)\) acts irreducibly on \(\mathbb C^4\). No nonzero alternating form is invariant: any invariant form commutes, in the standard coordinates, with all real rotations, hence is scalar by irreducibility. It therefore lies in no conjugate block subgroup or conjugate \(Sp(2)\). It is maximal connected since
\[
\mathfrak{su}(4)=\mathfrak{so}(4)\oplus i\,\mathrm{Sym}^2_0(\mathbb R^4)
\]
and the traceless real symmetric summand is irreducible under orthogonal conjugation by \(SO(4)\). Indeed diagonalize any nonzero element of an invariant subspace. Subtract its conjugate with two unequal diagonal entries swapped (a signed permutation of determinant one suffices); permutations of the difference span the traceless diagonals, and plane rotations then give every off-diagonal symmetric elementary pair. Irreducibility of the standard complex representation used above also follows from the diagonal sign changes of determinant one, which separate the four coordinate characters, and signed permutations, which act transitively on them. If “other” was intended to include all further maximal subgroups by definition, that convention gives no new MOC bound.

For BS an order-four spectrum with repetition has at most three distinct points, all on a generalized circle. The one-sided line-or-circle theorem therefore proves MOC for every eigenbasis in this case. For BU, a zero eigenvalue by itself costs no generality: replace \((a,b)\) by \((a-a_1,b+a_1)\). The matrix sum and all vertices stay fixed. If both sides have zero, the sum of the two ranks is at most six and the rank-sum theorem applies in order four. If an entire spectrum is zero, all products coincide with the determinant. [Proofs of the rank and generalized-circle theorems](../MOC_progress.tex)

## A real arithmetic test for the remaining inequality

The repository's minor-profile decomposition expresses \(d(a,b,W)\) as a convex combination of at most four values \(d(a,b,R_k)\) with \(R_k\in SO(4)\), for the *same* spectra. Thus a strict support violation forces a strict violation at some real rotation. [Minor-profile decomposition](../theorems/profile_geometry/verified_results.md)

Consequently a strict violation would admit the following more specific witness for AV, AW and CA:

1. Both ordered spectra have Gaussian integer entries, lie in \(G_4\) and have no zeros.
2. The relative matrix is \(R=(I-S)(I+S)^{-1}\) for a **rational real skew-symmetric** \(4\times4\) matrix \(S\); \(R\) has distinct eigenvalues and lies outside the spin gauge orbit.
3. Every one of the 24 inequalities \(\operatorname{Re}(d(a,b,R)-z_\pi)>0\) holds.

To prove this, absorb the separating direction \(\eta\) by multiplying all eight eigenvalues by a common fourth root of \(\eta\). Choose a real violating rotation by the cited theorem. Within the open set of violations, perturb the rotation to be regular and to avoid eigenvalue \(-1\); small perturbations of its two rotation angles suffice. The inverse Cayley map \(S=(I-R)(I+R)^{-1}\) is skew-symmetric. Approximate its six free entries by rationals. Approximate both spectra by generic elements of \(\mathbb Q(i)^4\), preserving the strict inequalities, then clear their denominators with a common positive integer. Any violating matrix is automatically outside the spin gauge orbit by the spin theorem and invariance under relabeling. Conversely such a witness violates MOC by the real supporting functional. The proof of this equivalence does not require a uniform distance from the hull boundary.

There is an explicit polynomial test with six rotation parameters. Set \(\delta=\det(I+S)>0\) and \(N=(I-S)\operatorname{adj}(I+S)\). The positivity follows by grouping conjugate eigenvalues of real skew \(S\). Since \(\det R=1\), right multiplication by \(R\) gives
\[
d=\det(D_a R+ R D_b)=\delta^{-4}\det\big[(a_i+b_j)N_{ij}\big]_{i,j=1}^4 .
\]
The 24 conditions are therefore \(\operatorname{Re}(\det[(a_i+b_j)N_{ij}]-\delta^4z_\pi)>0\), polynomial in 22 real unknowns. One can further reduce the spectral parameters. On a dense set the unique Möbius transformation taking \((a_1,a_2,a_3)\) to \((-1,0,1)\) has no pole among the eight signed points. Indeed the first three images are finite, and collisions of its pole with any remaining entry exclude only finitely many choices of that entry. Apply it simultaneously to the two signed spectra as above. The common complex multiplier changes the separating direction, so include a variable for that direction. Up to a positive multiplier each direction has the form \(\pm1+iu\) or \(\pm i\). With these four alternatives the search takes at most 17 real unknowns: six rotation parameters, the real and imaginary parts of five free spectral entries, and \(u\). Strict violations persist under approximation by rationals in these charts. Every violation found there returns directly to the original problem, since these are actual finite spectra. Cases O, AG, AE, CA and one-sided K require showing this feasible set is empty. Its emptiness has not been established here.

The existing cofactor-hull lemma eliminates the free fourth point and the support phase exactly. We give its short proof in the finite normalization used here. [Original cofactor-hull derivation](../research/moc_four_dimensional_cofactor_hull_20261031.txt) Put \(a=(-1,0,1,t)\) and fix the signed partner spectrum and the rotation. Write
\[
d(t)=h\,t+k,\qquad z_\pi(t)=h_\pi t+k_\pi .
\]
Then MOC for **every** complex \(t\) is equivalent to
\[
(h,k)\in\operatorname{conv}_{\mathbb R}\{(h_\pi,k_\pi):\pi\in S_4\}\subset\mathbb C^2.
\]
The forward implication follows by separation. A separating real functional has the form \(\operatorname{Re}(s h+w k)\). For \(w\ne0\), evaluate the scalar separation inequality at \(t=s/w\) in direction \(w/|w|\), giving a contradiction. For \(w=0\), perturb \(w\) to a small nonzero value while retaining strict separation. Conversely, any convex representation of the coefficient pair works after evaluation at each \(t\). This proves that five supported permutations always suffice simultaneously for a whole such pencil *if* the unrestricted conjecture holds, by Carathéodory in four real dimensions. At a specified rotation and partner the remaining obligation is an ordinary linear feasibility problem with 24 nonnegative unknowns and five real equality constraints, obtained from the coefficients at \(t=0,1\). Its universal validity still needs a proof.

## An exact open family outside the spin orbit

The preceding test gives a uniform positive result beyond the block cases. Take
\[
R=\frac1{51}\begin{pmatrix}
-37&16&20&-24\\-8&-31&-26&-30\\-12&30&-39&6\\32&22&2&-33
\end{pmatrix},\quad b=(1+i,2-i,-1+2i,-2-2i).
\]
Then MOC holds for **every** \(a=(-1,0,1,t)\), \(t\in\mathbb C\), with this relative unitary. It also holds for every such \(t\) simultaneously when \((b,R)\) varies throughout a neighborhood in \(\mathbb C^4\times U(4)\).

Here is a rational certificate. Use the five permutations in one-line, one-based notation \(1234,1243,3421,4312,4321\). Their five columns \((1,\Re h_\pi,\Im h_\pi,\Re k_\pi,\Im k_\pi)^T\) form the following matrix. The same coefficients of the actual determinant form the vector on the right:
\[
M=\begin{pmatrix}
1&1&1&1&1\\
-4&3&24&18&17\\
2&-4&-8&-1&-19\\
12&5&32&35&36\\
4&10&16&-20&-2
\end{pmatrix},\qquad
g=\begin{pmatrix}1\\2084/867\\-9706/2601\\47728/2601\\428/153\end{pmatrix}.
\]
These entries follow by evaluating the determinants and products at \(t=0,1\) and subtracting for the slopes. Direct multiplication gives
\[
M^{-1}g=\frac{(13359257,879638,462132,217210,4909186)^T}{19827423},\qquad\det M=182952.
\]
All five entries are positive. The same probabilities therefore give the identity for all complex \(t\). For nearby \((b,W)\), the columns and target depend continuously on the parameters, \(M\) stays invertible, and all five weights stay positive. This proves the neighborhood assertion without a bound depending on \(t\).

For checks on scope, multiplication gives \(R^TR=I\), \(\det R=1\), and \(\det(xI-R)=x^4+(140/51)x^3+(194/51)x^2+(140/51)x+1\). Its two values of \(x+x^{-1}\) are \((-70\pm4\sqrt{13})/51\), distinct in \((-2,2)\), so \(R\) is regular. In the standard spin weight basis every spin matrix has \(|W_{ij}|=|W_{5-i,5-j}|\), by commutation with the conjugate-linear quaternionic structure that exchanges opposite weights. Every modulus therefore has even multiplicity, a property preserved by diagonal phases and permutations. In \(R\), the value \(37/51\) occurs once. Thus it lies outside the compact spin gauge orbit, and the neighborhood can be chosen disjoint from that orbit and the closed block families.

There is an independent obstruction to one law matching all squared minors at this very rotation. With one-based row and column sets, define
\[
F=|R_{21}|^2+|R_{43}|^2+|\det R[34,14]|^2-|\det R[23,12]|^2.
\]
For any permutation matrix, a negative contribution would require rows 2 and 3 to occupy columns 1 and 2. If row 2 takes column 1 then the first singleton contributes. Otherwise row 3 takes column 1, and row 4 must take either column 3 (second singleton) or column 4 (positive minor). Thus \(F\ge0\) for every permutation. Substituting the displayed \(R\) gives \(-20/867\), so its entire minor profile lies outside the permutation hull, even throughout a sufficiently small neighborhood. The five weights above use the specified spectral pencil.

The positive result also includes simple quadruples with no collinear triple on either side. For example apply \(T(z)=1/(z-4i)\) to the signed spectra of this pencil, excluding poles. The transformed partner \(-T(-b)\) has no collinear triple: the four circle determinants with last point \(-4i\) and each sorted triple from \(b\) are \(12,-48,96,120\) in lexicographic triple order. The original four-point circle determinant is 36. The transformed first three points of \(a\) are noncollinear since \(4i\) lies off the real line. When \(t\) avoids the finitely many generalized circles that create degeneracies, the two transformed spectra are both in \(G_4\). By the common-factor identity these are explicit instances of CA as well as K before the transformation. The argument certifies this family; the universal quantifiers in CA remain open.

The exact coefficient identity, simplex determinant, five weights and negative minor facet can be replayed from the repository root with `python3 -B Code/verify_regular_pencil.py`. [Pencil verifier](../../Code/verify_regular_pencil.py)

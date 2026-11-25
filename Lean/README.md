# MOC source guide

Use this guide to find the Lean statement, the proof of a reduction, or the
status of a reformulation. For cases that Lean proves directly, see the
[proved-case list](ProvedCases.md).

## Statement

Let $a$ and $b$ be two ordered spectra of length $n$. Let $U$ be the unitary matrix that relates their eigenbases. The proposition `MOC.Holds a b U` states the inclusion below. [Definitions](MOC/Core.lean)

$$
\det\bigl(\mathrm{diag}(a)+U\mathrm{diag}(b)U^*\bigr)
\in \mathrm{conv}_{\mathbb{R}}
\left\{\prod_{j=1}^{n}(a_{\sigma(j)}+b_j)\mid\sigma\in S_n\right\}.
$$

`MOC.Conjecture (Fin n)` states the inclusion for all spectra and relative unitary matrices of order $n$. `MOC.MOCIsTrue` states the inclusion for every finite order. [Claim](MOC/Claim.lean)

## Equivalent forms and reductions

Each result below states an equivalence or gives a restriction that is enough for a proof.

| Reduction | Lean source |
| --- | --- |
| The statement for ordered spectra and a relative unitary is equivalent to the statement for normal matrices with their eigenvalue lists. | [Normal.lean](MOC/Normal.lean) |
| In a positive order, it suffices to prove MOC for spectra with equal traces. | [Core.lean](MOC/Core.lean) |
| It suffices to treat spectra for which all pair sums are nonzero and all matching products are distinct. | [SpectralPerturbation.lean](MOC/SpectralPerturbation.lean) |
| For fixed spectra, it suffices to prove MOC for each relative unitary with no zero entries. One can also impose nonzero pair sums and distinct matching products at the same time. | [FullSupportReduction.lean](MOC/FullSupportReduction.lean) |
| In orders at least four, also fix the first entries of the spectra to 0 and 1, respectively. A proof on this regular slice proves unrestricted MOC. A counterexample on the slice refutes it. | [Anchored.lean](MOC/Reformulations/Anchored.lean) |
| A counterexample of least order has order at least four. No independent row and column permutations give a proper block split of its relative unitary. | [Claim.lean](MOC/Claim.lean) |
| In a counterexample of least order, every row and column has at least three nonzero entries. | [SparseRow.lean](MOC/SparseRow.lean) |
| In a positive order, MOC has an equivalent determinant statement with matching factors $1-x_i y_j$. Set one specified entry of $x$ and one of $y$ to zero. | [Source.lean](MOC/Source.lean) |
| In the rank-one matching kernel, one can additionally set a second row coordinate to 1. This leaves `2n-3` free complex spectral coordinates and still gives an iff. | [ThreeAnchorKernel.lean](MOC/Reformulations/ThreeAnchorKernel.lean) |
| Restrict both spectral lists to trace zero. A shared fractional-linear change and a polynomial Wronskian give the reverse implication. | [NativeLinksCTraceless.lean](MOC/Reformulations/NativeLinksCTraceless.lean) |
| For traceless spectra and fully supported relative unitaries, it suffices to bound the real part of the determinant by the real part of a single matching product. | [TracelessSupport.lean](MOC/Reformulations/TracelessSupport.lean) |
| Order $n+1$ is equivalent to a determinant inclusion in order $n$. Use an $n\times(n+1)$ coisometry to compress the second diagonal matrix. Index the matching products by injections into the second spectrum. | [PrincipalCoisometry.lean](MOC/PrincipalCoisometry.lean) |
| After shifting an opposite eigenvalue pair to zero, the determinant hull test reduces to the overlap of the two spectral support spaces. The reduced comparison uses reciprocal nonzero eigenvalues and an explicit real contraction factor. | [OppositePair.lean](MOC/OppositePair.lean) |
| At each order, the Hermitian-by-normal claim is equivalent to MOC for all pairs with either spectrum on a circle or line. | [HermitianByNormal.lean](MOC/HermitianByNormal.lean) |
| For at most $k$ nonreal partner eigenvalues in arbitrary order, it suffices to prove Hermitian-by-normal MOC in orders at most $k$. | [FiveNonreal.lean](MOC/FiveNonreal.lean) |
| To prove unrestricted Hermitian-by-normal MOC, it suffices to treat orders at least four in which every partner eigenvalue is nonreal. | [FiveNonreal.lean](MOC/FiveNonreal.lean) |
| In order four, MOC is equivalent to the existence of a maximizing normal sum in each direction on each unitary orbit. Requiring such a maximizer in every finite order is equivalent to the unrestricted conjecture. | [NormalSupportMaximum.lean](MOC/NormalSupportMaximum.lean) |
| At a positive Hermitian orbit support maximum with a simple real spectrum, an exact transposition bound relates repeated stationary poles to inverse imaginary minors. A definite partner imaginary part makes the bound strict and forces distinct poles. | [HermitianStationarySwap.lean](MOC/HermitianStationarySwap.lean) |
| In a single complex spectral coordinate, a strict violation can be moved to a maximizer with at least three active permutations if the convex hull of the slopes contains zero in its interior. | [SpectralAffineContact.lean](MOC/SpectralAffineContact.lean) |
| If a fixed unitary and direction give a strict violation in the unit spectral polydisk, some maximum of the support excess there has at least three maximizing permutations. | [PolydiskContact.lean](MOC/PolydiskContact.lean) |
| A nonconstant exact affine profile line that preserves the old complex contact differences must increase the contact count. The determinant gap need not be fixed. | [ContactAffineRigidity.lean](MOC/ContactAffineRigidity.lean) |
| At a balanced Hermitian involution center, the corank is even. The first possible determinant coefficient is exactly the reduced determinant times the kernel-compression determinant. An interior matching-jet certificate yields actual hull inclusion nearby. | [Singular antipodal jets](AntipodalKernelJets.md) |
| Lean reduces terminal support to at least $2n-1$ contacts, with at least $2n-2$ independent contact-difference functions. The [affine cover argument](AffineGapContinuation.md) applies even to exceptional initial points. | [AffineGapCover.lean](MOC/AffineGapCover.lean) · [SharpContactRank.lean](MOC/SharpContactRank.lean) |
| Every violating exact profile is determined by its full vector of pivot differences. Contact differences alone can have another exact point in the same fibre. | [DifferenceProfileReconstruction.lean](MOC/DifferenceProfileReconstruction.lean) |
| An anchored full-rank contact pattern of terminal size gives hull inclusion for all mixers when the spectra are simple and all matching products are nonzero. | [Anchored star and rectangle](AnchoredStarContact.md) |
| In order four, every squared-minor table is a common mixture of two real orthogonal tables. It suffices to prove support for real orthogonal mixers at seven or more contacts. See the [Zheng proof audit](ZhengOrderFourReview.md) ([preprint DOI](https://doi.org/10.13140/RG.2.2.36790.25923)). | [FourMinorTransport.lean](MOC/FourMinorTransport.lean) · [ZhengContactReduction.lean](MOC/ZhengContactReduction.lean) |
| At a contact-maximal strict witness, the pivot-relative contacts jointly cross every nontrivial cut. Connected anchor triples give a separate sufficient support criterion. | [PolynomialProfileContact.lean](MOC/PolynomialProfileContact.lean) · [AnchoredConnectedContacts.lean](MOC/AnchoredConnectedContacts.lean) |
| A one-entry pencil has a common law exactly when conditional slope hulls can meet two complex moment equations. | [GroupedPencil.lean](MOC/GroupedPencil.lean) |
| The squared Frobenius self-commutator of a principal compression equals eight times a spectral covariance determinant, using the deleted row's weights. An imaginary strip gives a quadratic width bound for this squared norm. This does not provide a hull comparison. | [CompressionDefect.lean](MOC/CompressionDefect.lean) |
| It suffices to use Gaussian-integer spectra and unitary mixers with Gaussian-rational entries. Cayley density proves the reduction; no finite search is part of it. | [GaussianCayley.lean](MOC/GaussianCayley.lean) |

`MOC.HermitianByNormal` states the inclusion for real $a$ and complex $b$. The claim for all orders is open. [Hermitian-by-normal statement](MOC/HermitianByNormal.lean)

## Common permutation weights

A fixed set of real weights works for every complex partner spectrum if it works for all partners with entries in $\{0,1\}$. For real $a$, fix one partner entry at a nonreal value. The same weights work for all partners if they work for every complex choice of the other entries. [CommonWeights.lean](MOC/CommonWeights.lean)

Let one entry of each spectrum vary. A fixed set of real weights works for all values if it works at the four pairs formed by two distinct choices on each side. When the fixed entries are real, choose nonreal $s,u$. The two pairs $(s,u)$ and $(s,\bar u)$ suffice. [TwoFreeEntries.lean](MOC/TwoFreeEntries.lean) · [TwoFreeRealAnchors.lean](MOC/TwoFreeRealAnchors.lean)

For a fixed unitary, one set of weights represents the determinant for every pair of spectra if it represents all the following pairs. Choose index sets $I,J$ of the same size, at most $\lfloor n/2\rfloor$. Set the first spectrum to zero on $I$ and one elsewhere. Set the second spectrum to one on $J$ and zero elsewhere. The corresponding determinant is the squared modulus of the minor on rows $I$ and columns $J$. [SubsetMarkerTest.lean](MOC/SubsetMarkerTest.lean)

Start with two lists of order $d$. Count the occurrences of $c$ in the first list and $-c$ in the second list. Let $k$ be the sum of these counts. After adding $m$ copies of these two values, the inclusion holds for every relative unitary if $k+m+2\ge d$. In order four, a case proved for every unitary therefore extends to every larger order if at least one original entry has the specified value. [MarkedPadding.lean](MOC/MarkedPadding.lean)

At order five, a fixed relative unitary can have no single set of nonnegative weights that sums to one and works for every pair of spectra with an opposite eigenvalue pair at fixed labels. [OppositePair.lean](MOC/OppositePair.lean)

Let $a$, $x$, and $v$ be real lists of length $n$. For a partner of the form $x+zv$, the determinant and the matching products are polynomials in $z$. The coefficient of degree $n$ is the same in all these polynomials. The lower coefficients give a convex-hull test for one set of weights for all complex $z$. If the test holds, at most $n+1$ permutations suffice. The explicit order-five theorem takes membership in this hull as a hypothesis. [HermitianSpectralLine.lean](MOC/HermitianSpectralLine.lean)

## Check the library

Run `lake build` from this directory. The root module imports every project module and checks the axioms used by each safe declaration. The check permits `propext`, `Classical.choice`, and `Quot.sound`. [Build instructions](../README.md#build) · [Root module](MOC.lean)

Use `import MOC` in a Lean file in this package. The proofs in the proved-case list are part of this check. To check an individual module, give Lake its module name.

```sh
lake build +MOC.RankTwoOverlap
```

The checked reduction and equivalence API is in `MOC.Reformulations`. Exhaustive ray and permutation certificates are not part of this build.

The [native Lean coverage](MOC/Reformulations/NativeCoverage.lean) records the scope and proof status for atlas entries 001–133. The [native implication audit](MOC/Reformulations/NativeAudit.lean) records the directions and gaps for all 266 entries (243 atlas entries, eleven C★ statements, and twelve named reductions). A labelled spectral equivalence does not establish a reverse implication for the original native object.

The [research directory](research) contains the original reformulations. Research
notes record arguments and open questions outside the checked proof library.

The [contact reduction notes](OrderFiveContactReduction.md) describe
the global curve construction and contact transfer, and distinguish
them from the terminal inequality. The [order-four reduction](MOC/OrderFourIndependent.lean) and
[second-order test](MOC/OrderFourSecondVariation.lean) give necessary
conditions on an order-four counterexample. The [reflection test](MOC/OrderFourReflectionTest.lean)
reduces each real rank-one phase motion to its reflection endpoint.

Use the [proof tree](ProofTree.md) to compare complete routes to the
all-order, order-four, and order-five goals. It distinguishes alternative
proofs from steps that must be proved together.

The [fixed-gap contact reduction](MOC/GlobalContactSlice.lean) is exact
in every order. The [varying-gap reduction](MOC/AffineGapCover.lean)
adds one more contact while preserving the mixer, phase, pivot, and
old complex differences. Every strict witness can reach at least $2n-2$ maximal
matching labels without changing the mixer, phase, pivot, complex
determinant gap, or the original complex contact differences. This
includes witnesses with zero matching products. The profile ring has
[dimension $2n-2$](MOC/ProfileDimension.lean) for $n\ge 2$. The [balanced terminal equivalence](MOC/BalancedContactReduction.lean)
further lets us require a nonnormal orbit maximizer with equal traces
and cubic moments on unit energy and unit direction. The resulting
terminal support bound remains open. The [equation budget](MOC/ContactEquationBudget.lean)
can force a new contact even after the count threshold when the
active equations are redundant.
The [joint rank and moment reduction](MOC/SharpContactRank.lean)
requires at least $2n-2$ independent contact-difference functions and
a quartic spectral bound on the same balanced terminal maximizer.
[Subset incidences](MOC/ContactMarkerRank.lean) detect the linear
relations exactly.
The [isolated-fibre reduction](MOC/ContactFibreIsolation.lean) additionally
requires the exact matching profile to be locally isolated after fixing
the active complex differences and the full complex determinant gap.
This is isolation of the profile, not of the spectra that realize it. The [nonzero-chart reduction](MOC/SaturatedContactReduction.lean)
is also available when the final argument requires nonzero matching
products.

See [the literature notes](Literature.md) for DOIs and for the difference
between published results, preprint claims, and Lean proofs in this library.

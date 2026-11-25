# Marcus–de Oliveira conjecture

Let $A$ and $B$ be complex normal matrices of the same finite order $n$.
A matrix $M$ is normal if $MM^*=M^*M$, where $M^*$ is the conjugate transpose.
Let $a_1,\ldots,a_n$ and $b_1,\ldots,b_n$ be the eigenvalues of $A$ and $B$,
counted with multiplicity. Let $S_n$ be the set of permutations of
$\{1,\ldots,n\}$. For each $\sigma\in S_n$, define the matching product
$P_\sigma=\prod_{j=1}^n(a_{\sigma(j)}+b_j)$.

The conjecture states that

$$
\det(A+B)\in\mathrm{conv}_{\mathbb R}\{P_\sigma\mid\sigma\in S_n\}.
$$

Membership in the real convex hull means that the determinant is a sum of
matching products with nonnegative real weights whose sum is one.
[Conjecture in Lean](Lean/MOC/Core.lean#L33)

## Proof tree

[All orders](#all-orders) · [Equivalent formulations](Docs/Proofs/all-order-proof-maps.md#matrix-and-operator-formulations) · [Atlas audit](Docs/Proofs/all-order-proof-maps.md#atlas-realizations-and-implications) · [Order four](#order-four) · [Order five](#order-five) · [Proved cases](#cases-proved-in-lean) · [Counterexamples](#counterexamples-to-stronger-statements)

The detailed maps cover every registered Lean route and give the
premises and source for each branch.

| Detailed map | Coverage |
| --- | --- |
| [All-order routes](Docs/Proofs/all-order-proof-maps.md) | The order split, 71 general routes, and the audit of 243 spectral entries. |
| [Spectral and support results](Docs/Proofs/spectral-support-proof-map.md) | The order-four cone, real lifts, matching squares, spectral families, attainment, and PDF coverage. |
| [Contact transfer](Docs/Proofs/contact-proof-maps.md) | Fixed and varying determinant differences, terminal counts, rank, moments, and isolation. |
| [Order four](Docs/Proofs/order-four-proof-maps.md) | Eleven registered routes, orthogonal and stationary restrictions, and named contact patterns. |
| [Order five](Docs/Proofs/order-five-proof-maps.md) | Ten registered routes, contact thresholds, sparse matrices, and squared-minor tests. |

The unrestricted Marcus–de Oliveira conjecture (MOC) is open in this
library. Lean proves the unrestricted result through order three.
[General goal](Lean/MOC/Claim.lean#L9) · [Orders zero through three](Lean/MOC/Small.lean#L68)

Some historical proofs remain outside the default target. The new
spectral and support results have source and exact arithmetic checks.
They await Lean compilation. [Source scope](Docs/Proofs/all-order-proof-maps.md#scope-of-the-lean-source)

Choose a unitary eigenbasis for each matrix. In the basis for $A$, write
$A=\mathrm{diag}(a)$ and $B=U\mathrm{diag}(b)U^*$.
Here $\mathrm{diag}(a)$ is the diagonal matrix with entries $a_i$.
The unitary matrix $U$ gives the change between the two eigenbases.
The inclusion in these coordinates is equivalent to the matrix conjecture.
[Proof](Lean/MOC/Normal.lean#L280)

Read the arrows toward the goal. An **iff** arrow gives implications in
both directions. An **if** arrow gives a sufficient condition. At an
**AND** node, all incoming conditions are required. The arrows record
Lean proofs of the relations. A yellow box marks an open statement.
The status tables identify the steps and cases that Lean proves.

### All orders

```mermaid
flowchart BT
    accTitle: Proof routes to unrestricted MOC
    accDescr: The conjunction of all order ranges and any equivalent test each imply and follow from MOC. The separate characteristic coefficients and the simultaneous mixed determinant give sufficient conditions.
    Goal["Unrestricted MOC<br/>Open"]:::goal
    Ranges{{"AND<br/>All order ranges"}}:::join
    Tests["Any equivalent<br/>all-order test"]:::open
    Polys["Separate characteristic coefficients<br/>or simultaneous mixed determinant"]:::open
    Base["Orders 0–3<br/>Proved"]:::proved
    Four["Order 4"]:::open
    Five["Order 5"]:::open
    Higher["Orders 6 and higher"]:::open

    Ranges <-->|iff| Goal
    Tests <-->|iff| Goal
    Polys -->|if| Goal
    Base --- Ranges
    Four --- Ranges
    Five --- Ranges
    Higher --- Ranges

    classDef goal fill:#18344b,stroke:#18344b,color:#ffffff
    classDef join fill:#e7f0fa,stroke:#52779d,color:#142e47
    classDef open fill:#fff3d6,stroke:#9a6516,color:#432e0f
    classDef proved fill:#e3f4e8,stroke:#41905b,color:#163c24
```

Because the base orders are proved, the order split requires proofs in
order four, order five, and every order at least six.
[Order split](Lean/MOC/ProofRoutes.lean#L214)

A **directional bound** compares $\mathrm{Re}(\eta\det(A+B))$ with the
largest $\mathrm{Re}(\eta P_\sigma)$ for a complex direction $\eta$.
A **strict violation** occurs if the determinant projection exceeds that value.
A **contact** is a permutation that attains this largest value. Two
permutations with the same product count as two contacts. The determinant
is in the hull if and only if the bound holds in every direction.
[Directional equivalence](Lean/MOC/Support.lean#L52)

| Relation to unrestricted MOC | Open statement | Lean proof of the relation |
| --- | --- | --- |
| Iff | In orders at least four, prove the directional bound for $\eta=1$ if both eigenvalue lists sum to zero and every entry of $U$ is nonzero. | [Traceless form](Lean/MOC/Reformulations/TracelessSupport.lean#L14) |
| Iff | In each order $n$, prove the directional bound when there are at least $2n-1$ contacts. Another exact test uses at least $2n-2$ contacts and requires every matching product to be nonzero. | [General contact test](Lean/MOC/AffineGapCover.lean#L85) · [Nonzero-product test](Lean/MOC/ProofRoutes.lean#L232) |
| Iff, new Lean source | At the $2n-1$ threshold, exclude a strict maximum over all relative unitaries in which every nonzero mixer entry lies on an inactive permutation with negative real signed weight. | [Terminal stationary test](Lean/MOC/StationaryPivot.lean#L483) · [Signed score identity](Docs/Proofs/contact-proof-maps.md#complex-stationary-score) |
| Iff | For every pair of lists and every direction in orders at least four, some maximizing $U$ gives a normal sum. The maximum is over all unitary $U$ for the fixed lists. | [Normal maximizers](Lean/MOC/NormalSupportMaximum.lean#L314) |
| Iff | In each order, fix $U$ and all eigenvalues except one entry of $b$. Find one set of convex weights on at most five permutations that works for every complex value of that entry. | [One free entry](Lean/MOC/ProofRoutes.lean#L89) |
| Iff | Replace the square unitary by a rectangular matrix with at least three orthonormal rows and one extra column. Compare with products that match the shorter list to distinct positions in the longer list. | [Rectangular determinant bound](Lean/MOC/PrincipalCoisometry.lean#L248) |
| Iff | In orders at least four, use lists $x,y$ with $x_1=0$, $x_2=1$, and $y_1=0$. For every unitary $U$ with no zero entries, place $\det(U-XUY)/\det U$ in the hull of the products $\prod_j(1-x_{\sigma(j)}y_j)$. Here $X=\mathrm{diag}(x)$ and $Y=\mathrm{diag}(y)$. | [Three fixed coordinates](Lean/MOC/Reformulations/ThreeAnchorKernel.lean#L61) |
| Iff, new Lean source | Use normal adjacency matrices of loopless complex weighted directed graphs. Keep all relative unitary positions. | [Loopless adjacency](Lean/MOC/Reformulations/LooplessAdjacency.lean#L23) |
| If, new Lean source | For each index, place the elementary symmetric coefficient of the sum in its matching hull. The weights can depend on the index. The coefficient of index $n$ is the determinant. | [Separate coefficient implication](Lean/MOC/Reformulations/SecondCoefficient.lean#L89) |
| If | Use one set of convex weights for the full polynomial $\det(A+zB)$ and the polynomials from the matchings. Evaluation at $z=1$ gives the determinant. | [Mixed determinant implication](Lean/MOC/Reformulations/NativeLinksA.lean#L237) |

| Status | Result | Lean source |
| --- | --- | --- |
| Proved | A strict violation with at most $2n-2$ contacts can gain a contact by changing the lists. The new violation keeps the same $U$, direction, and previous contacts. | [Contact transfer](Lean/MOC/VaryingGapTerminal.lean#L110) · [Proof of the continuation premise](Lean/MOC/AffineGapCover.lean#L80) |
| Partial | A counterexample of least order has no proper diagonal block split after independent row and column permutations. Each row and column of $U$ has at least three nonzero entries. Every matrix that commutes with both summands is a scalar multiple of the identity. | [Block split](Lean/MOC/Claim.lean#L51) · [Rows](Lean/MOC/SparseRow.lean#L287) · [Columns](Lean/MOC/SparseRow.lean#L309) · [Commuting matrices](Lean/MOC/ReducingCommutant.lean#L70) |
| Partial | For $\det(A+zB)$ in positive order $n$, the separate coefficient bounds hold at degrees $0$, $1$, $n-1$, and $n$. This covers every coefficient through order three. | [First](Lean/MOC/Reformulations/NativeLinksA.lean#L107) · [Penultimate](Lean/MOC/Reformulations/NativeLinksA.lean#L150) · [Endpoints](Lean/MOC/Reformulations/NativeLinksA.lean#L162) |
| Partial, new Lean source | The first three elementary symmetric coefficients of $A+UBU^*$ have one set of matching weights in every order. The weights depend only on $U$. | [Coefficient proof](Lean/MOC/Reformulations/SecondCoefficient.lean#L245) |
| Open | The directional bound at the contact thresholds remains to be proved in general. The order split also leaves every order at least six to prove. | [Contact endpoint](Lean/MOC/AffineGapCover.lean#L85) · [Higher orders](Lean/MOC/ProofRoutes.lean#L214) |

Two iff routes for the same goal imply each other. A sufficient route
implies every iff route for that goal. An all-order route also implies
each iff route at a fixed order. Refuting an iff route refutes its goal.
A sufficient condition can fail while the goal still holds.
[Transfer between routes](Lean/MOC/ProofRoutes.lean#L36) · [Transfer to a fixed order](Lean/MOC/ProofRoutes.lean#L588)

### Order four

```mermaid
flowchart BT
    accTitle: Equivalent tests for order four
    accDescr: The real orthogonal, seven-contact, stationary seven-contact, and normal-maximizer tests each imply and follow from order four.
    Four["Order 4<br/>Open"]:::goal
    Real["Bound for real<br/>orthogonal U"]:::open
    Seven["Bound for real orthogonal U<br/>at 7 or more contacts"]:::open
    Pivots["Exclude stationary violations<br/>at 7 or more contacts"]:::open
    Normal["Find a normal sum at<br/>some maximum in each direction"]:::open

    Real <-->|iff| Four
    Seven <-->|iff| Real
    Pivots <-->|iff| Seven
    Normal <-->|iff| Four

    classDef goal fill:#18344b,stroke:#18344b,color:#ffffff
    classDef open fill:#fff3d6,stroke:#9a6516,color:#432e0f
```

The real orthogonal restriction applies to $U$. The eigenvalue lists
remain complex. Lean proves the restriction by expressing the squared
absolute values of all unitary minors as one finite convex combination
of the corresponding real orthogonal tables.
[Minor decomposition](Lean/MOC/FourMinorTransport.lean#L479) · [Orthogonal equivalence](Lean/MOC/FourMinorTransport.lean#L574)

| Status | Result | Lean source |
| --- | --- | --- |
| Proved | The inclusion holds if one list lies on a circle or a line, if an eigenvalue pair sums to zero, or if $U$ is real orthogonal with zero diagonal. | [Circle or line](Lean/MOC/HermitianByNormalFourProof.lean#L60) · [Opposite pair](Lean/MOC/FourCoincidence.lean#L360) · [Zero diagonal](Lean/MOC/FourZeroDiagonal.lean#L342) |
| Proved | The directional bound holds for specific sets of tied permutations. The pattern labels identify those sets in the linked statements. | [T1](Lean/MOC/ZhengT1Circle.lean#L184) · [T2](Lean/MOC/FourT2Minor.lean#L338) · [T3](Lean/MOC/FourT3.lean#L25) · [T4](Lean/MOC/FourT4.lean#L30) · [T5](Lean/MOC/FourT5.lean#L26) · [T6](Lean/MOC/FourT6Support.lean#L11) · [T15](Lean/MOC/FourT15.lean#L14) · [T21](Lean/MOC/FourT21ContactCone.lean#L275) |
| Partial | It suffices to exclude strict violations at real orthogonal maximizers with at least seven contacts. For each nonzero entry $U_{ij}$, some permutation with $\sigma(j)=i$ does not attain the maximum. Lean proves these restrictions on the same witness. | [Seven-contact reduction](Lean/MOC/ZhengContactReduction.lean#L14) · [Stationary reduction](Lean/MOC/StationaryPivot.lean#L221) |
| New Lean source | Subtract the smallest directional matching value from each projected product. In the 14-dimensional matching-function space, the cone of nonnegative costs has 34 ordinary and 48 mixed extreme rays. An ordinary ray is a subset assignment indicator. Up to relabeling, a cost outside the ordinary cone uses one mixed ray and at most 13 ordinary rays. | [Cone and cancellation](Docs/Proofs/spectral-support-proof-map.md#order-four-support-costs) |
| New Lean source | A determinant of size $n-2$ represents the transformed spectral polynomial for $n\ge2$. In order four its quadratic form has complex rank at most four. Its real form has positive and negative indices at most four. | [Spectral determinant and rank](Docs/Proofs/spectral-profile-determinant-map.md) |
| New Lean source | The four contacts given by the identity and the three products of two disjoint transpositions force an actual spectral cost to be a sum of real matching squares. | [Klein-four contacts](Docs/Proofs/order-four-klein-squares-map.md) |
| New Lean source | The real and imaginary parts of an exact spectral bracket profile satisfy two equations. A small integer example passes the cubic and Hessian kernel tests and fails the second equation for every candidate imaginary part. | [Lift equations](Lean/MOC/FourMatchingHessianKernel.lean#L124) · [Exact obstruction](Lean/MOC/FourMatchingHessianKernel.lean#L166) |
| Partial | For the contact pattern T34, Lean proves the bound at zero common projection. For T85, Lean excludes one branch and reduces the remaining case to at least eight contacts with positive common projection. | [T34 at zero projection](Lean/MOC/FourT34MinorBranch.lean#L145) · [T85 branch exclusion](Lean/MOC/ZhengPairedContacts.lean#L905) · [T85 reduction](Lean/MOC/ZhengPairedContacts.lean#L915) |
| Open | Prove the bound for every remaining real orthogonal case with at least seven contacts. An alternative is to show that a normal sum occurs at some maximum for every pair of lists and direction. | [Contact endpoint](Lean/MOC/ZhengContactReduction.lean#L14) · [Normal-maximizer equivalence](Lean/MOC/NormalSupportMaximum.lean#L303) |

Other exact routes include the test on stationary real orthogonal
violations with one row and one column free of zeros, the one-free-entry
law, and the rectangular test with three rows and four columns.
[Stationary row and column test](Lean/MOC/StationaryDenseCross.lean#L64) · [One free entry](Lean/MOC/ProofRoutes.lean#L89) · [Rectangular test](Lean/MOC/PrincipalCoisometry.lean#L140)

### Order five

```mermaid
flowchart BT
    accTitle: Proof routes to order five
    accDescr: The two tests with no zero entries in U are equivalent to order five. Order four together with normal order-five maximizers also suffices.
    Five["Order 5<br/>Open"]:::goal
    Contacts["Bound at 8 or more contacts<br/>with no zero entries in U"]:::open
    Regular["Bound regular spectra<br/>with no zero entries in U"]:::open
    Both{{"AND<br/>Both premises"}}:::join
    Four["Order 4"]:::open
    Normal["Find a normal sum at<br/>some order-5 maximum<br/>in each direction"]:::open

    Contacts <-->|iff| Five
    Regular <-->|iff| Five
    Both -->|if| Five
    Four --- Both
    Normal --- Both

    classDef goal fill:#18344b,stroke:#18344b,color:#ffffff
    classDef join fill:#e7f0fa,stroke:#52779d,color:#142e47
    classDef open fill:#fff3d6,stroke:#9a6516,color:#432e0f
```

Here **regular spectra** means that all sums $a_i+b_j$ are nonzero and
all matching products are distinct. The eight-contact test in the diagram
uses the condition on the entries of $U$. The separate eight-contact test
in the all-order table uses the condition on the matching products.
[Regular spectra](Lean/MOC/FullSupportReduction.lean#L118) · [Nonzero entries in $U$](Lean/MOC/OrderFiveContact.lean#L51) · [Nonzero matching products](Lean/MOC/SaturatedContactReduction.lean#L63)

| Status | Result | Lean source |
| --- | --- | --- |
| Proved | The all-order contact transfer increases the contact count of a strict violation below eight and keeps the same $U$. This supplies the premise in the equivalence for the eight-contact test with no zero entries in $U$. | [Transfer](Lean/MOC/VaryingGapTerminal.lean#L110) · [Continuation](Lean/MOC/AffineGapCover.lean#L80) · [Eight-contact equivalence with the step premise](Lean/MOC/OrderFiveContact.lean#L97) |
| Proved | The inclusion holds for the order-five discrete Fourier matrix. It also holds if the first spectrum is real and the second has at least one real entry. | [Fourier matrix](Lean/MOC/FourierProfiles.lean#L211) · [Real eigenvalue](Lean/MOC/HermitianByNormalFourProof.lean#L100) |
| Partial | If order four holds, a counterexample in order five has at most seven zero entries in $U$. Under the same premise, order five is equivalent to the existence of normal maximizers. | [Zero count](Lean/MOC/OrderFiveSparseGeometry.lean#L189) · [Conditional equivalence](Lean/MOC/NormalSupportMaximum.lean#L270) · [Order-five implication](Lean/MOC/ProofRoutes.lean#L110) |
| Partial | Lean expresses each directional determinant value through squared absolute values of two-by-two minors. A bound on the associated pair costs certifies the desired inequality when one permutation attains the bound. | [Pair-cost formula](Lean/MOC/OrderFivePairCost.lean#L247) · [Certificate](Lean/MOC/OrderFivePairCost.lean#L284) |
| Open | Prove the general directional bound on the eight-contact test in the diagram. Another exact test uses at least nine contacts with arbitrary unitary $U$. | [Eight-contact test](Lean/MOC/OrderFiveContact.lean#L51) · [Nine-contact test at $n=5$](Lean/MOC/AffineGapCover.lean#L85) |

A further sufficient route needs **both** the bound for order-five real
orthogonal matrices and a decomposition of every unitary squared-minor
table into a convex combination of two real orthogonal tables.
The proposed route through one nonnegative permutation law for all
spectra of every fixed $U$ is refuted in order five.
[Orthogonal transfer](Lean/MOC/ProofRoutes.lean#L203) · [Refuted common-law premise](Lean/MOC/ProofRoutes.lean#L132)

Lean also records further equivalent formulations and sufficient
conditions, including routes through finite representations, matrix
polynomials, and matching problems. The branch lists give the complete
statements and the proof of each connection to its goal.
[All-order branches](Lean/MOC/ProofRoutes.lean#L236) · [Order-four branches](Lean/MOC/ProofRoutes.lean#L169) · [Order-five branches](Lean/MOC/ProofRoutes.lean#L187)

## Cases proved in Lean

### A common law at small shifted rank sum

Fix the relative unitary and a scalar shift. Fix the allowed nonzero
labels in both shifted spectra. If their total number is at most
two above the matrix order, one permutation law works for every
choice of the values on those labels. The law also permits additional
zeros. The new source states this common law in orders at least two.
[Common law](Lean/MOC/RankTwoOverlap.lean#L708) · [Matrix-rank restriction](Lean/MOC/RankTwoOverlap.lean#L723)

### Common weights for all diagonal partners

Fix one list of four eigenvalues. Every normal matrix with this list
has one law that works for all diagonal partners if and only if the
four eigenvalues lie on one circle or line. For a Hermitian matrix of
order four, the law also represents all principal minors together.
Each real linear objective on those minors attains a maximum at a
diagonal permutation of the spectrum.
[Criterion and consequences](Docs/Proofs/circle-line-common-weights-map.md)

### Matrices and eigenvalues

- The inclusion holds in any order if $A+B$ is singular or if $A$ and $B$
  have a common unitary eigenbasis.
  [Singular sum](Lean/MOC/Singular.lean#L417) · [Common eigenbasis](Lean/MOC/Normal.lean#L240)
- The inclusion holds in any order if each eigenvalue list lies on a
  circle or a line. The choice of circle or line can differ between the
  lists. This includes two real lists, lists on parallel lines, and
  lists that each have at most three distinct values.
  [Circles and lines](Lean/MOC/TwoSpectralCircles.lean#L153) · [Real eigenvalues](Lean/MOC/Hermitian.lean#L53) · [Parallel lines](Lean/MOC/Collinear.lean#L62) · [Three distinct values](Lean/MOC/TwoSpectralCircles.lean#L161)
- Let $C$ and $D$ each be a circle or a line. The inclusion holds in
  any order if all $a_i$ lie in $C$ and all $-b_j$ lie in $C\cup D$.
  [Proof](Lean/MOC/TwoCircleCover.lean#L10)
- Suppose all $a_i$ lie on one circle or line $C$. The inclusion holds
  in any order if at most four entries $-b_j$, counted with multiplicity,
  lie outside $C$. It also holds if the entries outside $C$ take at most
  three distinct values.
  [Four entries](Lean/MOC/HermitianByNormalFourProof.lean#L78) · [Three distinct values](Lean/MOC/HermitianByNormalGeneral.lean#L90)
- The inclusion holds in any order if either list has at most two
  distinct values. It also holds if deleting one entry from the second
  list leaves at most two distinct values, or if the first list is
  constant except at up to two positions.
  [Two distinct values in the second list](Lean/MOC/TwoValues.lean#L317) · [Two distinct values in the first list](Lean/MOC/TwoValues.lean#L331) · [One deletion](Lean/MOC/ThreeValues.lean#L14) · [Two exceptions](Lean/MOC/TwoExceptions.lean#L247)
- Partition one spectrum into three fixed groups with the last group
  of size one. For a fixed mixer, one law works for all three group
  values and every opposing spectrum.
  [Common law for three values](Docs/Proofs/three-value-singleton-map.md)
- Under the stated assignment-sum genericity condition, a sufficiently
  small complex spectral parameter gives inclusion uniformly over
  all mixers in the fixed order.
  [Small-spectrum theorem](Docs/Proofs/small-spectrum-perturbation-map.md)
- In order four, the inclusion holds if either list lies on a circle or
  a line. This includes a Hermitian matrix with an arbitrary normal
  partner and the case where either list has a repeated value.
  [Circle or line](Lean/MOC/HermitianByNormalFourProof.lean#L60) · [Hermitian matrix](Lean/MOC/HermitianByNormalFourProof.lean#L55) · [Repeated value](Lean/MOC/TwoExceptions.lean#L287)
- In order four, the inclusion holds if any $a_i+b_j=0$. This includes
  a list paired with its negation. In any order, an opposite pair suffices
  if the sum of its two eigenvalue multiplicities is at least $n-2$.
  [Order four](Lean/MOC/FourCoincidence.lean#L360) · [Negated list](Lean/MOC/FourNegativeCopy.lean#L147) · [Multiplicity bound](Lean/MOC/OppositePair.lean#L25)
- One fixed pair of complex lists of length four satisfies the inclusion
  for every unitary. A weighted-minor inequality certifies two of the
  nine hull edges. One of those edges has no certificate made only of
  nonnegative coefficients on ordinary minor indicators.
  [Spectra and proof](Docs/Proofs/order-four-weighted-minor-center-map.md)
- For an order-four support cost in the symmetric six-contact family,
  the spectral equations force one of three bounds on the minor
  coefficients. Each bound gives the directional determinant inequality
  for every unitary. The proof covers all seven free ordinary coefficients.
  [Family and proof](Docs/Proofs/order-four-symmetric-six-contact-map.md)
- In order five, the inclusion holds if the first list is real and at
  least one entry of the second list is real.
  [Proof](Lean/MOC/HermitianByNormalFourProof.lean#L100)
- Let $I$ be the identity matrix. The inclusion holds in any order if
  the ranks of $A+tI$ and $B-tI$ sum to at most $n+2$ for some complex $t$.
  [Proof](Lean/MOC/RankTwoOverlap.lean#L481)
- Start with lists of length $d$. Add $m$ copies of $c$ to the first list
  and $m$ copies of $-c$ to the second. The inclusion holds for every
  unitary of order $d+m$ if $d\le m+2+r+s$, where $r$ and $s$ are the
  original multiplicities of $c$ and $-c$, respectively. If the original
  inclusion holds for every unitary and $d\le r+s+3$, the inclusion holds
  for every $m$.
  [Rank condition](Lean/MOC/MarkedPadding.lean#L21) · [Extension from a known case](Lean/MOC/MarkedPadding.lean#L60)

### Change of eigenbasis

- The inclusion holds if independent row and column permutations put
  $U$ into diagonal blocks of order at most three.
  [Proof](Lean/MOC/ExtendedCases.lean#L91)
- Start with two diagonal blocks that each satisfy the inclusion for all
  eigenvalue lists. Apply a two-by-two unitary matrix of determinant one
  to one row from each block. The resulting matrix also satisfies the
  inclusion for all eigenvalue lists.
  [Proof](Lean/MOC/OneBridge.lean#L307)
- The inclusion holds if independent row and column permutations make
  all entries of $U$ below the first subdiagonal zero.
  [Proof](Lean/MOC/SparseRow.lean#L281)
- Let $v$ be a unit column vector and $z$ a complex number of modulus
  one. The inclusion holds if $U=I+(z-1)vv^*$. It also holds if $U-I$
  is zero outside one principal block of order at most three.
  [Rank-one change](Lean/MOC/HouseholderSupport.lean#L360) · [Principal block](Lean/MOC/IdentityPadding.lean#L52)
- In order four, the inclusion holds if a row or column of $U$ has at
  most two nonzero entries. It also holds if $U$ is real orthogonal with
  a zero diagonal.
  [Sparse row](Lean/MOC/SparseRow.lean#L287) · [Sparse column](Lean/MOC/SparseRow.lean#L309) · [Zero diagonal](Lean/MOC/FourZeroDiagonal.lean#L342)
- In order five, the inclusion holds for the discrete Fourier matrix.
  It also holds for each unitary with zero diagonal and off-diagonal
  entries of absolute value $1/2$.
  [Fourier matrix](Lean/MOC/FourierProfiles.lean#L211) · [Zero diagonal and equal magnitudes](Lean/MOC/ConferenceFive.lean#L260)
- If $U$ is the tensor product of two order-two unitaries, one
  permutation law works for all pairs of spectra.
  [Tensor-product law](Docs/Proofs/two-by-two-tensor-permutation-map.md)
- A specified rational orthogonal matrix of order six has a closed
  operator-norm ball of radius $1/23083105288$. Every unitary in this
  ball satisfies the inclusion when the second spectrum is constant
  on each of three specified pairs. The first spectrum is arbitrary.
  [Mixer ball](Docs/Proofs/six-dimensional-mixer-ball-map.md)

### Determinant and matching products

- The inclusion holds if all matching products lie on one line in the
  complex plane. It also holds if each product has the form
  $P_\sigma=c+\sum_j f(j,\sigma(j))$ for a fixed $c$ and a fixed function $f$.
  [Collinear products](Lean/MOC/CollinearKernelSupport.lean#L190) · [Sum over matched pairs](Lean/MOC/Weights.lean#L185)
- Fix $a$, $b$, and $U$, with all entries of $U$ nonzero. The inclusion
  holds for the lists $(a_i-z)$ and $(b_j)$ for every complex $z$ of
  sufficiently large modulus. The lower bound can depend on $a$, $b$, and $U$.
  [Proof](Lean/MOC/ExtendedCases.lean#L428)
- Fix a real spectrum and a complex partner spectrum. The exterior
  shift bound gives inclusion for every mixer outside an explicit
  radius computed from the two lists and a triangle gap of the
  partner spectrum.
  [Exterior shifts](Docs/Proofs/free-eigenvalue-exterior-map.md#exterior-shifts)
- Fix a complex direction $\eta$. The inclusion holds at a maximum of
  $\mathrm{Re}(\eta\det(A+B))$ over relative unitaries if the sum
  at that maximum is normal and has the largest Frobenius norm among
  all maximizing sums. The Frobenius norm is the square root of the sum
  of the squared absolute values of the entries. In order four, a normal
  sum at a nonzero maximum is sufficient.
  [Norm condition](Lean/MOC/NormalOrbit.lean#L408) · [Order four](Lean/MOC/NormalSupportMaximum.lean#L198)

## Other proved reductions

- Suppose the smaller-order conjecture holds. Choose a row of $U$.
  The inclusion follows if the partner eigenvalues on its nonzero
  columns lie on one circle or line through the negative of the
  corresponding first eigenvalue. The written reduction allows
  repeated values.
  [Proof map](Docs/Proofs/spectral-support-proof-map.md#deletion-and-padding-tests)
- Apply the same map $f(z)=(\alpha z+\beta)/(\gamma z+\delta)$ to
  $a_i$ and $-b_j$. If $\alpha\delta-\beta\gamma\ne0$ and the denominators
  are nonzero on both lists, the inclusion for the lists $(f(a_i))$ and
  $(-f(-b_j))$ is equivalent to the original inclusion with the same $U$.
  [Proof](Lean/MOC/ProjectiveTransport.lean#L61)
- For fixed $a$ and $b$, a singular sum is possible for some $U$ if and
  only if the convex hulls of the lists $(a_i,|a_i|^2)$ and
  $(-b_j,|b_j|^2)$ intersect.
  [Proof](Lean/MOC/Singular.lean#L496)
- Join matching products when their permutations differ by a
  transposition. If a closed walk avoids a point and has nonzero
  winding about it, some unitary gives that point as its determinant
  value. This result includes repeated eigenvalues.
  [Transposition winding](Docs/Proofs/transposition-winding-map.md)

## Counterexamples to stronger statements

- In order four, a real orthogonal $U$ and two complex spectra give a
  characteristic polynomial outside the convex hull of the matching
  characteristic polynomials. Each coefficient of the example is in its
  own matching hull. [Exact arithmetic certificate](Docs/Proofs/all-order-proof-maps.md#counterexample-to-the-common-characteristic-polynomial-law)

- In order five, let $U=I-2vv^*$ with $v=(1,1,1,1,1)^{\mathsf T}/\sqrt{5}$.
  For this $U$, every pair of lists satisfies the determinant inclusion.
  There is no one set of nonnegative weights with sum one that represents
  the determinant for all pairs of lists.
  [Inclusion](Lean/MOC/OrderFiveCommonLawObstruction.lean#L38) · [Failure of common weights](Lean/MOC/OrderFiveCommonLawObstruction.lean#L163)
- In order four, some pairs of lists have nonzero and distinct matching
  products, with eight permutations that attain the directional maximum.
  The eight permutations have no common nonempty proper subset of the
  index set that they all map onto itself.
  [Proof](Lean/MOC/ContactCountObstruction.lean#L48)
- The partner list $(0,1,1+i,2i)$ forms a convex quadrilateral. Every
  dense row with a regular pole gives a nonnormal reciprocal
  compression.
  [Pole compression obstruction](Docs/Proofs/spectral-support-proof-map.md#deletion-and-padding-tests)

## Paper proofs and exact certificates

The proof maps include the following results with their hypotheses.
The new Lean source in this update awaits compilation. The cases in
this table use paper arguments or exact arithmetic certificates.

| Result | Scope |
| --- | --- |
| [Smaller overlap reduction](Docs/Proofs/all-order-proof-maps.md#finite-overlap-compression) | The paper reduction uses square order at most $3k^2-k$ for two frames with $k$ columns. At overlap three the bound is 24, compared with 33 in the existing Lean source. Restricted overlap-three cases have a separate direct proof. |
| [Spectral and mixer families](Docs/Proofs/all-order-proof-maps.md#paper-cases-in-any-order) | A uniformly small summand under a general-position condition, a common law for a normal diagonal-plus-rank-one matrix, and a one-port block factorization. |
| [Order-four support cases](Docs/Proofs/order-four-proof-maps.md#paper-support-bounds-and-exact-examples) | A global maximizer with a zero entry, specified high-contact patterns, and an open set of complex spectra that needs a weighted minor certificate. |
| [Exact order-five families](Docs/Proofs/order-five-proof-maps.md#exact-spectral-and-mixer-cases) | An open set of mixers for all real first lists and complex partners, two free complex partner entries at fixed starting spectra, and a complex spectral neighborhood beyond the ordinary minor cone. |

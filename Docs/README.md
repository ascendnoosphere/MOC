# Proof maps

The Marcus–de Oliveira conjecture asks whether the determinant of the
sum of two complex normal matrices is a convex combination of products
obtained by matching their eigenvalues. Count eigenvalues with
multiplicity. A normal matrix commutes with its conjugate transpose.
[Problem, notation, and main theorems](../README.md)

Start with the all-order map for general reductions. Use the order-four
or order-five map for a fixed order. The other maps give the hypotheses,
arguments, and exact Lean statements for specific subjects.

## Notation and proof status

Write $\mathrm{MOC}_n$ for the conjecture for every normal pair of order
$n$. Write $\mathrm{MOC}$ for the conjecture in every finite order.
In a route table, $T_n$ is the complete test in that row, including all
of its quantifiers. Write $T$ for an all-order test. Thus
$\mathrm{MOC}_n\Longleftrightarrow T_n$ states two implications.
$T_n\Longrightarrow\mathrm{MOC}_n$ states a sufficient condition.
An order change is explicit, as in
$\mathrm{MOC}_{n+1}\Longleftrightarrow C_n$, where $C_n$ is the
rectangular test with $n$ rows and $n+1$ columns.

The mathematical status is independent of the build status.
“Proved case” gives the inclusion under its stated hypotheses.
“Reduction” gives an implication whose premise can remain open.
“Open” identifies a statement for which this repository has no proof.
“Paper only” identifies an argument whose full conclusion is outside Lean.
In a diagram, an AND node needs every input. An OR node needs one
complete input. A dashed arrow needs the stated open premise.

## Lean check status

The “Lean Checked?” column reports the linked Lean statements and their
imports. The status snapshot uses Lean 4.19.0 and the pinned mathlib.
Lake checked the source and dependency hashes against existing build
artifacts on 27 November 2026. This check did not compile new proofs.
It verified current builds for 304 of the 374 cited modules. An axiom
audit of those modules checked 13,108 safe imported declarations.

| Entry | Meaning |
| --- | --- |
| Yes | Lake validated a current cached build of every linked Lean module. |
| Partial | The row includes both checked and unchecked Lean modules. |
| No | No current build was verified for the linked claim. This includes retained files with compile errors and files without a current artifact. |
| Paper only | The full claim has a paper argument. Linked Lean lemmas can cover individual steps. |
| Not applicable | The row defines notation or lists data; it does not assert a Lean theorem. |

A checked equivalence does not prove an open side of that equivalence.
A checked conditional theorem does not discharge its premise. A file
name or an import in the default target is not evidence of a passing
build. The complete library build and its final axiom audit remain
pending. The [build instructions](../README.md#check-the-lean-source)
state the permitted axioms and commands.

The file `Lean/MOC/Small.lean` defines the module `MOC.Small`.
Run `lake --no-build build +MOC.Small:olean` from the repository root
to validate its existing cache. This command checks the dependencies.
It stops if a required artifact needs a build.

## General routes

| Map | Coverage | Lean Checked? |
| --- | --- | --- |
| [All orders](all-orders-proof-map.md) | All-order alternatives, the order split, fixed-order tests, and spectral formulations. | Partial (106/112) |
| [Proof routes](research-attempts-proof-map.md) | Proved steps, exact examples, and open implications for spectral reductions and support bounds. | Partial (22/31) |
| [Determinant methods](determinant-research-reports-proof-map.md) | Determinant identities, coefficient laws, compression, convexity, topology, and open proof obligations. | Partial (37/53) |
| [Order four](order-four-proof-map.md) | Fixed conics, real orthogonal mixers, stationary maxima, contact patterns, and the bilinear chart. | Partial (28/44) |
| [Order five](order-five-proof-map.md) | Fixed conics, contact thresholds, two-by-two zero submatrices, and squared-minor tests. | Partial (19/21) |
| [Determinant inclusion certificates](determinant-inclusion-certificates-proof-map.md) | Integer and power comparisons, a finite free-entry test, spectral multiplicities, composition of mixers, and support bounds in orders four and five. | Partial (12/14) |
| [Contact transfer](contact-transfer-proof-map.md) | Fixed and varying determinant differences, contact counts, rank, moments, and isolation. | Yes |
| [Determinant modulus bound](modulus-order-transfer-proof-map.md) | Drury's bound in every order, transfer to smaller orders, and the equivalence with real orthogonal changes of eigenbasis on any unbounded set of orders. | Yes |
| [Spectral and support results](spectral-support-proof-map.md) | Spectral families, order-four support tests, and determinant reductions. | Partial (16/26) |

## Order-four support tests

A support test compares the projection of the determinant in one
direction with the largest projection of a matching product. A
contact is a matching that attains that largest projection.

| Map | Lean Checked? |
| --- | --- |
| [Support-cost cone](order-four-support-cost-cone-proof-map.md) | Partial (1/3) |
| [Mixed-ray cancellation](order-four-mixed-ray-cancellation-proof-map.md) | Partial (2/14) |
| [Real spectral lifts](order-four-real-spectral-lift-proof-map.md) | Yes |
| [Real matching sums of squares](order-four-real-matching-squares-proof-map.md) | Partial (4/11) |
| [Klein-four matching squares](order-four-klein-four-matching-squares-proof-map.md) | Partial (4/7) |
| [Five-parameter contact family](order-four-five-parameter-contact-proof-map.md) | Partial (3/5) |
| [Symmetric six-contact family](order-four-symmetric-six-contact-proof-map.md) | Partial (2/4) |
| [Opposite eigenvalues](order-four-opposite-eigenvalues-proof-map.md) | Partial (3/4) |
| [Weighted-minor center](order-four-weighted-minor-center-proof-map.md) | Partial (1/2) |

## Spectral and mixer cases

The mixer is the unitary change between the two eigenbases.

| Map | Lean Checked? |
| --- | --- |
| [Normal products and normal relative products](normal-products-proof-map.md) | Yes |
| [Quadratic images of Hermitian rank-one perturbations](quadratic-rank-one-perturbations-proof-map.md) | Yes |
| [Common permutation weights for Cauchy eigenbases](cauchy-eigenbasis-permutation-laws-proof-map.md) | Yes |
| [Circle-or-line common weights in order four](order-four-circle-or-line-common-weights-proof-map.md) | Yes |
| [Complex Hadamard matrices in order four](order-four-complex-hadamard-proof-map.md) | Yes |
| [Conic spectral reductions](conic-spectral-reductions-proof-map.md) | Partial (3/4) |
| [Equal spectral coefficients](equal-spectral-coefficients-proof-map.md) | Yes |
| [One free eigenvalue and exterior shifts](free-eigenvalue-and-exterior-shifts-proof-map.md) | Partial (14/15) |
| [Overlapping circle blocks](overlapping-circle-blocks-proof-map.md) | Yes |
| [Real-parameter spectra in order four](order-four-real-parameter-spectra-proof-map.md) | Yes |
| [Six-dimensional mixer ball](six-dimensional-mixer-ball-proof-map.md) | No |
| [Six-dimensional rank-two overlap](six-dimensional-rank-two-overlap-proof-map.md) | No |
| [Small spectral perturbations](small-spectral-perturbation-proof-map.md) | Yes |
| [Unitary matrices with at most three nonzero entries per row or per column](sparse-unitary-proof-map.md) | Yes |
| [Symmetric cube mixer in order four](order-four-symmetric-cube-mixer-proof-map.md) | Yes |
| [Three spectral values with one singleton](three-spectral-values-with-one-singleton-proof-map.md) | Partial (9/10) |
| [Two-by-two tensor mixers](two-by-two-tensor-mixer-proof-map.md) | Yes |
| [Weighted permutation cycles](weighted-permutation-cycles-proof-map.md) | Yes |

## Determinant formulas, attainment, and probability

| Map | Lean Checked? |
| --- | --- |
| [Projection deletion and overlapping two-level blocks](projection-leaf-deletion-proof-map.md) | Yes |
| [Spectral profile determinant](spectral-profile-determinant-proof-map.md) | Partial (3/9) |
| [Attained values from transposition walks](transposition-winding-proof-map.md) | No |
| [Gaussian spectra and Haar mixers](gaussian-spectra-and-haar-mixers-proof-map.md) | Yes |

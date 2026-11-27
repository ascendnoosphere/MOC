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
Each relation names the complete test in its row, including all its
quantifiers. A subscript gives the matrix order. For example,
$\mathrm{MOC}_n\Longleftrightarrow\text{one-free-entry law}_n$
states that the conjecture and that law imply each other at order $n$.
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
imports. The snapshot uses Lean 4.19.0 and the pinned mathlib. The checks
on 27 November 2026 combine compilation of selected modules with Lake
validation of existing build artifacts. Lake compares the current source
and dependency hashes with those artifacts.

The current record gives passing builds for 394 of the 983 source
modules. This includes 183 of the 383 modules linked in these documents.
A changed source or import invalidates its earlier check record.
A module without a current passing record remains “No.”

The latest completed axiom audit covers 142 modules and 6500 safe
declarations. It found only the three permitted axioms. Later builds
still need a combined axiom audit. The focused build stopped before
completion. Revised proofs without a passing build remain unchecked.
The full T34 polynomial certificate reached the limit of 12 gibibytes
of memory. Its check remains incomplete.

| Entry | Meaning |
| --- | --- |
| Yes | Lake validated a current cached build of every linked Lean module. |
| Partial | The row includes both checked and unchecked Lean modules. |
| No | No current passing build is recorded for the linked claim. This includes changed source or imports, compile errors, checks that reached a resource limit, and files without a current artifact. |
| Paper only | The full claim has a paper argument. Linked Lean lemmas can cover individual steps. |
| Not applicable | The row defines notation or lists data; it does not assert a Lean theorem. |

A checked equivalence does not prove an open side of that equivalence.
A checked conditional theorem does not discharge its premise. A file
name or an import in the default target is not evidence of a passing
build. The complete library build and its final axiom audit remain
pending. The [build instructions](../README.md#check-the-lean-source)
state the permitted axioms and commands.

The file `Lean/MOC/Small.lean` defines the module `MOC.Small`.
Run `LEAN_NUM_THREADS=2 taskset -c 0-3 timeout 15m lake --no-build build +MOC.Small:olean`
from the repository root to validate its existing cache. This command
uses four CPU cores and checks the dependencies. It stops if a required
artifact needs a build. A time limit leaves the check incomplete.

## General routes

| Map | Coverage | Lean Checked? |
| --- | --- | --- |
| [All orders](all-orders-proof-map.md) | All-order alternatives, the order split, fixed-order tests, and spectral formulations. | Partial (43/114) |
| [Proof routes](research-attempts-proof-map.md) | Proved steps, exact examples, and open implications for spectral reductions and support bounds. | Partial (16/31) |
| [Determinant methods](determinant-research-reports-proof-map.md) | Determinant identities, coefficient laws, compression, convexity, topology, and open proof obligations. | Partial (32/53) |
| [Order four](order-four-proof-map.md) | Fixed conics, real orthogonal mixers, stationary maxima, contact patterns, and the bilinear chart. | Partial (13/36) |
| [Order five](order-five-proof-map.md) | Fixed conics, contact thresholds, two-by-two zero submatrices, and squared-minor tests. | Partial (13/21) |
| [Determinant inclusion certificates](determinant-inclusion-certificates-proof-map.md) | Integer and power comparisons, a finite free-entry test, spectral multiplicities, composition of mixers, and support bounds in orders four and five. | Partial (6/14) |
| [Contact transfer](contact-transfer-proof-map.md) | Fixed and varying determinant differences, contact counts, rank, moments, and isolation. | Partial (18/28) |
| [Determinant modulus bound](modulus-order-transfer-proof-map.md) | Drury's bound in every order, transfer to smaller orders, and the equivalence with real orthogonal changes of eigenbasis on any unbounded set of orders. | Partial (6/9) |
| [Spectral and support results](spectral-support-proof-map.md) | Spectral families, order-four support tests, and determinant reductions. | Partial (11/26) |

## Order-four support tests

A support test compares the projection of the determinant in one
direction with the largest projection of a matching product. A
contact is a matching that attains that largest projection.

| Map | Lean Checked? |
| --- | --- |
| [Support-cost cone](order-four-support-cost-cone-proof-map.md) | Partial (2/3) |
| [Support bounds from six contacts](order-four-six-contact-support-proof-map.md) | Partial (14/18) |
| [Mixed-ray cancellation](order-four-mixed-ray-cancellation-proof-map.md) | Partial (5/14) |
| [Real spectral lifts](order-four-real-spectral-lift-proof-map.md) | Partial (1/3) |
| [Real matching sums of squares](order-four-real-matching-squares-proof-map.md) | Partial (6/11) |
| [Klein-four matching squares](order-four-klein-four-matching-squares-proof-map.md) | Partial (5/7) |
| [Five-parameter contact family](order-four-five-parameter-contact-proof-map.md) | Partial (1/5) |
| [Symmetric six-contact family](order-four-symmetric-six-contact-proof-map.md) | Partial (2/4) |
| [Opposite eigenvalues](order-four-opposite-eigenvalues-proof-map.md) | Partial (3/4) |
| [Weighted-minor center](order-four-weighted-minor-center-proof-map.md) | Yes |

## Spectral and mixer cases

The mixer is the unitary change between the two eigenbases.

| Map | Lean Checked? |
| --- | --- |
| [Normal products and normal relative products](normal-products-proof-map.md) | Partial (3/6) |
| [Quadratic images of Hermitian rank-one perturbations](quadratic-rank-one-perturbations-proof-map.md) | Partial (2/9) |
| [Common permutation weights for Cauchy eigenbases](cauchy-eigenbasis-permutation-laws-proof-map.md) | Partial (4/16) |
| [Circle-or-line common weights in order four](order-four-circle-or-line-common-weights-proof-map.md) | Partial (1/4) |
| [Complex Hadamard matrices in order four](order-four-complex-hadamard-proof-map.md) | Yes |
| [Conic spectral reductions](conic-spectral-reductions-proof-map.md) | Partial (3/4) |
| [Equal spectral coefficients](equal-spectral-coefficients-proof-map.md) | Yes |
| [One free eigenvalue and exterior shifts](free-eigenvalue-and-exterior-shifts-proof-map.md) | Partial (8/15) |
| [Overlapping circle blocks](overlapping-circle-blocks-proof-map.md) | Partial (4/9) |
| [Real-parameter spectra in order four](order-four-real-parameter-spectra-proof-map.md) | Partial (2/9) |
| [Six-dimensional mixer ball](six-dimensional-mixer-ball-proof-map.md) | No |
| [Six-dimensional rank-two overlap](six-dimensional-rank-two-overlap-proof-map.md) | No |
| [Small spectral perturbations](small-spectral-perturbation-proof-map.md) | Partial (4/6) |
| [Unitary matrices with at most three nonzero entries per row or per column](sparse-unitary-proof-map.md) | Partial (14/26) |
| [Symmetric cube mixer in order four](order-four-symmetric-cube-mixer-proof-map.md) | Yes |
| [Three spectral values with one singleton](three-spectral-values-with-one-singleton-proof-map.md) | Partial (5/10) |
| [Two-by-two tensor mixers](two-by-two-tensor-mixer-proof-map.md) | Yes |
| [Weighted permutation cycles](weighted-permutation-cycles-proof-map.md) | Yes |

## Determinant formulas, attainment, and probability

| Map | Lean Checked? |
| --- | --- |
| [Projection deletion and overlapping two-level blocks](projection-leaf-deletion-proof-map.md) | Yes |
| [Spectral profile determinant](spectral-profile-determinant-proof-map.md) | Partial (4/9) |
| [Attained values from transposition walks](transposition-winding-proof-map.md) | No |
| [Gaussian spectra and Haar mixers](gaussian-spectra-and-haar-mixers-proof-map.md) | Partial (1/2) |

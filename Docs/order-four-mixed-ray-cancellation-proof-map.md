# Order-four mixed-ray cancellation

[Proof map index](README.md) · [Order-four proof map](order-four-proof-map.md) · [Unrestricted conjecture](../README.md)

A cost profile assigns a real number to each of the 24 permutations of
four labels. An ordinary ray is the indicator that a permutation sends
a specified row set to a specified column set. The 34 ordinary rays
use singleton sets and one representative from each complementary pair
of two-element sets. A mixed ray is a relabeling of a fixed signed sum
of four of these indicators. All indices in the Lean source start at
zero. [Cost profiles](../Lean/MOC/FourSupportCostProfiles.lean#L24)

```mermaid
flowchart TD
    A["Nonnegative expansion in<br/>34 ordinary and 48 mixed rays"]
    B["Ordinary sum and at most<br/>one mixed term"]
    C["Relabel to the canonical mixed ray"]
    D["Absorb ordinary generators<br/>outside the thirteen-ray section"]
    E["Ordinary sum"]
    F["Canonical mixed ray with positive coefficient<br/>and at most thirteen ordinary coefficients"]
    A --> B --> C --> D
    D --> E
    D --> F
```

For two distinct mixed rays, their sum is a nonnegative combination of
ordinary rays. Multiply this identity by the smaller mixed coefficient.
The operation removes at least one mixed term and preserves the whole
profile. Induction adds the mixed terms one at a time. [Pair cancellation](../Lean/MOC/FourMixedRayCancellation.lean#L376) · [Reduction to one mixed term](../Lean/MOC/FourMixedRayCancellation.lean#L421)

After relabeling the remaining mixed term, pair it with each ordinary
term outside the canonical set of thirteen ordinary rays. The exact
absorption identity puts the paired part in that set. The procedure
uses the smaller of the two coefficients at each step. If the mixed
coefficient becomes zero, the result is in the ordinary cone. Otherwise
the final profile has the canonical mixed ray and ordinary coefficients
on the thirteen-ray set. [Absorption identities](../Lean/MOC/FourMixedRayCancellation.lean#L180) · [Support bound](../Lean/MOC/FourMixedRayCancellation.lean#L26) · [Normal form](../Lean/MOC/FourMixedRayCancellation.lean#L515)

Signed determinant weights evaluate a cost profile at a fixed mixer by
a linear map. An ordinary ray evaluates to the squared modulus of its
specified minor. Thus the cancellation identities preserve the value
at every unitary mixer, and the ordinary branch is nonnegative.
Nonnegativity in the mixed section requires a separate argument for
the costs that come from spectra. [Squared-minor evaluation](../Lean/MOC/FourMixedRayCancellation.lean#L553) · [Ordinary nonnegativity](../Lean/MOC/FourMixedRayCancellation.lean#L582)

The Lean proof checks the 47 seed pair identities and the 21
absorption identities over integer permutation profiles. An independent
exact replay also checked closure of the ordinary rays under the 48
relabelings used here. The new Lean source was written without a build.
[Archived certificate source](https://github.com/ascendnoosphere/MOC/blob/a49606d39e8bb5903c9bb4a51651a18679499c0c/data/certificates/geometry/mixed_cancellation_graph.json)

## Canonical contact certificates

Write a normalized cost as the canonical mixed ray plus a sum of
ordinary rays with nonnegative coefficients. Each tuple specifies the
ordinary ray indices and the order of their coefficients. The premises
use the mixed-sign factors of the inverse-pencil determinants. Each
factor has a positive constant term.

| Ordinary ray indices | Premise and conclusion |
| --- | --- |
| $(13,17,18,27,30)$ | If the first determinant factor is nonpositive, the coefficients on rays 13, 18 and 27 satisfy the bound for a square decomposition. The full cost is a sum of matching squares. [Lean statement](../Lean/MOC/FourEightContactSmallFactors.lean#L167) |
| $(7,13,20,27,31)$ | If the second determinant factor is nonpositive, the coefficients on rays 7, 13 and 31 satisfy the bound for a square decomposition. The full cost is a sum of matching squares. [Lean statement](../Lean/MOC/FourEightContactSmallFactors.lean#L213) |

Both certificates allow zero coefficients. Exact Python checks expanded
both pencil determinants and checked the square identities on all 24
permutations. The new Lean source awaits verification.
[Archived proof](https://github.com/ascendnoosphere/MOC/blob/14cf959d78ae5828a92013d13a65b9c50ebb01d0/Docs/research/moc_high_contact_nonlinear_capacity_20261031.txt)

### Additional whole-domain certificates

Each table row uses positive ordinary coefficients. Exact Python
checks verified the full determinant identities and the permutation
identities used in the square decompositions.

| Ordinary ray indices | Premise and result |
| --- | --- |
| $(13,18,23,28,30)$ | A zero mixed determinant factor forces one of three square bounds. [Lean statement](../Lean/MOC/FourEightContactReducedFactors.lean#L397) |
| $(7,18,20,23,28)$ | A zero mixed determinant factor forces one of four square bounds. [Lean statement](../Lean/MOC/FourEightContactReducedFactors.lean#L423) |
| $(13,17,18,27,28)$ | A zero mixed determinant factor and the cubic height equation at positive height give one of three square bounds. [Lean scalar certificate](../Lean/MOC/FourEightContactHigherFactors.lean#L48) |
| $(7,13,17,27,31)$ | A zero mixed determinant factor gives a matching sum of squares through an explicit four-by-four Gram matrix. [Lean statement](../Lean/MOC/FourEightContactLargestFactors.lean#L45) |

The archived threshold-rectangle proof gives squares for the whole
family $(7,13,18,27,31)$ on its mixed factor sublevel. For six
seven-contact families, setting one coefficient to zero reduces the
nonpositive factor to that of a settled family, with relabeling where
necessary. The removed term is an ordinary square. The six tuples are
$(13,17,18,20,27,30)$, $(7,13,20,27,30,31)$,
$(7,13,18,27,30,31)$, $(7,13,17,18,27,30)$,
$(7,10,13,17,27,30)$ and $(7,10,13,20,23,30)$.
For $(7,17,18,23,27,30)$ the factor equation forces the product of the
coefficients on rays 18 and 23 to be at least one. The formal factor
links remain separate from these Lean square lemmas.
[Inheritance and pair certificate](../Lean/MOC/FourSevenContactAffineElimination.lean#L47) · [Archived threshold-rectangle proof](https://github.com/ascendnoosphere/MOC/blob/14cf959d78ae5828a92013d13a65b9c50ebb01d0/Docs/research/moc_high_contact_threshold_rectangle_closure_20261031.txt)

### Remaining coefficient tests

For $(7,13,23,30,31)$ the factor equation gives squares when the
coefficient on ray 31 is at most one. For four seven-contact classes,
affine factor equations have a nonzero slope or give a pair bound on
the zero-slope branch. Shared Gram terms give further sufficient
conditions in seven-contact classes.
[Eight-contact bound](../Lean/MOC/FourEightContactAffineFactors.lean#L217) · [Affine charts](../Lean/MOC/FourSevenContactAffineChambers.lean#L37) · [Shared compensation](../Lean/MOC/FourSevenContactMiddleNonlinearFactors.lean#L77) · [Four-feature Gram client](../Lean/MOC/FourSevenContactHighNonlinearFactors.lean#L10)

In twelve seven-contact profiles the matching cubic fixes the height
as a quotient with positive numerator. Positive height requires a
positive denominator. Exact balanced rank-eight roots can pass this
test. The open domains require further spectral or support restrictions.
The new Lean source awaits verification.
[First six profiles](../Lean/MOC/FourSevenContactSmallNonlinearFactors.lean#L87) · [Second six profiles](../Lean/MOC/FourSevenContactLargeNonlinearFactors.lean#L66)

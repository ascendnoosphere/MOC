# Common determinant weights on a circle or line

[All-order proof map](all-order-proof-maps.md) · [Order-four proof map](order-four-proof-maps.md)

Let (a) be a list of four eigenvalues. Let (U) be the unitary change
between eigenbases. A common law assigns one probability to each
permutation of the four labels. It represents the determinant of
(mathrm{diag}(a)+Umathrm{diag}(b)U^*) as an average of the matching
products for every complex list (b).

| Premise | Result | Lean source |
| --- | --- | --- |
| Four distinct real eigenvalues | A finite facet check gives common weights. The lower parameter interval suffices, and closedness includes its upper endpoint. | [Lower interval](../../Lean/MOC/HermitianByNormalFourProof.lean#L40) · [Conversion to weights](../../Lean/MOC/HermitianByNormalFour.lean#L80) |
| A repeated eigenvalue in a list of length four | Three groups suffice, and one can be a singleton. A coupling of the corresponding adjacent sized minors gives common weights. | [Repeated case](../../Lean/MOC/FourCircleLineCommonWeights.lean#L49) |
| The four eigenvalues lie on one circle or one line | A fractional-linear change maps the fixed list to real values. The law survives the change, including partner values at the pole by continuity. | [Common law](../../Lean/MOC/FourCircleLineCommonWeights.lean#L87) |

The equivalent formulation with (b) fixed swaps the two lists and
uses the adjoint of (U). The weights are indexed by inverse
permutations after this swap.

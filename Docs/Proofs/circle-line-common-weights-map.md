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

## Two free diagonal entries

The fixed spectrum is ((1,-i,-2,-2i)). The diagonal partner is
((x,y,0,1+i)), for complex (x,y). The mixer in the eigenbasis of the
diagonal partner is (1/14) times the real matrix
[
egin{pmatrix}
-5&-11&1&-7\
-1&-5&-11&7\
7&-7&7&7\
-11&1&5&7
end{pmatrix}.
]
Its rows have squared norm (196) and are orthogonal before division
by (14). [Unitary proof](../../Lean/MOC/FourCircleLineCommonWeights.lean#L107)

For each determinant or matching product, evaluate at
((x,y)=(0,0),(1,0),(1,1)). Use the real part of the linear combination
with coefficients (1+3i,2-i,-4+2i) on these three values. Every
permutation gives a value at most (-4). The matrix gives
(-769/196), which is strictly greater than (-4).
Thus no probability law gives all three evaluations at once.
[Obstruction](../../Lean/MOC/FourCircleLineCommonWeights.lean#L205)

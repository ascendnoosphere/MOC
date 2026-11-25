# Order-four weighted-minor center

[Conjecture](../../README.md) · [Order-four proof routes](order-four-proof-maps.md)

Let $U$ be a complex unitary matrix of order four. Let $U^*$ be its
conjugate transpose. Use the eigenvalue lists

$$
a=\left(0,-\frac15+\frac4{15}i,-\frac1{10}+\frac2{15}i,
\frac{177-66i}{793}\right),\qquad
b=\left(\frac12,1,-\frac15-\frac25i,\frac{-232-344i}{1345}\right).
$$

For a permutation $p$ of the four labels, write
$P_p=\prod_j(a_j+b_{p(j)})$. The determinant of
$\mathrm{diag}(a)+U\mathrm{diag}(b)U^*$ belongs to the convex hull of
the 24 values $P_p$. The theorem applies to every $U$ for these fixed
lists. [Left list](../../Lean/MOC/FourWeightedMinorCenter.lean#L37) · [Right list](../../Lean/MOC/FourWeightedMinorCenter.lean#L40) · [Hull inclusion](../../Lean/MOC/FourWeightedMinorCenter.lean#L473)

```mermaid
flowchart TD
    A["Two fixed complex spectra"] --> B["24 matching products"]
    B --> C["Exact oriented area identities for nine edges"]
    C --> D["Seven edges use ordinary minor terms"]
    C --> E["Two edges also use weighted minor terms"]
    F["Quaternion inequality and arithmetic-geometric mean"] --> G["Weighted terms are nonnegative on real orthogonal matrices"]
    G --> H["One minor-table mixture transports each weighted term to unitary matrices"]
    E --> I["The determinant meets all nine edge bounds"]
    H --> I
    D --> I
    I --> J["The determinant is in the matching hull"]
    K["Positive turns at each of the nine vertices"] --> J
    C --> L["A linear functional excludes an ordinary certificate for the final edge"]
```

## Nine oriented edge bounds

Number the row-to-column permutations from zero in lexicographic
order. The counterclockwise vertex order is $0,6,18,12,11,17,4,10,2$.
For an edge from label $l$ to label $r$, its cost at a matching $p$
is the oriented area form applied to $P_r-P_l$ and $P_p-P_l$.
Multiply this cost by the positive scale for the edge. The resulting
function on permutations is a sum of the terms in the rational table.
The exact identities use the finite eigenvalue lists in the theorem.
[Term table](../../Lean/MOC/FourWeightedMinorCenter.lean#L112) · [Edge identities](../../Lean/MOC/FourWeightedMinorCenter.lean#L243)

For row and column sets $I,J$, the ordinary indicator is one if
$p(I)=J$ and zero otherwise. Evaluation at $U$ replaces this indicator
with the squared modulus $M_{I,J}$ of the corresponding minor.
Seven edge certificates use only nonnegative coefficients on these
indicators. The edges $10\to2$ and $2\to0$ also use relabeled and
transposed copies of the following expression for a real $\tau>0$:

$$
M_{\{1\},\{2\}}+M_{\{2\},\{1\}}
+(1+\tau)M_{\{2,3\},\{2,3\}}
+(1+1/\tau)M_{\{1,2\},\{1,2\}}-M_{\{1,3\},\{0,2\}}.
$$

Let $x=M_{\{2,3\},\{2,3\}}$ and $y=M_{\{1,2\},\{1,2\}}$.
The quaternion inequality proves nonnegativity on real orthogonal
matrices when the two extra terms are replaced by $2\sqrt{xy}$.
The arithmetic–geometric mean inequality gives
$2\sqrt{xy}\le\tau x+\tau^{-1}y$. The squared-minor table of a complex
unitary matrix is a convex combination of real orthogonal tables.
Since the expression is linear in this table, the bound holds for
each complex unitary. [Quaternion and mean inequality](../../Lean/MOC/FourWeightedMinorCenter.lean#L279) · [Unitary evaluation](../../Lean/MOC/FourWeightedMinorCenter.lean#L313)

Evaluate the nine identities at the determinant to get the nine
oriented edge inequalities. Each selected vertex has a positive
turn. In any projection direction, the two incident edges at a
maximizing vertex bound the projection of the determinant. This
proves membership in the hull of the nine selected matching products,
which is a subset of the full matching hull. [Strict turns](../../Lean/MOC/FourWeightedMinorCenter.lean#L252) · [Edge bounds](../../Lean/MOC/FourWeightedMinorCenter.lean#L420) · [Plane hull criterion](../../Lean/MOC/PlaneHullEdges.lean#L55)

## Obstruction to an ordinary certificate

Let $g$ be the cost for the edge $2\to0$. For a cost $v$ on the 24
permutations define

$$
L(v)=v_{10}-v_4+\sum_{k\in\{0,1,2,7,8,13,19\}}v_k.
$$

The functional $L$ is nonnegative on every ordinary indicator and
negative on $g$. Linearity excludes a nonnegative combination of
ordinary indicators for this edge, with arbitrary finite support.
[Functional on indicators](../../Lean/MOC/FourWeightedMinorCenter.lean#L266) · [Edge gap](../../Lean/MOC/FourWeightedMinorCenter.lean#L487) · [No ordinary certificate](../../Lean/MOC/FourWeightedMinorCenter.lean#L506)

## Verification status

The local source is `Temp/pdf/MOC-proof-report.pdf` and the exact
fixture in `Temp/txt/exact_case_certificate_bundle.txt`. An
independent rational computation checked the Lean table at 216
edge-permutation pairs, all nine turns, and 256 indicators for the
separating functional. The Lean source awaits compilation. The
uniform neighborhood of radius $10^{-17}$ remains a research result
with an exact arithmetic check. [Neighborhood argument](order-four-proof-maps.md#an-open-set-of-spectra-with-a-uniform-proof)

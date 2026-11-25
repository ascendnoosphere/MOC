# Order-four opposite eigenvalue support

[Conjecture](../../README.md) · [Order-four proof routes](order-four-proof-maps.md)

Let $a$ and $b$ be complex eigenvalue lists of length four. Let $U$
be the unitary matrix that relates their eigenbases. For a permutation
$\sigma$, the matching product is
$P_\sigma=\prod_j(a_{\sigma(j)}+b_j)$. If $a_i+b_j=0$ for one pair
of labels, the determinant of
$\mathrm{diag}(a)+U\mathrm{diag}(b)U^*$ belongs to the convex hull of
the matching products. The result allows all other complex values
and repetitions. It therefore gives the support bound in every
complex direction. [Lean hull inclusion](../../Lean/MOC/FourCoincidence.lean#L360) · [Directional statement](../../Lean/MOC/FourOppositePairSupport.lean#L355)

```mermaid
flowchart BT
    Opposite["One opposite eigenvalue pair"]
    Hull["Order-four determinant inclusion"]
    Direction["Bound in every complex direction"]
    Gap["Nonnegative support cost<br/>constant on six fixed-label matchings"]
    Ordinary["Nonnegative combination of<br/>16 subset-image indicators"]
    Squares["16 real squares in the<br/>matching-function space"]
    Opposite --> Hull
    Hull --> Direction
    Opposite -->|with a support height| Gap
    Gap --> Ordinary
    Ordinary --> Squares
```

## Ordinary cost and sum of squares

Relabel the opposite pair as $a_0+b_0=0$. Fix a direction $\eta\in
\mathbb C$ and a real number $H$ with
$\mathrm{Re}(\eta P_\sigma)\le H$ for all $\sigma$. The cost
$g(\sigma)=H-\mathrm{Re}(\eta P_\sigma)$ is nonnegative. All six
permutations with $\sigma(0)=0$ have cost $H$.
[Spectral cost](../../Lean/MOC/FourOppositePairSupport.lean#L325)

For sets $S,T$ of labels, the subset-image indicator is one if
$\sigma(S)=T$ and zero otherwise. The decomposition uses seven
singleton indicators and nine indicators on two-element sets. One
singleton indicator is supported on the six permutations that
fix zero. The other fifteen are zero on these permutations.
[Ordinary generators](../../Lean/MOC/FourOppositePairSupport.lean#L163)

The same decomposition holds for every nonnegative function in the
fourteen-coordinate matching-function space that is constant on
those six permutations. The proof uses a table $w$ with three rows
and three columns to express the other eighteen matching costs.
Each cost is the sum of two entries in distinct rows and columns.
Every such pair occurs. Thus two negative entries cannot lie in
distinct rows and columns. The negative entries all lie on one row
or one column.

If they lie on row $i$, let $p$ and $q$ be its two largest nonnegative
deficits, with a zero deficit for each nonnegative entry. Put
$p+q$ on the singleton indicator for row $i$. Put $p-q$ on the
singleton indicator for a column $j$ that attains the largest deficit.
Add these amounts to the corresponding row and column of the table,
then subtract $p$ from each cell. The resulting table is nonnegative.
For each pair of selected cells, adding the singleton coefficients
for the missing row and column preserves the original matching cost.
Transposition gives the same construction when the negative entries
lie on a column. [Lean decomposition](../../Lean/MOC/FourOppositePairSupport.lean#L207)

Each indicator $I$ belongs to the matching-function space. For its
coefficient $t\ge0$, the function $tI$ equals $(\sqrt{t}I)^2$.
The sixteen terms give the real sum of squares.
[Lean sum of squares](../../Lean/MOC/FourOppositePairSupport.lean#L293)

The matching coordinates use Appendix A of [Zheng's preprint](https://doi.org/10.13140/RG.2.2.36790.25923).
The local source for the constant-cost claim is
`Temp/txt/moc_one_collision_support_theorem_20261031.txt`. The table
construction above gives a direct proof of that claim. An exact
arithmetic check verified the coordinate identities on all 24
permutations and the membership of all 16 indicators in the matching
space. It also tested rebalancing on 36,498 admissible integer tables
with entries in $[-2,2]$.

The existing opposite-pair law gives one distribution for all lists
with the specified opposite pair at label zero. The new Lean source
was written with compilation deferred.
[Common distribution](../../Lean/MOC/FourCoincidence.lean#L338)

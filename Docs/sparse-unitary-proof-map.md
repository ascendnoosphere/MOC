# Sparse unitary proof map

[Proof map index](README.md) · [README overview](../README.md) · [All-order routes](all-orders-proof-map.md)

Let $n$ be the matrix order. Let $a$ and $b$ be the lists of complex eigenvalues, with multiplicity. Let $U$ be the unitary change of eigenbasis and let $U^*$ be its conjugate transpose. Write $S_n$ for the permutations of the $n$ labels, $\mathrm{diag}$ for the diagonal matrix of a list, and $\mathrm{conv}_{\mathbb R}$ for the real convex hull. The inclusion to prove is

$$
\det\bigl(\mathrm{diag}(a)+U\,\mathrm{diag}(b)\,U^*\bigr)
\in
\mathrm{conv}_{\mathbb R}\left\{\prod_{j=1}^n(a_{\sigma(j)}+b_j):\ \sigma\in S_n\right\}.
$$

The inclusion holds at every order if each row has at most three nonzero entries, or if each column has at most three. A row or column degree counts its nonzero entries. Lean calls the inclusion `Holds` and uses the row degrees of $U^*$ for the column degrees of $U$. It also states the case with both bounds as `SupportDegreeLEThreeConjecture`.
[Inclusion](../Lean/MOC/Core.lean#L21) · [Both bounds](../Lean/MOC/SparseUnitary.lean#L13) · [Row bound](../Lean/MOC/SparseUnitary.lean#L27) · [Column bound](../Lean/MOC/SparseUnitary.lean#L44)

Every violation therefore needs both a row and a column with at least four nonzero entries. In order four, each entry of this row and this column must be nonzero. This conclusion holds for every violating matrix and every choice of spectra.
[Necessary degrees](../Lean/MOC/SparseUnitary.lean#L54) · [Full row and column in order four](../Lean/MOC/SparseUnitary.lean#L66)

## Induction on the order

```mermaid
flowchart TD
    A["Row degree at most three"]
    B{"Row or column of degree at most two?"}
    C["Smaller normalized minors"]
    D["All degrees equal three"]
    E{"Proper paired block split?"}
    F["Smaller paired blocks"]
    G["Order at most four"]
    H["Known orders at most three"]
    I["Zero matching at order four"]
    A --> B
    B -->|Yes| C
    B -->|No| D
    D --> E
    E -->|Yes| F
    E -->|No| G
    G --> H
    G --> I
```

Use strong induction. The hypothesis gives the inclusion for all spectra and all smaller unitary matrices with the row degree bound. Order zero starts the induction. When a row has degree at most two, expand along that row. For each supported column $p$, a normalized minor deletes the row and column $p$ and scales the remaining columns to obtain a unitary matrix. Deleting entries and scaling columns preserve the bound because neither operation creates a nonzero entry from a zero.
[Normalized minor](../Lean/MOC/SparseRow.lean#L19) · [Degree preservation](../Lean/MOC/SparseDegreeInduction.lean#L39)

The expansion uses the weights $|U_{ip}|^2$, whose sum is one. The term for column $p$ is the smaller determinant times $a_i+b_p$. Each smaller matching product times this factor gives an ambient matching product, by pairing $p$ with $i$. Convexity gives the ambient inclusion. For a low-degree column, exchange the spectra and apply the same expansion to $U^*$. The normalized minors of $U^*$ retain the column bound inherited from $U^*$. Take their adjoints to obtain smaller matrices with the required row bound, then use the induction hypothesis.
[Expansion and convexity](../Lean/MOC/SparseRow.lean#L248) · [Exchange of spectra](../Lean/MOC/Core.lean#L103) · [Induction](../Lean/MOC/SparseDegreeInduction.lean#L104)

If no row or column has degree at most two, then each row has degree three and each column has degree at least three. The sum of the row degrees equals the sum of the column degrees because each sum counts every nonzero entry once. The row sum is $3n$, so each column must also have degree three. The case with only the column bound follows by exchanging the spectra and taking the adjoint.
[Double count](../Lean/MOC/SupportDegreeBalance.lean#L10) · [Exact degrees](../Lean/MOC/SupportDegreeBalance.lean#L28)

When all degrees equal three, first test for a proper paired block split. Separate row and column permutations then give two nonempty square diagonal blocks. The blocks are unitary, have smaller order and retain the degree bound. The determinants multiply. A product of one matching product from each block is an ambient matching product, so the products of the two convex combinations lie in the ambient convex hull.
[Paired block definition](../Lean/MOC/Claim.lean#L37) · [Sparse block reduction](../Lean/MOC/SparsePairedBlocks.lean#L27) · [Product of convex-hull inclusions](../Lean/MOC/Blocks.lean#L32)

## Why exact degree three gives a small block

Orthogonality prevents two distinct rows from sharing exactly one nonzero position. If they shared only one, their inner product would contain one nonzero summand. The same argument applies to columns.
[Row orthogonality](../Lean/MOC/SparseUnitarySupport.lean#L33) · [Column orthogonality](../Lean/MOC/SparseUnitarySupport.lean#L55)

Fix a row $i$. Let $S$ be its three supported columns and let $R$ be the set of rows that meet $S$. Each column in $S$ has three nonzero entries, so there are nine nonzero positions in $R\times S$. Row $i$ accounts for three. Each other row in $R$ accounts for at least two. Thus $3\le |R|\le 4$. If $|R|=3$, all the positions in $R\times S$ are nonzero. The three rows have used all their nonzero entries, so their column neighborhood is $S$.
[Count of rows that meet $S$](../Lean/MOC/SparseUnitarySupport.lean#L63)

If $|R|=4$, each of the other three rows can meet at most one column outside $S$. Each such outside column that meets $R$ shares a row with some column in $S$. Column orthogonality forces a second shared row, which also lies in $R$. Two outside columns would therefore need four distinct rows other than $i$. Only three are available, so the column neighborhood of $R$ has at most four elements.
[Bound on the column neighborhood](../Lean/MOC/CubicSupportCut.lean#L11)

Without a proper paired block split, a nonempty proper row set has strictly more column neighbors than rows. Each row and column has squared norm one. The rows in the set contribute all their squared mass to its column neighbors. The column capacities therefore add up to at least the number of rows. If the counts are equal, the rows use all the capacity. The remaining rows then vanish on those columns, which gives a paired block split. In both neighborhood cases above, $R$ has at most $|R|$ column neighbors. Thus $R$ is the full row set and $n\le 4$.
[Strict expansion](../Lean/MOC/SupportBlocks.lean#L109) · [Order bound](../Lean/MOC/CubicSupportCut.lean#L100)

## The cases of order at most four

The inclusion holds for all unitary matrices of orders zero through three. At order four, exact degree three gives one zero in each row and one zero in each column. These zeros form a permutation. Relabel the columns to put the zeros on the diagonal, and apply the zero-diagonal unitary theorem. Relabeling also permutes the second spectrum and preserves the ambient matching hull.
[Small orders](../Lean/MOC/Small.lean#L68) · [Zero matching](../Lean/MOC/SparsePairedBlocks.lean#L66) · [Zero-diagonal unitary theorem](../Lean/MOC/OrderFourZeroDiagonalUnitary.lean#L196) · [Relabeling invariance](../Lean/MOC/Small.lean#L41)

## Total number of nonzero entries

Suppose $U$ has order $n$ and at most $n+8$ nonzero entries. The
inclusion holds for all pairs of spectra. For a row of degree at
most two, each normalized minor removes at least its nonzero pivot.
The order also drops by one, so the smaller matrix satisfies the
same bound.
[Count by matrix positions](../Lean/MOC/SparseSupportCardinality.lean#L12) · [Deletion](../Lean/MOC/SupportCardinalityDeletion.lean#L19)

Now suppose $n\ge 4$ and each row has at least three nonzero entries.
If one row has four or more, there are at least $3n+1>n+8$ nonzero
entries. Thus each row has degree three, and the row bound proves the
claim. At order four, the total bound is twelve in a matrix with
sixteen positions. Four zeros in any positions therefore suffice.
[All orders](../Lean/MOC/SparseSupportCardinality.lean#L58) · [Order four](../Lean/MOC/SparseSupportCardinality.lean#L74)

## One probability law for all spectra

Fix $U$. Under any of the three bounds above, there are real numbers
$w_\sigma\ge 0$ with $\sum_{\sigma\in S_n}w_\sigma=1$ such that, for
every pair of complex spectra $a,b$,

$$
\det\bigl(\mathrm{diag}(a)+U\,\mathrm{diag}(b)\,U^*\bigr)
=\sum_{\sigma\in S_n}w_\sigma\prod_{j=1}^n(a_{\sigma(j)}+b_j).
$$

[Definition](../Lean/MOC/UniversalMatchingWeights.lean#L13) · [Row bound](../Lean/MOC/SparseUnitaryUniversalWeights.lean#L69) · [Column bound](../Lean/MOC/SparseUnitaryUniversalWeights.lean#L84) · [Total count](../Lean/MOC/SparseUnitaryUniversalWeights.lean#L121)

The induction constructs the law. In orders at most three, one
permutation law represents the matrix of squared entry magnitudes.
Its singleton probabilities suffice for every pair of spectra. At a
row with at most two nonzero entries, choose column $p$ with probability
$|U_{ip}|^2$. Extend a permutation from its normalized minor by pairing
$p$ with $i$. For two diagonal blocks, choose their permutations
independently. These choices use only the entries of $U$. In the
remaining order-four case, the signed determinant terms already give
nonnegative weights.
[Small orders](../Lean/MOC/UniversalMatchingWeights.lean#L133) · [Row deletion](../Lean/MOC/SparseRowUniversalWeights.lean#L11) · [Independent blocks](../Lean/MOC/PairedBlockUniversalWeights.lean#L37) · [Order four](../Lean/MOC/SparseUnitaryUniversalWeights.lean#L17)

## Three zeros in order four

The following real orthogonal matrix has exactly three zero entries.
Its thirteen nonzero entries exceed the order-four bound by one.

$$
U=\frac{1}{\sqrt{21}}
\begin{pmatrix}
0&4&-1&2\\
-1&0&4&2\\
4&-1&0&2\\
2&2&2&-3
\end{pmatrix}.
$$

[Matrix](../Lean/MOC/OrderFourThreeZeroMinorObstruction.lean#L19) · [Unitarity](../Lean/MOC/OrderFourThreeZeroMinorObstruction.lean#L36) · [Zero positions](../Lean/MOC/OrderFourThreeZeroMinorObstruction.lean#L40)

Suppose one law works for all spectra. For sets of labels $I,J$ of
equal size, choose spectra with entries zero and one to isolate
the event $\sigma(J)=I$. Its probability must be the squared absolute
value of the minor with rows $I$ and columns $J$. The three diagonal
zeros therefore imply that the first three labels have zero probability
of being fixed.
[Spectral test](../Lean/MOC/SubsetMarkerTest.lean#L43) · [Minor probabilities](../Lean/MOC/SubsetMarkerTest.lean#L28)

Number the labels from one through four. On permutations of positive
probability, $\sigma(\{3,4\})=\{1,3\}$ implies
$\sigma(\{1,3\})=\{1,2\}$. The two minors prescribe probabilities
$4/441$ and $1/441$, respectively. The first event cannot have the
larger probability. This refutes one law for all spectra. The
determinant inclusion allows the weights to depend on the two spectra.
[Contradictory probabilities](../Lean/MOC/OrderFourThreeZeroMinorObstruction.lean#L65) · [Failure of a common law](../Lean/MOC/OrderFourThreeZeroMinorObstruction.lean#L112)

## Exact threshold in each order

Fix an order $n\ge 4$ and a nonnegative integer $t$. Every unitary of
order $n$ with at most $t$ nonzero entries has a common probability law
for all complex spectra if and only if $t\le n+8$.
[Exact threshold](../Lean/MOC/SparseSupportThreshold.lean#L89)

For the upper bound, put the preceding order-four matrix and the
identity matrix of order $n-4$ on the diagonal. This unitary has
$13+(n-4)=n+9$ nonzero entries. A common law would give probability
zero to every permutation that sends a label across the two blocks,
because each such matrix entry is zero. The restriction to the first
block would give a law for the order-four example. Its two minor
probabilities contradict that conclusion.
[Construction](../Lean/MOC/SparseSupportThreshold.lean#L72) · [Restriction of a law to a block](../Lean/MOC/UniversalWeightsBlockRestriction.lean#L15)

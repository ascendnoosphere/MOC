# Order-four complex Hadamard matrices

Let $A$ and $B$ be complex normal matrices of order four. Let $a_i$
and $b_i$ be their eigenvalues with multiplicity. The Marcus–de Oliveira
conjecture asks whether $\det(A+B)$ belongs to the real convex hull of
the matching products $\prod_j(a_{\sigma(j)}+b_j)$ over all permutations
$\sigma$.

In an eigenbasis of $A$, write $A=\mathrm{diag}(a)$ and
$B=U\mathrm{diag}(b)U^*$. Here $U$ is unitary and $U^*$ is its conjugate
transpose. If every entry of $U$ has modulus $1/2$, then $U$ is a
normalized complex Hadamard matrix. The inclusion holds for every such
$U$ and for all complex spectra $a,b$. One probability law on
permutations depends only on $U$ and gives the determinant for
every pair of spectra.
[Determinant inclusion](../Lean/MOC/OrderFourComplexHadamard.lean#L272) ·
[Common law](../Lean/MOC/OrderFourComplexHadamard.lean#L259)

## Complementary pairs

For row and column pairs $I,J$, let $q(I,J)$ be the squared modulus
of the corresponding two-by-two minor of $U$. The existing signed
determinant formula gives complex permutation weights whose sum is one.
Their total weight on the permutations that send $J$ to $I$ is
$q(I,J)$.
[Signed minor formula](../Lean/MOC/TwoValues.lean#L141)

Let $I^c$ be the complementary row pair. For any permutation $\sigma$,
the difference between the indicators of $\sigma(J)=I$ and
$\sigma(J)=I^c$ is $|I\cap\sigma(J)|-1$. Sum this identity with the
signed weights. The weighted sum of the intersection size is the sum
of the four singleton weights at rows in $I$ and columns in $J$. Each
is $1/4$, so this gives $q(I,J)=q(I^c,J)$. The complementary-minor
identity for unitary matrices also gives $q(I,J)=q(I,J^c)$.
[Row-complement equality](../Lean/MOC/OrderFourComplexHadamard.lean#L88) ·
[Unitary complementary minors](../Lean/MOC/FiniteMinorLaw.lean#L58)

## A law on the three partitions

There are three partitions of four indices into two complementary
pairs. Each permutation of the four indices induces a permutation of
these three partitions. For each pair of partitions, add the real
parts of the weights of permutations that send the column partition to the
row partition. The result is twice the corresponding squared minor,
since each of the two target row pairs has the same squared minor.
Thus the three-by-three matrix of these sums has nonnegative entries.
Every row and column sums to one because the induced maps are
permutations and the signed weights sum to one.

The Birkhoff decomposition gives a probability law on permutations of
the three partitions for this matrix. Lift each partition permutation
to a permutation of the four indices that fixes one index. Compose
with each of the four members of the Klein four group with equal
weight. This group consists of the identity and the three products of
two disjoint transpositions. The four compositions send any singleton
to each target index once. For each permitted target pair, exactly two
send the column pair to that target. Thus the lifted law gives the
correct squared minors of orders one and two. The total mass gives the
empty minor, and complementary minors give the remaining orders.
The determinant expansion then gives the inclusion for every pair of
spectra.
[Lifted probability law](../Lean/MOC/OrderFourComplexHadamard.lean#L259) ·
[Transfer to determinants](../Lean/MOC/FiniteMinorLaw.lean#L37)

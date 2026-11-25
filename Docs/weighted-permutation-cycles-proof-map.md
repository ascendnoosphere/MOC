# Weighted permutation cycles

Let $A$ and $B$ be complex normal matrices of the same finite order.
Write $a_i$ and $b_i$ for their eigenvalues, with multiplicity. The
Marcus–de Oliveira conjecture asks whether $\det(A+B)$ is in the real
convex hull of the products $\prod_j(a_{\sigma(j)}+b_j)$ for all
permutations $\sigma$.

This case uses a basis in which $A$ is diagonal. In this basis, suppose
$B$ is block diagonal. In each block, choose a permutation $p$ with
one cycle, one complex weight $w_j$ for each column $j$, and a complex
shift $c$. Define the weighted permutation matrix $W$ by putting
$w_j$ at row $p(j)$ in column $j$ and putting zero in the other
entries of column $j$. The block is $cI+W$, where $I$ is the identity
matrix of that block. The inclusion holds if $B$ is normal. Each block
can have a different size, shift, and set of weights.
[Finite block matrix theorem](../Lean/MOC/WeightedPermutationCycle.lean#L191)

## One block

For a cycle of length at least two, let $d_j$ be the diagonal entry of
$A+cI$ in column $j$. A nonzero term in the determinant uses row $j$
or row $p(j)$ in each column. If a term uses row $p(j)$ in column $j$,
column $p(j)$ must also use its cycle edge, because a permutation uses
each row once. Repetition follows the cycle through all indices. Thus
the determinant is $\prod_j d_j+\mathrm{sgn}(p)\prod_j w_j$, where
$\mathrm{sgn}(p)$ is the sign of $p$. This expression is invariant
under every permutation of the diagonal entries of $A$. The
invariance also holds for a block with at most one entry.
[Determinant formula](../Lean/MOC/WeightedPermutationCycle.lean#L73)

For a fixed unitary diagonalization of the block, the signed
determinant identity writes the determinant as a sum of matching
products with complex weights that sum to one. Average this identity
over all permutations of the diagonal entries of $A$. For each fixed
matching, its compositions with those permutations run through all
matchings exactly once. Thus every signed term has the same average
matching product. The signed weights sum to one, so the determinant
equals the uniform mean of the matching products. This mean gives a
real convex combination for every diagonal partner of the block.
[Signed identity](../Lean/MOC/Weights.lean#L41) ·
[Uniform-mean implication](../Lean/MOC/WeightedPermutationCycle.lean#L115) ·
[Uniform cycle law](../Lean/MOC/WeightedPermutationCycle.lean#L148) ·
[One-block inclusion](../Lean/MOC/WeightedPermutationCycle.lean#L175)

## Multiple blocks

Normality of $B$ gives normality of each block. Diagonalize the blocks
by separate unitary matrices, then apply the one-block law to each
block. The finite block result combines the block inclusions to give
the full inclusion. Its matchings assign the eigenvalue labels of each
block to the diagonal entries from that block. The result applies to
any labeling of the full eigenvalue list because relabeling preserves
the set of matching products.
[Finite block closure](../Lean/MOC/ExtendedCases.lean#L78) ·
[Relabeling](../Lean/MOC/Normal.lean#L151) ·
[Finite block matrix theorem](../Lean/MOC/WeightedPermutationCycle.lean#L191)

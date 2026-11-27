# Weighted permutation cycles

Let $A$ and $B$ be complex normal matrices of the same finite order.
Write $a_i$ and $b_i$ for their eigenvalues, with multiplicity. The
Marcus–de Oliveira conjecture asks whether $\det(A+B)$ is in the real
convex hull of the products $\prod_j(a_{\sigma(j)}+b_j)$ for all
permutations $\sigma$.

Take an orthonormal basis in which $A$ is diagonal and $B$ is block
diagonal. In each nonempty block, take a permutation $p$ that visits
all labels in one cycle. A block of order one uses the identity
permutation. Define $W$ by setting its entry at row $p(j)$ and column
$j$ to $w_j\in\mathbb C$. Set the other entries of that column to zero.
Suppose each block of $B$ has the form $cI+W$, where $c\in\mathbb C$
and $I$ is the identity matrix of that block. For every such normal
$B$ and every diagonal $A$, the inclusion holds. The sizes, shifts,
and weights can differ between blocks.
[Finite block matrix theorem](../Lean/MOC/WeightedPermutationCycle.lean#L191)

## One block

For a cycle of length at least two, let $d_j$ be the diagonal entry of
$A+cI$ in column $j$. A nonzero term in the determinant uses row $j$
or row $p(j)$ in each column. If a term uses row $p(j)$ in column $j$,
column $p(j)$ must also use its cycle edge, because a permutation uses
each row once. Repetition follows the cycle through all indices. Thus
the determinant is $\prod_j d_j+\mathrm{sgn}(p)\prod_j w_j$, where
$\mathrm{sgn}(p)$ is the sign of $p$. This expression is invariant
under every permutation of the diagonal entries of $A$. In a block
of order one the only diagonal permutation is the identity.
[Determinant formula](../Lean/MOC/WeightedPermutationCycle.lean#L73)

Fix a unitary diagonalization of the block. The signed determinant
identity writes the determinant as a sum of matching products with
complex weights that sum to one. Average this identity over all
permutations of the diagonal entries of $A$. The determinant stays
constant. Each matching product on the right runs through all matching
products, with one term for each permutation. Its average is the
uniform mean. The signed weights sum to one, so the determinant
equals this mean. The uniform law works for every diagonal partner
of the block.
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

## Lean check status

| Lean scope | Lean Checked? |
| --- | --- |
| The 4 source modules linked in this map | Yes |

[Status definitions](README.md#lean-check-status). Paper arguments retain their stated scope.

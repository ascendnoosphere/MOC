# Normal products

[Proof map index](README.md) · [All orders](all-orders-proof-map.md) · [Conjecture](../README.md#proof-tree)

Let $A$ and $B$ be complex normal matrices of the same finite order $n$.
Write $M^*$ for the conjugate transpose of a matrix $M$. Normality means
$M^*M=MM^*$. Let $a_1,\ldots,a_n$ and $b_1,\ldots,b_n$ enumerate the
eigenvalues of $A$ and $B$, with algebraic multiplicity. Let $S_n$ be the
permutation group on these labels.

Suppose $AB$ is normal. Then

$$
\det(A+B)\in\mathrm{conv}_{\mathbb R}
\left\{\prod_{j=1}^n(a_{\sigma(j)}+b_j):\sigma\in S_n\right\}.
$$

There is no bound on $n$. Either matrix can be singular. Both spectra can
have repeated eigenvalues. No commutation of $A$ and $B$ is required.
[Matrix theorem](../Lean/MOC/NormalProductInclusion.lean#L199) ·
[Spectral theorem](../Lean/MOC/NormalProductInclusion.lean#L165)

## Proof route

The Gram matrices are $P=A^*A$ and $Q=B^*B$. Both commute with both
summands. A Hermitian matrix equals its conjugate transpose. A common
Hermitian commuter is a Hermitian matrix that commutes with $A$ and $B$.
A reducing subspace is a subspace preserved by both matrices and their
adjoints.

```mermaid
flowchart TD
    N["A, B, and AB normal"]
    P["B commutes with P = A* A"]
    Q["A commutes with Q = B* B"]
    C["P and Q belong to the common Hermitian commutant"]
    R["OR"]
    S["Every common Hermitian commuter is scalar"]
    H["A nonscalar common Hermitian commuter exists"]
    G["P and Q are scalar"]
    B["Proper common reducing blocks"]
    T["Both spectra have constant modulus"]
    I["Induction within the normal-product class"]
    F["Concentric-circle inclusion"]
    D["Multiply the block convex combinations"]
    M["Determinant inclusion for this pair"]
    N --> P --> Q --> C --> R
    R --> S --> G --> T --> F --> M
    R --> H --> B --> I --> D --> M
```

The induction hypothesis covers only smaller pairs with a normal
product. The restriction of $AB$ to a common reducing block is the
product of the restricted matrices. That restriction remains normal.
Thus the proof does not assume unrestricted MOC in smaller orders.
[Complete induction](../Lean/MOC/NormalProductInclusion.lean#L165)

### Gram commutation

Choose a unitary eigenbasis of $A$. In this basis,
$A=\mathrm{diag}(a_1,\ldots,a_n)$. Write $B_{ij}$ for the entries of $B$
and put $q_i=|a_i|^2$. The row and column energy identities for $B$ and
$AB$ give

$$
\sum_{i,j}|B_{ji}|^2(q_i-q_j)^2=0.
$$

Each term is nonnegative. Therefore $B_{ij}=0$ whenever $q_i\ne q_j$.
This proves $PB=BP$.
[Energy identity](../Lean/MOC/RelativeUnitaryGram.lean#L72) ·
[Commutation](../Lean/MOC/RelativeUnitaryGram.lean#L108)

Normality of $AB$ and commutation of $P$ with $B$ give
$AQA^*=PQ$. Its $(i,j)$ entry is

$$
a_i Q_{ij}\overline{a_j}=|a_i|^2 Q_{ij}.
$$

If $a_i\ne0$ and $Q_{ij}\ne0$, cancellation gives $a_i=a_j$.
If $a_i=0$ and $a_j\ne0$, apply the reversed entry identity.
The equality $Q_{ji}=\overline{Q_{ij}}$ gives the same conclusion.
Thus $(a_i-a_j)Q_{ij}=0$ for all labels. This proves $AQ=QA$.
This argument includes zero eigenvalues.
[Entrywise proof](../Lean/MOC/RelativeUnitaryGram.lean#L115)

### Reduction and assembly

If the common Hermitian commutant contains only scalar matrices, then
$P=r^2I$ and $Q=s^2I$ for nonnegative real numbers $r,s$. Every eigenvalue
of $A$ has modulus $r$. Every eigenvalue of $B$ has modulus $s$.
The concentric-circle theorem gives the inclusion.
[Scalar commutant](../Lean/MOC/NormalRelativeInclusion.lean#L45) ·
[Concentric circles](../Lean/MOC/ConcentricPerturbation.lean#L131)

Otherwise, diagonalize a nonscalar common Hermitian commuter. Its
eigenspaces give proper common reducing blocks. Apply the same theorem
in the smaller orders. If the block weights are $u_\sigma$ and
$v_\tau$, use the products $u_\sigma v_\tau$. These weights are
nonnegative and sum to one. Each block matching extends to a matching
of the full spectra.
[Block assembly](../Lean/MOC/Blocks.lean#L31)

## Normal relative products

Suppose $A$ is invertible and $A^{-1}B$ is normal. The existing relative
Gram theorem gives $BP=PB$ and $AQ=QA$. These two equalities make $AB$
normal. Apply the normal-product theorem. This proves the determinant
inclusion without a scalar-commutant assumption and without any
lower-order MOC assumption.
[Spectral relative-product theorem](../Lean/MOC/NormalProductInclusion.lean#L177) ·
[Matrix relative-product theorem](../Lean/MOC/NormalProductInclusion.lean#L220)

```mermaid
flowchart LR
    R["A and B normal; A invertible; A inverse B normal"]
    G["Each matrix commutes with the other Gram matrix"]
    P["AB normal"]
    M["Determinant inclusion"]
    R --> G --> P --> M
```

[Relative Gram identities](../Lean/MOC/RelativeUnitaryGram.lean#L220) ·
[Normal-product criterion](../Lean/MOC/RelativeUnitaryGram.lean#L170)

## Interpretation and source

The Gram matrix records the squared change in length. The energy identity
prevents the other matrix from mixing unequal length levels. On each
irreducible common block, both length changes are constant. The phase
data can still vary. The circle theorem controls that remaining freedom.

In algebraic terms, the two positive Gram matrices are central in the
unital algebra generated by the summands and their adjoints. Common
Hermitian eigenspaces supply the decomposition used by the proof.
The Lean proof uses finite-dimensional matrix arguments directly.

The block structure for normal products is classical. See Theorem 1.1
and Section 3 of Aurelian Gheondea,
[When are the products of normal operators normal?](https://ssmr.ro/bulletin/pdf/52-2/Gheondeamod.pdf)
(2009). The paper attributes the finite-dimensional structure theorem
to Gantmaher and Krein (1930). Publication novelty of the determinant
corollary has not been established.

The unrestricted conjecture and the other proposed proof targets remain
separate claims. The normal-product theorem does not establish them.

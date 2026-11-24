# Marcus-de Oliveira formulations: Combinatorics, graphs and discrete mathematics

Atlas entries 172–183.

All eigenvalue lists use the indicated multiplicities. $`S_n`$ is the set of permutations of $`\{1,\ldots,n\}`$; $`U(n)`$ is the complex unitary group; $`*`$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. For normal operators the Marcus-de Oliveira conjecture compares the determinant of the sum over relative unitary positions with the convex hull of products of matched eigenvalue sums. The statements below identify the operator, its spectral length, and the determinant used in each setting. When the native object has no such determinant, the specified realization is part of the formulation.

## Complex spectral form and equivalence

The following statement is part of each numbered formulation. Use the finite spectral realization specified in that entry. For continuous spectral data use a finite sample or a finite spectral resolution. For infinite-dimensional data use a finite spectral subspace. If an entry has fixed rank, take finite direct sums of its realizations and select the required number of modes. When the datum is not a linear operator, use one orthogonal complex coordinate for each selected occurrence of the datum.

Let the two selected spaces have the same positive dimension $`N`$. Choose orthonormal spectral bases in these spaces, with rank-one projections $`P_j,Q_j`$ onto the basis lines. In a repeated eigenspace, choose an orthonormal basis to distinguish its occurrences. Denote the associated scalar or labelled spectral data by $`s_j,t_j`$, respectively. Let $`f,g`$ be arbitrary complex-valued functions of the labelled data $`(s_j,j)`$ and $`(t_j,j)`$. Set

```math
A_f=\sum_{j=1}^N f(s_j,j)P_j,\qquad B_g=\sum_{j=1}^N g(t_j,j)Q_j.
```

For every unitary identification $`U`$ of the second selected space with the first, the conjecture is

```math
\det(A_f+UB_gU^*)\in\mathrm{conv}\left\{\prod_{j=1}^N\big(f(s_j,j)+g(t_{\pi(j)},\pi(j))\big):\pi\in S_N\right\}.
```

The permutation weights may depend on both evaluations and on $`U`$. If the spectra are simple, the occurrence labels are unnecessary: functions of the spectral values suffice.

The forward implication follows from normality of the two diagonal spectral evaluations. For the reverse implication, take any two normal complex matrices of order $`N`$ and list their eigenvalues in orthonormal eigenbases. Select $`N`$ modes in the stated realization of each object and assign these eigenvalues to the two lists through $`f`$ and $`g`$. The relative unitary is unrestricted. The determinant and every permutation product then agree with the original matrix conjecture. Thus the complex spectral form, with all finite ranks and evaluations, is equivalent in both directions. Direct sums and arbitrary unitary mixing here concern the selected linear realizations, not necessarily operations on the native objects. The specific reverse reductions below avoid the extra labels or sums when possible. The native determinant, norm, volume or signed invariant is retained in each entry; an intrinsic comparison not given by this matrix realization requires its own justification.

## 172 Spectral graph theory

Let $`G,H`$ be undirected finite weighted graphs on $`n>0`$ vertices each, with real symmetric adjacency matrices $`A_G,A_H`$ and real eigenvalue lists $`\lambda_j,\mu_j`$. For every orthogonal $`Q`$ on the identified vertex space,

```math
\det(A_G+QA_HQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

In particular a permutation matrix $`Q`$ relabels the vertices of $`H`$, and the sum is the adjacency matrix of the weighted graph union. General orthogonal $`Q`$ does not necessarily preserve nonnegative edge weights.

**Equivalence reduction.** Use finite graphs with sufficiently many orthogonal adjacency modes. For example n disjoint weighted edges give n distinct positive adjacency eigenvalues after choosing different edge weights. Select one positive mode per edge and apply arbitrary complex functions.

## 173 Graph Laplacians

Let $`G,H`$ be connected undirected graphs with $`N\ge2`$ vertices and nonnegative edge weights. Let $`L_G,L_H`$ be their combinatorial Laplacians (degree minus adjacency). On the orthogonal complement $`E`$ of the all-ones vector put $`A=L_G|_E`$, $`B=L_H|_E`$, with $`n=N-1`$ positive eigenvalues $`\lambda_j,\mu_j`$. For every orthogonal $`Q`$ of $`E`$,

```math
\det_E(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

For a vertex relabeling fixing the all-ones vector, the determinant equals $`N`$ times the weighted spanning-tree sum of the graph union, by the matrix-tree theorem. The zero mode is omitted on both sides, with the common complement fixed.

**Equivalence reduction.** Use a connected weighted graph with sufficiently many positive Laplacian modes, such as a path on n+1 vertices. The positive modes have dimension n and a path has simple Laplacian spectrum. Complex spectral evaluation on its mean-zero space recovers all normal spectra.

## 174 Normalized graph Laplacians

Let $`G,H`$ be undirected weighted graphs of order $`n`$ with symmetric normalized Laplacians $`A=I-D_G^{-1/2}A_GD_G^{-1/2}`$ and $`B=I-D_H^{-1/2}A_HD_H^{-1/2}`$ (put zero rows and columns at isolated vertices). Let $`\lambda_j,\mu_j\in[0,2]`$ be their full spectra, including zeros. For every orthogonal $`Q`$,

```math
\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

A pseudodeterminant version must restrict to a fixed common positive invariant subspace. Even for a vertex permutation, the sum of normalized Laplacians need not be the normalized Laplacian of the union.

**Equivalence reduction.** Use the normalized Laplacian of a weighted or unweighted path, selecting n modes with distinct eigenvalues. Evaluate arbitrary complex functions before taking the determinant. The normalization and the interval from zero to two are properties of the original spectrum.

## 175 Directed graph spectra

Let $`G,H`$ be directed weighted graphs on $`n`$ vertices with complex adjacency matrices $`A,B`$ that are normal in the standard Hermitian vertex inner product. Let $`\lambda_j,\mu_j`$ be their characteristic roots. For every unitary $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

For a vertex permutation the determinant is that of a weighted directed union. Without normality the determinant hull can fail, as shown by two opposite single directed edges on two vertices.

**Equivalence reduction.** Use diagonal normal adjacency matrices of loop-weighted directed graphs with arbitrary complex weights. Every complex spectrum is available. If loops are excluded, select n modes of disjoint directed cycles with labelled eigenlines and evaluate arbitrary complex functions.

## 176 Graph Ihara zeta

Let $`G,H`$ be finite undirected graphs with the same number $`m>0`$ of edges. On the $`n=2m`$ directed-edge space let $`B_G,B_H`$ be their nonbacktracking adjacency operators: an arc can follow another when its initial vertex is the preceding terminal vertex and it is not the reversed arc. Assume these matrices normal for the chosen Hermitian edge products; let $`\lambda_j,\mu_j`$ be their spectra. For every unitary $`U`$ and $`z\in\mathbb C`$,

```math
\det(I-z(B_G+UB_HU^*))\in\mathrm{conv}\left\{\prod_{j=1}^n(1-z(\lambda_j+\mu_{\pi(j)})):\pi\in S_n\right\}.
```

For each graph separately the inverse Ihara zeta function is $`\det(I-zB_G)`$. The left side is the characteristic determinant for the combined transition operator, not necessarily that of a graph. Nonnormal nonbacktracking matrices require a separate normal realization or additional hypotheses.

**Equivalence reduction.** Use disjoint cycles of sufficient total edge count; their nonbacktracking edge transitions are permutations and hence normal. Select n labelled eigenmodes and apply arbitrary complex functions. A nonzero pointwise characteristic parameter can be absorbed by an affine shift.

## 177 Graph cycle and cut spaces

Let $`G,H`$ be finite undirected graphs with their oriented edge spaces and standard Euclidean inner products. Choose either cycle spaces $`\ker\partial_G,\ker\partial_H`$ or cut spaces $`\mathrm{im}\partial_G^T,\mathrm{im}\partial_H^T`$ of equal positive dimension $`n`$; $`\partial`$ is the vertex-edge incidence map. Let $`A,B`$ be self-adjoint restrictions or orthogonal compressions of specified graph edge operators to those spaces. With eigenvalues $`\lambda_j,\mu_j`$ and any orthogonal identification $`Q`$,

```math
\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

For cycle spaces $`n`$ is the edge count minus vertex count plus component count; for cut spaces it is vertex count minus component count. The determinant comparison is separate for each choice.

**Equivalence reduction.** Use n independent cycle-space or cut-space coordinates, for example disjoint cycles or a tree with n edges. Choose a self-adjoint operator with distinct real values on these orthogonal coordinates and evaluate arbitrary complex functions there.

## 178 Electrical networks

Let two connected resistive networks have $`N\ge2`$ common labeled vertices, positive conductances, and a common grounded vertex. Delete its row and column from each conductance Laplacian to obtain positive definite reduced matrices $`A,B`$ of order $`n=N-1`$. Let $`\lambda_j,\mu_j`$ be their eigenvalues. For each orthogonal $`Q`$,

```math
\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

For a permutation of ungrounded vertices, the sum is the reduced conductance Laplacian of networks connected in parallel at corresponding vertices. Its determinant is the sum of products of conductances over spanning trees.

**Equivalence reduction.** Use star networks with the common central vertex grounded. The reduced Laplacian is diagonal with the positive conductances of the n branches. These may be distinct. Complex spectral evaluation gives every complex list, although the tree-sum interpretation uses the positive native form.

## 179 Hypergraph spectra

Let two finite weighted hypergraphs on $`n>0`$ vertices have incidence matrices $`H_1,H_2`$, with nonnegative diagonal hyperedge weight matrices $`W_1,W_2`$. Fix the positive incidence Gram model $`A=H_1W_1H_1^T`$, $`B=H_2W_2H_2^T`$. Let $`\lambda_j,\mu_j`$ be their $`n`$ nonnegative eigenvalues. For every orthogonal $`Q`$,

```math
\det(H_1W_1H_1^T+QH_2W_2H_2^TQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The incidence Gram model is specified because hypergraph adjacency tensors, tensor eigenvalues and Laplacian matrices need not have the same spectra or determinants.

**Equivalence reduction.** Use n singleton hyperedges of distinct positive weights. The incidence Gram matrix is diagonal with those weights. Complex spectral evaluation on the vertex modes recovers arbitrary spectra.

## 180 Simplicial Laplacians

Let $`K,L`$ be finite simplicial complexes with equal positive $`k`$-simplex count $`n`$, and let $`A=\partial_{k+1}\partial_{k+1}^*+\partial_k^*\partial_k`$ and $`B`$ be their degree-$`k`$ combinatorial Laplacians, with orthonormal oriented simplex bases. For their eigenvalues $`\lambda_j,\mu_j\ge0`$ and every unitary identification $`U`$ of the chain spaces,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

If using higher-dimensional tree invariants derived from pseudodeterminants, restrict both operators to identified positive spectral subspaces of the same dimension and use only those positive eigenvalues. The complete formula includes zero modes.

**Equivalence reduction.** Use finite simplicial complexes with sufficiently many k-simplex modes. For example take n disjoint simplices and choose labelled chain spectral lines. Apply arbitrary complex values to the selected modes. Retain the dimension of the selected spectral space, not the Betti number unless they agree.

## 181 Cellular sheaf Laplacians

Let $`\mathcal F,\mathcal G`$ be finite cellular sheaves of complex Hilbert spaces on finite cell complexes. In degree $`k`$ let their cochain stalk sums have the same positive dimension $`n`$. With coboundaries $`\delta_\mathcal F,\delta_\mathcal G`$, define $`A=\delta_\mathcal F^*\delta_\mathcal F+\delta_\mathcal F\delta_\mathcal F^*`$ in degree $`k`$, and define $`B`$ likewise. Let $`\lambda_j,\mu_j`$ be their nonnegative spectra. For every unitary identification $`U`$ of the cochain spaces,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The kernel dimensions equal the corresponding sheaf cohomology ranks. A pseudodeterminant version uses fixed positive blocks and does not assume the sum is another cellular sheaf Laplacian.

**Equivalence reduction.** Use a cellular sheaf on n isolated vertices with one-dimensional stalks. Its degree-zero cochain space has n independent labelled lines, even if the Laplacian is zero. Complex spectral evaluations distinguish those lines and give arbitrary normal spectra.

## 182 Incidence algebras of finite posets

Let $`P`$ be a finite poset of cardinality $`n>0`$. In a chosen linear extension of its order, identify its complex incidence algebra with upper triangular matrices supported on comparable pairs. For elements $`a,b`$ let $`A,B`$ be these triangular representations, and list their diagonal entries $`\lambda_j,\mu_j`$. For every invertible $`V`$ for which $`VBV^{-1}`$ is upper triangular in the same order and has diagonal a permutation of $`\mu`$,

```math
\det(A+VBV^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The sum is triangular and its determinant is one of the permutation products. If $`A,B`$ are normal in this orthonormal order basis they are diagonal, and the full unitary matrix version also applies. A general unitary conjugation of a nonnormal triangular operator is not covered.

**Equivalence reduction.** Use the incidence algebra of the discrete poset on n elements. It consists of diagonal matrices with arbitrary complex entries. Its normal spectral realization with all relative unitary positions is the full conjecture; the triangular-preserving orbit alone yields permutation values.

## 183 Bipartite matchings and assignment

Let $`\lambda_j,\mu_j\in\mathbb C`$, $`1\le j\le n`$, be labels on the two parts of a complete bipartite graph. Assign edge $`(i,j)`$ the complex factor $`\lambda_i+\mu_j`$. For each perfect matching $`\pi\in S_n`$ define its product $`d_\pi=\prod_i(\lambda_i+\mu_{\pi(i)})`$. Let $`A=\mathrm{diag}(\lambda)`$, $`B=\mathrm{diag}(\mu)`$ and $`U\in U(n)`$. The matching form states that there is a probability distribution $`w_\pi`$ on perfect matchings such that

```math
\det(A+UBU^*)=\sum_{\pi\in S_n}w_\pi d_\pi,\qquad w_\pi\ge0,\quad\sum_\pi w_\pi=1.
```

This is the exact matrix conjecture expressed as an expected matching product. A doubly stochastic matrix specifies single-edge marginals; it does not determine all joint subset probabilities. A permanent sums all matching products rather than providing the required convex weights.

**Equivalence reduction.** Already equivalent: the two complex labels on each part may be arbitrary, and any relative unitary matrix is allowed. The probability weights need only represent the scalar matching product for the chosen labels.


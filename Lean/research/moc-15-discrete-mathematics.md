# Marcus-de Oliveira formulations: Combinatorics, graphs and discrete mathematics

Atlas entries 172–183.

All eigenvalue lists use the indicated multiplicities. $S_n$ is the set of permutations of $\{1,\ldots,n\}$; $U(n)$ is the complex unitary group; $*$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. For normal operators the Marcus-de Oliveira conjecture compares the determinant of the sum over relative unitary positions with the convex hull of products of matched eigenvalue sums. The statements below identify the operator, its spectral length, and the determinant used in each setting. When the native object has no such determinant, the specified realization is part of the formulation.

## 172 Spectral graph theory

Let $G,H$ be undirected finite weighted graphs on $n>0$ vertices each, with real symmetric adjacency matrices $A_G,A_H$ and real eigenvalue lists $\lambda_j,\mu_j$. For every orthogonal $Q$ on the identified vertex space,

$$\det(A_G+QA_HQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

In particular a permutation matrix $Q$ relabels the vertices of $H$, and the sum is the adjacency matrix of the weighted graph union. General orthogonal $Q$ does not necessarily preserve nonnegative edge weights.

## 173 Graph Laplacians

Let $G,H$ be connected undirected graphs with $N\ge2$ vertices and nonnegative edge weights. Let $L_G,L_H$ be their combinatorial Laplacians (degree minus adjacency). On the orthogonal complement $E$ of the all-ones vector put $A=L_G|_E$, $B=L_H|_E$, with $n=N-1$ positive eigenvalues $\lambda_j,\mu_j$. For every orthogonal $Q$ of $E$,

$$\det_E(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

For a vertex relabeling fixing the all-ones vector, the determinant equals $N$ times the weighted spanning-tree sum of the graph union, by the matrix-tree theorem. The zero mode is omitted on both sides, with the common complement fixed.

## 174 Normalized graph Laplacians

Let $G,H$ be undirected weighted graphs of order $n$ with symmetric normalized Laplacians $A=I-D_G^{-1/2}A_GD_G^{-1/2}$ and $B=I-D_H^{-1/2}A_HD_H^{-1/2}$ (put zero rows and columns at isolated vertices). Let $\lambda_j,\mu_j\in[0,2]$ be their full spectra, including zeros. For every orthogonal $Q$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

A pseudodeterminant version must restrict to a fixed common positive invariant subspace. Even for a vertex permutation, the sum of normalized Laplacians need not be the normalized Laplacian of the union.

## 175 Directed graph spectra

Let $G,H$ be directed weighted graphs on $n$ vertices with complex adjacency matrices $A,B$ that are normal in the standard Hermitian vertex inner product. Let $\lambda_j,\mu_j$ be their characteristic roots. For every unitary $U$,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

For a vertex permutation the determinant is that of a weighted directed union. Without normality the determinant hull can fail, as shown by two opposite single directed edges on two vertices.

## 176 Graph Ihara zeta

Let $G,H$ be finite undirected graphs with the same number $m>0$ of edges. On the $n=2m$ directed-edge space let $B_G,B_H$ be their nonbacktracking adjacency operators: an arc can follow another when its initial vertex is the preceding terminal vertex and it is not the reversed arc. Assume these matrices normal for the chosen Hermitian edge products; let $\lambda_j,\mu_j$ be their spectra. For every unitary $U$ and $z\in\mathbb C$,

$$\det(I-z(B_G+UB_HU^*))\in\mathrm{conv}\left\{\prod_{j=1}^n(1-z(\lambda_j+\mu_{\pi(j)})):\pi\in S_n\right\}.$$

For each graph separately the inverse Ihara zeta function is $\det(I-zB_G)$. The left side is the characteristic determinant for the combined transition operator, not necessarily that of a graph. Nonnormal nonbacktracking matrices require a separate normal realization or additional hypotheses.

## 177 Graph cycle and cut spaces

Let $G,H$ be finite undirected graphs with their oriented edge spaces and standard Euclidean inner products. Choose either cycle spaces $\ker\partial_G,\ker\partial_H$ or cut spaces $\mathrm{im}\partial_G^T,\mathrm{im}\partial_H^T$ of equal positive dimension $n$; $\partial$ is the vertex-edge incidence map. Let $A,B$ be self-adjoint restrictions or orthogonal compressions of specified graph edge operators to those spaces. With eigenvalues $\lambda_j,\mu_j$ and any orthogonal identification $Q$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

For cycle spaces $n$ is the edge count minus vertex count plus component count; for cut spaces it is vertex count minus component count. The determinant comparison is separate for each choice.

## 178 Electrical networks

Let two connected resistive networks have $N\ge2$ common labeled vertices, positive conductances, and a common grounded vertex. Delete its row and column from each conductance Laplacian to obtain positive definite reduced matrices $A,B$ of order $n=N-1$. Let $\lambda_j,\mu_j$ be their eigenvalues. For each orthogonal $Q$,

$$\det(A+QBQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

For a permutation of ungrounded vertices, the sum is the reduced conductance Laplacian of networks connected in parallel at corresponding vertices. Its determinant is the sum of products of conductances over spanning trees.

## 179 Hypergraph spectra

Let two finite weighted hypergraphs on $n>0$ vertices have incidence matrices $H_1,H_2$, with nonnegative diagonal hyperedge weight matrices $W_1,W_2$. Fix the positive incidence Gram model $A=H_1W_1H_1^T$, $B=H_2W_2H_2^T$. Let $\lambda_j,\mu_j$ be their $n$ nonnegative eigenvalues. For every orthogonal $Q$,

$$\det(H_1W_1H_1^T+QH_2W_2H_2^TQ^T)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The incidence Gram model is specified because hypergraph adjacency tensors, tensor eigenvalues and Laplacian matrices need not have the same spectra or determinants.

## 180 Simplicial Laplacians

Let $K,L$ be finite simplicial complexes with equal positive $k$-simplex count $n$, and let $A=\partial_{k+1}\partial_{k+1}^*+\partial_k^*\partial_k$ and $B$ be their degree-$k$ combinatorial Laplacians, with orthonormal oriented simplex bases. For their eigenvalues $\lambda_j,\mu_j\ge0$ and every unitary identification $U$ of the chain spaces,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

If using higher-dimensional tree invariants derived from pseudodeterminants, restrict both operators to identified positive spectral subspaces of the same dimension and use only those positive eigenvalues. The complete formula includes zero modes.

## 181 Cellular sheaf Laplacians

Let $\mathcal F,\mathcal G$ be finite cellular sheaves of complex Hilbert spaces on finite cell complexes. In degree $k$ let their cochain stalk sums have the same positive dimension $n$. With coboundaries $\delta_\mathcal F,\delta_\mathcal G$, define $A=\delta_\mathcal F^*\delta_\mathcal F+\delta_\mathcal F\delta_\mathcal F^*$ in degree $k$, and define $B$ likewise. Let $\lambda_j,\mu_j$ be their nonnegative spectra. For every unitary identification $U$ of the cochain spaces,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The kernel dimensions equal the corresponding sheaf cohomology ranks. A pseudodeterminant version uses fixed positive blocks and does not assume the sum is another cellular sheaf Laplacian.

## 182 Incidence algebras of finite posets

Let $P$ be a finite poset of cardinality $n>0$. In a chosen linear extension of its order, identify its complex incidence algebra with upper triangular matrices supported on comparable pairs. For elements $a,b$ let $A,B$ be these triangular representations, and list their diagonal entries $\lambda_j,\mu_j$. For every invertible $V$ for which $VBV^{-1}$ is upper triangular in the same order and has diagonal a permutation of $\mu$,

$$\det(A+VBV^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The sum is triangular and its determinant is one of the permutation products. If $A,B$ are normal in this orthonormal order basis they are diagonal, and the full unitary matrix version also applies. A general unitary conjugation of a nonnormal triangular operator is not covered.

## 183 Bipartite matchings and assignment

Let $\lambda_j,\mu_j\in\mathbb C$, $1\le j\le n$, be labels on the two parts of a complete bipartite graph. Assign edge $(i,j)$ the complex factor $\lambda_i+\mu_j$. For each perfect matching $\pi\in S_n$ define its product $d_\pi=\prod_i(\lambda_i+\mu_{\pi(i)})$. Let $A=\mathrm{diag}(\lambda)$, $B=\mathrm{diag}(\mu)$ and $U\in U(n)$. The matching form states that there is a probability distribution $w_\pi$ on perfect matchings such that

$$\det(A+UBU^*)=\sum_{\pi\in S_n}w_\pi d_\pi,\qquad w_\pi\ge0,\quad\sum_\pi w_\pi=1.$$

This is the exact matrix conjecture expressed as an expected matching product. A doubly stochastic matrix specifies single-edge marginals; it does not determine all joint subset probabilities. A permanent sums all matching products rather than providing the required convex weights.

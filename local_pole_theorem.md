# A local extension of the Hermitian interlacing argument

Work in the difference convention. The sum convention follows by replacing the second matrix by its negative. A generalized circle is a circle or a straight line in the Riemann sphere.

**Theorem.** Let A and B be normal operators on a complex Hilbert space of finite dimension n. Suppose there are orthogonal projections P and Q with P ≤ Q, AP = PA, and BQ = QB. Suppose the spectra of A on ran P and B on ran Q lie on one generalized circle Γ. If rank P ≥ n−3, then the scalar Marcus–de Oliveira inclusion holds for A−B.

The condition on ran P is imposed only on eigenvalues whose eigenvectors belong to that subspace. The remaining eigenvalues of both operators can be arbitrary complex numbers. Setting Q = I gives the projective form of Shitov's 2025 theorem. The case P < Q < I permits both full spectra to be nonconcyclic.

## Proof

Use induction on n. Dimensions at most three satisfy the unrestricted theorem. In a higher dimension, fix a unit A-eigenvector h in ran P, with eigenvalue p on Γ. Set V = h-perp and let E be the orthogonal projection onto V. First assume p is simple in A and does not belong to the spectrum of B. Put F = A−pI and G = B−pI. In the decomposition spanned by h and V, F has the form 0 direct sum F0, with F0 invertible. Block expansion gives

    det(A−B) = H det(F0⁻¹ − (E G⁻¹)|V),
    H = (−1)^n det(G) det(F0).

Indeed det(A−B) = (−1)^n det(G) det(I−F G⁻¹). The first row of the latter determinant is the first row of the identity. Upon relabeling h as the first row, the same nonzero factor H works for every permutation vertex:

    product_i (a_i−b_{π(i)}) = H product_{i≠1} (a'_i−b'_{π(i)}),
    a'_i = 1/(a_i−p),       b'_j = 1/(b_j−p).

The map z ↦ 1/(z−p) sends Γ to an affine real line L, because p belongs to Γ. Let Q0 and P0 be the restrictions to V of Q−hh* and P−hh*. Then P0 ≤ Q0. The compression C = (E G⁻¹)|V is a direct sum. On ran Q0, it is a compression of a normal matrix with all eigenvalues on L. After translation and rotation, that matrix is Hermitian. On ran(I−Q), compression leaves G⁻¹ unchanged. Thus C is normal and commutes with Q0, and its eigenvalues on ran Q0 lie on L. The operator F0⁻¹ commutes with P0 and its eigenvalues on ran P0 lie on L. Since rank P0 ≥ (n−1)−3, the induction hypothesis encloses the reduced determinant in its permutation hull.

It remains to lift each reduced vertex. The eigenvalues of C on ran(I−Q) are untouched b'_j values. Fix their assignments. On the active block, translation and rotation give an interlacing list y1 ≤ c1 ≤ y2 ≤ ... ≤ c_(r−1) ≤ yr by the Cauchy interlacing theorem, where r = rank Q. Shitov's Lemma 17 shows that each product with the compressed c values is in the convex hull of products with distinct y values. The other factors in that vertex stay fixed. Equivalently, each lifted vertex is an injection of the n−1 remaining rows into the n original columns. Complete this injection with the unique omitted column and multiply by H. The result is an original permutation vertex.

For clarity, the interlacing lemma even supplies probabilities independent of all the other complex factors. First assign position r−1 to endpoint y_(r−1) or yr with mean c_(r−1). After either endpoint is removed, the remaining y values still interlace c1,...,c_(r−2). Continue recursively. Conditional expectation, starting from the last assignment, gives the required product identity for every choice of the scalar factors. Equal endpoints use deterministic assignment. The r = 1 block has an empty product.

When the first pole is repeated or belongs to the spectrum of B, perturb eigenvalues in eigenbases adapted to P and Q, preserving Γ on their respective subspaces. P, Q, and their inclusion stay fixed. Apply the preceding step and pass to the limit. The determinant and the finite list of vertices are continuous, and the simplex of probability weights is compact. This proves the theorem.

## Four dimensions through a failed common-law test

In coordinates numbered 0 to 3, apply real Givens rotations on (0,1), (1,2), (2,3), and (3,0), in that order. The real blocks have rows (c,s), (−s,c). Choose (c,s) = (3/5, 4/5) for the first three rotations and (5/13, 12/13) for the last. The resulting relative eigenbasis matrix is

    [1143/1625    −76/1625     144/325    −36/65]
    [  −12/25        9/25         4/5          0]
    [  48/125     −36/125        9/25        4/5]
    [ 116/325     288/325      −12/65       3/13].

Write K(I,J) = |det U[I,J]|². Single digits below denote singleton sets and pairs of digits denote two-element sets. Each of the 24 permutations obeys

    K(0,1) + K(1,3) − K(02,12) + K(03,23) ≥ 0.

For this U, the left side is −2048/203125. Thus no common probability law reproduces every squared minor. Still, row 1 is supported on columns 0,1,2, so the theorem proves scalar MOC whenever a1,b0,b1,b2 lie on a generalized circle, with all remaining eigenvalues arbitrary.

For example let a = (i,3,1+2i,2+5i), b = (0,1,2,2+i). Neither quadruple is concyclic and no two eigenvalues from opposite spectra are equal. The determinant is (11280200−1893872i)/528125. Three permutation products are 10−10i, 10−4i, and 60. The respective weights 43548/528125, 364598/528125, and 119979/528125 give this determinant exactly.

## Five dimensions

Use a chronological five-cycle (0,1), (1,2), (2,3), (3,4), (4,0), with arbitrary rotation angles and phases. Rows 1 and 2 are supported on columns 0,1,2,3. Therefore, if a1,a2,b0,b1,b2,b3 lie on a generalized circle, the theorem applies for all values of a0,a3,a4,b4. It also applies at phases where the five-cycle common-law test fails for balanced rotations.

**Source.** Y. Shitov, *A further sufficient condition for the determinantal conjecture*, Izvestiya: Mathematics 89 (2025), 862–869, Theorem 1 and Lemma 17. DOI 10.4213/im9292e.

## Several active circles

The theorem also applies to a family of pairwise orthogonal B-reducing spaces Q_l. Suppose each Q_l contains an A-reducing space P_l. Assume the eigenvalues of A on P_l and B on Q_l lie on a generalized circle Γ_l, which may depend on l. If the sum of the dimensions of the P_l is at least n−3, the same induction applies. A pole step on Q_l leaves the other Q spaces intact, and the reciprocal map takes each of their circles to a generalized circle. In five dimensions this includes disjoint row supports of sizes three and two. Only the three eigenvalues in the first support need share a circle with its row eigenvalue. Any three points in the second group lie on some generalized circle.

## A quantitative open set beyond the common-law condition

At the rational four-cycle example the distance from the determinant to every side of the three-vertex triangle exceeds 0.49. The smallest distance is (43548/528125) times 300 divided by √2516. Let all eigenvalues vary independently by at most 10⁻⁵ and let the unitary vary by at most 10⁻⁵ in operator norm. All resulting difference matrices have norm less than 9. For square matrices of size four and norms at most 9, multilinearity in the columns and Hadamard's inequality give |det X−det Y| ≤ 4·9³‖X−Y‖. The determinant thus moves by less than 0.234 and each selected vertex by less than 0.059. The support inequality for the triangle remains strict in every direction. At the same time, the four-term common-law witness moves at most 12·10⁻⁵, because ‖ΛᵏU−ΛᵏV‖ ≤ k‖U−V‖ and the individual minor moduli are at most one. The common-law violation therefore remains strict throughout this neighborhood. The neighborhood includes dense relative eigenbases and allows independent perturbations of the spectral points off the active circle.

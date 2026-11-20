# MOC at overlap three

## Theorem

Let $A$ and $B$ be normal complex $n\times n$ matrices. Fix $\mu\in\mathbb C$. Let $a_1,\ldots,a_r$ and $b_1,\ldots,b_s$ be the nonzero eigenvalues of $A-\mu I$ and $B+\mu I$, respectively, with multiplicity. Assume $r+s=n+3$. The Marcus–de Oliveira inclusion holds if either reciprocal list $x_i=1/a_i$ or $y_j=1/b_j$ satisfies one of the following conditions.

1. The list has at most two distinct values.
2. The list lies on a real affine line in $\mathbb C$, has at least two distinct values, and each endpoint of its convex hull occurs at least twice.

The other list may contain arbitrary nonzero complex numbers. For example, the theorem applies in size nine when the first shifted spectrum is $(0,0,0,u,u,u,v,v,v)$ for distinct nonzero $u,v$, and the second shifted spectrum has three zeros and six arbitrary nonzero values. The argument gives an explicit probabilistic representation. No claim of publication priority is made.

## 1. Reduction to a three-dimensional intersection

Opposite shifts preserve both the sum and every permutation product. Write the shifted matrices as $X D_a X^*$ and $Y D_b Y^*$, where $X$ and $Y$ have orthonormal columns and $D_a,D_b$ are the diagonal matrices of the displayed nonzero eigenvalues. Define $T=[X\;Y]$ and $D=\prod_i a_i\prod_j b_j$. If $T$ has rank less than $n$, the sum is singular. Both $r$ and $s$ are then less than $n$, so a permutation can pair a zero from each spectrum. Its vertex is zero, which proves the inclusion in this case.

Suppose $T$ has rank $n$. The ranges of $X$ and $Y$ span $\mathbb C^n$ and have an intersection of dimension three. Let $W$ have orthonormal columns spanning that intersection. Set $E=X^*W$ and $F=Y^*W$. Both matrices have three orthonormal columns. Then

$$
\det(A+B)=D q\det(E^*D_x E+F^*D_yF),\qquad q=2^{-3}\det(TT^*),\qquad 0<q\le1. \tag{1}
$$

To verify the identity, let $V=(TT^*)^{-1/2}T$. Its rows are orthonormal. The columns of $K=2^{-1/2}(E^{\mathsf T},-F^{\mathsf T})^{\mathsf T}$ form an orthonormal basis of $\ker T$. For each set $S$ of $n$ column labels, complementary minors of the unitary matrix with row blocks $V$ and $K^*$ give $|\det V_{:,S}|^2=|\det K_{S^c,:}|^2$. Apply Cauchy–Binet to $T\operatorname{diag}(a,b)T^*$. Factor out $D\det(TT^*)$ and apply Cauchy–Binet to $K^*\operatorname{diag}(x,y)K$. This gives (1). The positive operator $TT^*=XX^*+YY^*$ equals $2I$ on the common three-space. On its orthogonal complement it has trace $n-3$, so its determinant there is at most one by the arithmetic–geometric mean inequality. The empty complement contributes one.

Consider a three-edge matching between the $r$ nonzero labels of the first matrix and the $s$ nonzero labels of the second. It extends to a permutation by pairing all other nonzero labels with zeros on the opposite side. There are exactly enough zeros because $r+s=n+3$. Its vertex is

$$
D\prod_{(i,j)\text{ in the matching}}(x_i+y_j). \tag{2}
$$

It suffices to express the three-dimensional determinant in (1) as an average of the products in (2) divided by $D$. If $r,s<n$, use the permutation vertex zero with probability $1-q$. If $r=n$ or $s=n$, one support projection is $I$ and the other has rank three, so $q=1$.

## 2. Sampling the eigenvalues of a Hermitian compression

Suppose $h_1\le \cdots\le h_m$ are real. Let $\lambda_1\le\cdots\le\lambda_k$ be the eigenvalues of a $k$-dimensional compression of a Hermitian matrix with eigenvalues $h_1,\ldots,h_m$. There is a random injection $\pi:[k]\to[m]$ such that, for every subset $S\subseteq[k]$,

$$
\mathbb E\prod_{i\in S}h_{\pi(i)}=\prod_{i\in S}\lambda_i. \tag{3}
$$

For a compression of codimension one, Cauchy interlacing gives $h_i\le\lambda_i\le h_{i+1}$. Choose one of the two largest labels with probabilities such that its value has mean $\lambda_{m-1}$. Assign that label to slot $m-1$ and delete it. The lower $m-2$ values still interlace the remaining labels for either choice. Induction supplies a conditional injection for the lower slots. For a product containing the last slot, the conditional expected product of the lower slots is the same in both branches, so taking expectation gives (3). If the two largest values coincide, either label can serve. For higher codimension, pass through a chain of subspaces with successive codimension one. Compose the independent injections for the successive eigenvalue lists and condition on their chosen indices. Distinct indices at each stage allow (3) to be applied at the next stage.

Shitov's Lemma 17 uses the same endpoint deletion for a fixed product. Keeping the endpoint probabilities gives the simultaneous moment identity (3). His Corollary 18 applies interlacing to determinant polygons. [Y. N. Shitov, *A further sufficient condition for the determinantal conjecture*, Izvestiya: Mathematics 89 (2025), 862–869, §3](https://www.mathnet.ru/eng/im9292).

Any multiaffine polynomial is a linear combination of the monomials in (3). Consequently (3) remains valid after replacing each real coordinate by the same affine function $h\mapsto u+v h$ with complex $u,v$. It applies to either list in the theorem: a list with at most two distinct values also lies on such a line.

## 3. Reduction to triples with repeated values

Use symmetry to put the hypothesis on $x$. Choose a basis of the common three-space that diagonalizes $C=E^*D_xE$. Such a basis exists because $C$ is an affine complex function of a Hermitian compression. In this basis, write $C=\operatorname{diag}(\lambda_1,\lambda_2,\lambda_3)$ and $H=F^*D_yF$. Equation (3) represents the multiaffine function $\det(\operatorname{diag}(\lambda_1,\lambda_2,\lambda_3)+H)$ as an average over ordered triples of distinct $x$-labels.

Under condition 1, each selected triple already has at most two distinct values. Under condition 2, let $u,v$ be the two global endpoint values. Whenever a selected triple has three distinct values, choose one value strictly between $u$ and $v$. Replace it by an endpoint, with probabilities giving that value as the mean. Each endpoint occurs at most once in the current triple. Since the original spectrum has two labels at each endpoint, the replacement can always use a label outside the two retained slots. This step preserves the conditional expectation of every multiaffine function. Each step reduces the number of interior entries by one, so the process stops after at most three steps. The final triple has at most two distinct values and still uses three distinct original labels.

## 4. A positive matching for each selected triple

After permuting the basis for a fixed triple, its values have the form $(c,c,d)$. The scalar case has $d=c$. Let $F_0$ be the first two columns of $F$ in this basis and let $H_0=F_0^*D_yF_0$. Expansion in the last diagonal entry gives

$$
\det(\operatorname{diag}(c,c,d)+H)=\det(cI_3+H)+(d-c)\det(cI_2+H_0). \tag{4}
$$

Define probabilities on pairs $S$ and triples $J$ of distinct column labels by $p_S=|\det(F_0)_{S,:}|^2$ and $p_J=|\det F_{J,:}|^2$. Each family sums to one by Cauchy–Binet. There is a coupling with $S\subset J$ almost surely. Here is a finite proof. Let $f_1,f_2,f_3$ be the columns of $F$, $\xi=f_1\wedge f_2$, and $\zeta=f_1\wedge f_2\wedge f_3$. Contraction by $f_3$ sends $\zeta$ to $\xi$ and has operator norm one. For any family $\mathcal S$ of coordinate pairs, only triples in its upper shadow $\mathcal J=\{J:J\supset S\text{ for some }S\in\mathcal S\}$ can contribute to the $\mathcal S$-coordinates of this contraction. Coordinate projection and contraction both have norm at most one. Thus $\sum_{S\in\mathcal S}p_S\le\sum_{J\in\mathcal J}p_J$. These are the cut conditions for a unit flow from pairs to triples through containment edges. The resulting flow gives the required coupling.

Cauchy–Binet expresses the first determinant on the right of (4) as $\mathbb E\prod_{j\in J}(c+y_j)$ and the second as $\mathbb E\prod_{j\in S}(c+y_j)$. If $m$ denotes the sole element of $J\setminus S$, the same coupling therefore gives

$$
\det(\operatorname{diag}(c,c,d)+H)=\mathbb E\left[(d+y_m)\prod_{j\in S}(c+y_j)\right].
$$

Assign the two labels with value $c$ to the two labels in $S$, in either order. Assign the remaining label to $m$. This supplies the matching required in (2). Averaging over the red triples and applying (1) proves the theorem.

## 5. A separate finite reduction for the unrestricted overlap-three test

This section gives a finite reduction for the following test. For arbitrary complex $x_1,\ldots,x_r$ and $y_1,\ldots,y_s$ and arbitrary three-column isometries $E,F$, ask whether $\det(E^*D_xE+F^*D_yF)$ lies in the convex hull of zero and the products for all three-edge matchings. If a strict violation exists, it exists with $r,s\le9$. When both counts are at least six, they can also be taken to satisfy $r+s\le15$. Zero is part of this explicitly stated test, as required for the original problem when both shifted matrices are singular. This reduction does not decide the finite cases.

To prove the reduction, choose a separating real linear functional $z\mapsto\operatorname{Re}(\eta z)$ and perturb the two lists generically, keeping the same strict inequality. This is possible because all quantities and the finitely many comparison products are continuous. Maximize the functional over the compact product of the two Stiefel manifolds. Write $Z=E^*D_xE+F^*D_yF$. The maximum is positive because zero is a comparison point. Thus $Z$ and $T_0=\eta\operatorname{adj}(Z)$ are invertible. Define $R(z)=(zT_0+\bar z T_0^*)/2$.

At a maximizer, the Lagrange multiplier conditions for $E^*E=I$ and $F^*F=I$ give Hermitian matrices $L_A,L_B$ such that $(L_A-R(x_i))e_i=0$ and $(L_B-R(y_j))f_j=0$, where $e_i,f_j$ are the conjugate transposes of the corresponding rows. Indeed, the first variation in $E$ uses $d\det Z=\operatorname{tr}(\operatorname{adj}(Z)dZ)$, so the real differential of the objective equals the differential of $\sum_i e_i^*R(x_i)e_i$ at these frames. The constraint differential is surjective onto the Hermitian matrices, as seen by varying $E$ by $E G/2$ for Hermitian $G$. The same argument applies to $F$.

Every nonzero row therefore contributes a zero of its corresponding real polynomial $P_A(z)=\det(L_A-R(z))$ or $P_B(z)=\det(L_B-R(z))$ in $\operatorname{Re}z,\operatorname{Im}z$. Both cubics have the same homogeneous degree-three part $\det(-R(z))$. Its $z^3$ coefficient in the variables $z,\bar z$ is $-\det(T_0)/8$, which is nonzero. Thus neither cubic vanishes identically.

Ten generic plane points do not lie on a nonzero polynomial of degree at most three. For instance the ten integer points $(i,j)$ with $i,j\ge0$ and $i+j\le3$ determine such a polynomial uniquely. This follows by successively factoring $j,j-1,j-2$ after imposing the vanishing conditions on each horizontal row. Thus each list can have at most nine active labels.

A pair of real cubics with identical cubic part has sixteen real coefficients: four common cubic coefficients and six coefficients of lower degree for each polynomial. If both active counts are at least six and have sum at least sixteen, select sixteen points with at least six of each color. Generically their evaluation equations force the entire pair to vanish. To see this, use the same six nodes $i+j\le2$ of the triangular grid for both colors. Assign the four remaining nodes $i+j=3$ to the colors to match the required counts. The polynomial difference has degree at most two and vanishes at the six shared nodes, so the polynomials agree. Their common cubic vanishes on the full ten-node grid, hence is zero. Thus the determinant of the evaluation matrix is a nonzero polynomial in the point coordinates. Generic choices satisfy this condition simultaneously for every eligible subset of the two finite lists. The nonzero common highest-degree part excludes the stated count pattern. Removing the zero rows preserves the determinant, the isometry constraints, and the strict separation from the smaller list of comparison points. This proves the reduction.

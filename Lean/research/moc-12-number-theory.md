# Marcus-de Oliveira formulations: Number theory and field arithmetic

Atlas entries 136–147.

All eigenvalue lists use the indicated multiplicities. $S_n$ is the set of permutations of $\{1,\ldots,n\}$; $U(n)$ is the complex unitary group; $*$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. The classical conjecture compares the determinant of a sum of two normal operators with the convex hull of products of matched eigenvalue sums. The following statements specify scalar realizations when the native objects are not complex operators. The chosen realizations and all rank conditions are part of the hypotheses.

## 136 Finite separable field extensions

Let $L/K$ be a finite separable field extension of degree $n$, with a fixed embedding of $K$ into $\mathbb C$. The $n$ embeddings $\sigma_j:L\to\mathbb C$ over $K$ identify $L\otimes_K\mathbb C$ with $\mathbb C^n$. For $a,b\in L$ the scalar-extended multiplication operators $A=L_a,B=L_b$ are diagonal in the orthonormal embedding basis. For every unitary $U$ of this complex space,

$$\det(L_a+UL_bU^*)\in\operatorname{conv}\left\{\prod_{j=1}^n(\sigma_j(a)+\sigma_{\pi(j)}(b)):\pi\in S_n\right\}.$$

The determinant of multiplication by a field element is its field norm in the chosen embedding. For $U=I$ the product is the norm of $a+b$. General $U$ need not preserve the field multiplication structure.

## 137 Galois representations

Let $\rho,\eta$ be representations of a Galois group on finite-dimensional spaces of equal dimension $n$ over a field with a specified complex scalar realization. For two group elements $g,h$, suppose $A=\rho(g)$ and $B=\eta(h)$ in that realization are normal for chosen Hermitian products. Let $\lambda_j,\mu_j$ be their eigenvalues. For every unitary identification $U$ of the spaces,

$$\det(\rho(g)+U\eta(h)U^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The individual traces are character values and the determinants are determinant characters. The complex realization and normality are hypotheses; an arbitrary $\ell$-adic representation does not have a canonical Hermitian structure.

## 138 Local fields

Let $K$ be a nonarchimedean local field with real additive valuation $v$, normalized by $v(\varpi)=1$ for a uniformizer. Let $A,B\in GL_n(K)$ and let $s_j=v(\alpha_j)$, $t_j=v(\beta_j)$ be the valuations of their eigenvalues in a fixed algebraic closure with extended valuation. Form positive slope operators $X=\operatorname{diag}(e^{-s_j})$, $Y=\operatorname{diag}(e^{-t_j})$ on $\mathbb C^n$. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{-s_j}+e^{-t_{\pi(j)}})\le \log\det(X+UYU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{-s_j}+e^{-t_{\pi(j)}}).$$

The individual log-determinants are $-v(\det A)$ and $-v(\det B)$. This comparison is in the real slope realization, not a convex hull in $K$. Valuation of a sum can exceed the smaller valuation through cancellation, so the slope operators do not give the valuation of the original matrix sum.

## 139 Newton polygons

Let $P,Q$ be Newton polygons of monic degree-$n$ polynomials over a valued field with nonzero constant terms. List their real slopes $s_j,t_j$ in nondecreasing order, with each slope repeated by its horizontal length; use the convention in which slopes equal valuations of roots (reverse the usual geometric polygon as necessary). Let $X=\operatorname{diag}(e^{s_j})$ and $Y=\operatorname{diag}(e^{t_j})$. For each unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(X+UYU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

Each original polygon has terminal height equal to the sum of its listed slopes. The comparison bounds the terminal log-determinant of a sum of positive slope operators, not the Newton polygon of an unspecified polynomial addition.

## 140 Crystalline cohomology

Let two isocrystals obtained from a specified crystalline cohomology degree have the same rank $n>0$. Let $s_j,t_j$ be their intrinsic Frobenius slopes, repeated by isoclinic rank. With a fixed normalization of the Frobenius valuation, use positive slope operators $A=\operatorname{diag}(e^{s_j})$ and $B=\operatorname{diag}(e^{t_j})$ on a complex Hilbert space of dimension $n$. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The log-determinants of the inputs are their determinant-isocrystal slopes. This avoids taking ordinary eigenvalues of a semilinear Frobenius; a linear Frobenius iterate would require a separate choice.

## 141 Filtered phi-modules

Let $D,E$ be filtered Frobenius modules of equal rank $n>0$. For each choose either the Newton slope list or the Hodge weight list, using the same convention and choice for both modules; write the lists $s_j,t_j$. For each list form the positive operator with eigenvalues $e^{s_j},e^{t_j}$ on identified complex Hilbert spaces. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(\operatorname{diag}(e^{s_j})+U\operatorname{diag}(e^{t_j})U^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The sum of the selected slopes is $t_N$ in the Newton case or $t_H$ in the Hodge case. This is a separate comparison for each polygon. Weak admissibility requires the corresponding inequalities on subobjects and is not implied by this determinant statement.

## 142 Etale cohomology over finite fields

Let $X,Y$ be varieties over a finite field with $n>0$ dimensional $\ell$-adic cohomology groups in a fixed degree $k$ ($\ell$ different from the field characteristic). Choose geometric or arithmetic Frobenius consistently, and a complex scalar realization of the eigenvalues. Require the Frobenius operators to admit normal representatives $F_X,F_Y$ on complex Hilbert spaces of dimension $n$, with eigenvalues $\lambda_j,\mu_j$. For every unitary identification $U$,

$$\det(F_X+UF_YU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

A semisimple realized Frobenius admits such a choice of inner product; for a nonsemisimple operator diagonal root representatives replace the original action. The scalar extension, not the $\ell$-adic vector space itself, supplies the real convex hull.

## 143 Weil zeta functions

Let $X,Y$ be smooth proper varieties over a finite field and choose one cohomological degree $k$ in which the Frobenius factors have the same degree $n>0$. In a chosen complex realization let $F,G$ be normal Frobenius representatives with eigenvalues $\lambda_j,\mu_j$. For every $t\in\mathbb C$ and unitary $U$,

$$\det(I-t(F+UGU^*))\in\operatorname{conv}\left\{\prod_{j=1}^n(1-t(\lambda_j+\mu_{\pi(j)})): \pi\in S_n\right\}.$$

The Weil zeta function is an alternating product of degreewise characteristic factors $\det(I-tF_k)^{(-1)^{k+1}}$. For the total product one must combine the degreewise hulls by multiplication or reciprocation according to the exponent, excluding zero denominators. The statement is pointwise in $t$.

## 144 Motivic theory

Let $M,N$ be two motives with a specified complex linear realization of a fixed cohomological degree and equal positive dimension $n$. Choose motivic endomorphisms whose realized actions $A,B$ are normal for specified Hermitian products, and let $\lambda_j,\mu_j$ be their eigenvalues. For every unitary identification $U$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The realized determinant is the scalar action on the highest exterior power in that degree. A motivic Euler characteristic or categorical dimension may be signed and is not the spectral length in the formula.

## 145 Local L-factors

Let $F,G$ be the Frobenius operators on inertia-invariant spaces in two local Galois or Weil-Deligne representations at a place of residue cardinality $q$. Fix complex normal realizations of the same positive dimension $n$, with eigenvalues $\lambda_j,\mu_j$. For every $s\in\mathbb C$ and unitary $U$,

$$\det(I-q^{-s}(F+UGU^*))\in\operatorname{conv}\left\{\prod_{j=1}^n(1-q^{-s}(\lambda_j+\mu_{\pi(j)})):\pi\in S_n\right\}.$$

The left side is the reciprocal Euler factor of the combined realized operator. If the determinant is nonzero, its inverse belongs to the reciprocal of the hull with zero removed. Inversion does not generally preserve complex convex hulls.

## 146 Mahler measure

Let $f,g$ be Laurent polynomials on the torus $\mathbb T^r$, equipped with normalized Haar measure $\nu$, and suppose both are real and strictly positive there. Let $\mu_f=f_*\nu$, $\mu_g=g_*\nu$. For the probability couplings $\Gamma$ of these two laws and the Mahler measure $M(h)=\exp\int_{\mathbb T^r}\log|h|\,d\nu$,

$$M(f+g)\in\left[\inf_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma,\ \sup_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma\right].$$

The common torus defines one such coupling. For finite equal-mass samples the geometric-mean bounds are the normalized permutation-product bounds. General complex Mahler measures lose phase and need separate treatment near zeros.

## 147 Discriminants

Let $L/K$ be a finite separable extension of degree $n$ with a fixed complex embedding of $K$. Choose a $K$-basis $b_1,\ldots,b_n$ of $L$. For $a,c\in L$ let $A_{ij}=\operatorname{Tr}_{L/K}(ab_i b_j)$, $B_{ij}=\operatorname{Tr}_{L/K}(cb_i b_j)$ in that embedding. Require the complex matrices $A,B$ normal in the orthonormal coordinate basis. For their eigenvalues $\lambda_j,\mu_j$ and every unitary $U$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

At $U=I$ the determinant is the discriminant of the weighted trace pairing for $a+c$. For real symmetric pairings use real orthogonal $U$ so the conjugated pairing remains symmetric. A basis change by congruence need not preserve these eigenvalues.

# A neighborhood uniform in one unrestricted eigenvalue

Use the sum convention. Fix a simple nonconcyclic list $b=(b_1,\ldots,b_4)$, a value $t$ outside $\{-b_j\}$, and $r\ne t$. Let $W$ be the relative unitary. Write $u,v$ for its third and fourth rows. Assume every entry of these rows is nonzero and every two-column minor of the two rows is nonzero. These are open dense conditions on $W$.

**Theorem.** There is an open neighborhood of $((t,t,r),b,W)$ in $\mathbb C^3\times\mathbb C^4\times U(4)$ such that for every $(a',b',W')$ in the neighborhood, MOC holds with first spectrum $(a'_1,a'_2,a'_3,z)$ for **all** $z\in\mathbb C$. Each such triple admits a single convex witness that works for every $z$. In particular this controls arbitrarily large values of the fourth eigenvalue while allowing the other three to split and both spectra to be nonconcyclic.

## A joint interior point

For fixed other data, both the determinant and the vertices are affine polynomials in $z$. Encode each by its value at $z=t$ and its slope, a vector in $\mathbb C^2$ regarded as a real space. If the determinant's vector lies in the real convex hull of the 24 vertex vectors, the same law evaluates to the desired inclusion for every $z$. Conversely, validity for every $z$ implies this joint hull condition by real separation. Every functional $\Re(\alpha P(t)+\beta P')$ with $\alpha\ne0$ evaluates $\Re(\alpha P(t+\beta/\alpha))$, and the functionals with $\alpha=0$ follow by limits. [Previous affine hull reduction](../research/moc_joint_affine_hull_lean_status_20261031.txt)

Put $Q=\prod_j(t+b_j)$, $\gamma_j=1/(t+b_j)$ and $\delta=r-t$. At the base, the vertex assigning $j$ to row three and $k$ to row four is the polynomial
$$
 Q(1+\delta\gamma_j)(1+(z-t)\gamma_k),\qquad j\ne k.
$$
Its coefficient vector after division by $Q$ is $(s_j,s_j\gamma_k)$, where $s_j=1+\delta\gamma_j$.

Write $q_{jk}=|u_jv_k-u_kv_j|^2$ for $j<k$. We first construct strictly positive numbers $w_{jk}$ on all ordered pairs of distinct labels such that
$$
 w_{jk}+w_{kj}=q_{jk},\qquad \sum_{k\ne j}w_{jk}=|u_j|^2,\qquad
 \sum_{j\ne k}w_{jk}=|v_k|^2 .
$$
Assign each unoriented edge of mass $q_{jk}$ to either endpoint by fractional shares. The supply-demand cuts for assigning masses $d_j=|u_j|^2$ to the vertices are $\sum_{j\in S}d_j\ge\sum_{\{j,k\}\subset S}q_{jk}$ for every $S$, with equal totals. These are sufficient by the finite max-flow theorem on the incidence network, joining each edge node to its two endpoints. By Cauchy–Binet the difference on a proper nonempty set is
$$
 \|u_S\|^2(1-\|v_S\|^2)+|\langle u_S,v_S\rangle|^2>0 .
$$
All edge masses are positive. Preassign the same sufficiently small positive amount to *each* orientation of *each* edge. The remaining capacities and strict proper cuts stay nonnegative by finiteness, and total supply still equals demand. An ordinary feasible assignment completes the weights. The total incident mass at $j$ is $|u_j|^2+|v_j|^2$ by orthonormality, so the incoming sums also have the required values.

The determinant at the base agrees as a polynomial with the $w_{jk}$-average of the displayed products. In fact, dividing the determinant by $Q$ and applying the determinant lemma to the two diagonal updates gives
$$
 1+\delta\sum_j|u_j|^2\gamma_j+(z-t)\sum_k|v_k|^2\gamma_k
       +\delta(z-t)\sum_{j<k} q_{jk}\gamma_j\gamma_k .
$$
This computation uses Cauchy–Binet for the $2\times2$ compression of the inverse of $tI+WD_bW^*$. [Oriented-pair law](../theorems/finite_and_spin_geometry/dual_local_to_open_theorem.md)

It remains to prove **full** real affine dimension four. The $\gamma_j$ are nonconcyclic because the reciprocal chart is pole-free. Hence they are noncollinear. At least two of the four triples obtained by omitting one $\gamma_j$ are noncollinear: any two distinct collinear triples would share two distinct points and therefore coincide in line, forcing all four collinear. At most one $s_j$ vanishes. Choose $j$ with $s_j\ne0$ whose other three $\gamma_k$ are noncollinear. Differences between the three coefficient vectors for this $j$ span the entire second complex coordinate in the real direction space. The projections of all vectors to the first coordinate are the four noncollinear $s_j$. This proves the dimension assertion. The strictly positive $w_{jk}$ put the determinant coefficient vector in the interior. It stays interior for sufficiently small perturbations of all the coefficients and vertices, by its positive minimum support slack on the real unit sphere of functionals. These coefficient vectors depend continuously on $(a',b',W')$. The same neighborhood works for every $z$ because $z$ has been eliminated before taking the neighborhood. This proves the theorem. By compactness a uniform neighborhood in the spectral variables can be taken for $W$ in any compact subset of the stated open set.

## Why a common law for all four free eigenvalues would overshoot

A tempting next step is to find one law that works for all first spectra $a$ after fixing simple nonconcyclic $b$ and $W$. In fact this would force a common law for *all minors*, even though only one $b$ is being tested.

Suppose $\lambda$ recovers the determinant polynomial for every $a$. First take $a_i=z$ on one row and $t$ on the other three. Compare the linear coefficient in $z$ at $t=-b_j$. On the vertex side only permutations matching row $i$ to $j$ survive, with multiplier $\prod_{k\ne j}(b_k-b_j)\ne0$. On the matrix side the same coefficient is the principal cofactor of $W(D_b-b_jI)W^*$, equal to $|W_{ij}|^2$ times that multiplier. Thus the law recovers every singleton marginal.

For a two-row set $I$, put $m_{jk}$ equal to its unordered pair marginal under $\lambda$ minus $|\det W[I,\{j,k\}]|^2$. The singleton identities and the degree identities for a pair of orthonormal rows give $\sum_{k\ne j}m_{jk}=0$ for all $j$. Therefore
$$
 m_{12}=m_{34}=u,\quad m_{13}=m_{24}=v,\quad
 m_{14}=m_{23}=-u-v
$$
for real $u,v$. Compare the coefficient of $\prod_{i\notin I}a_i$ in the determinant polynomial. It is the corresponding principal $2\times2$ minor of $WD_bW^*$, so Cauchy–Binet gives $\sum_{j<k}m_{jk} b_j b_k=0$. Substituting the preceding expressions gives
$$
 u(b_1-b_3)(b_2-b_4)+v(b_1-b_2)(b_3-b_4)=0.
$$
The two complex coefficients are independent over $\mathbb R$ because their ratio is a nonreal anharmonic cross-ratio. Thus $u=v=0$ for each $I$. Complementarity recovers the three-row marginals too. Conversely a common law on all minors recovers every determinant by expansion.

There are rational orthogonal $W$ for which the required minor law does not exist. The cited family gives such $W$ arbitrarily close to identity. Hence one cannot obtain a global bound by keeping a single common witness while freeing all four first eigenvalues, even for a **single** fixed simple nonconcyclic $b$. The one-variable result avoids this obstruction by letting the witness respond to the other three eigenvalues. Its remaining limitation is loss of a positive coefficient-hull interior margin away from the repeated base or at singular row configurations. Resolving whether the determinant coefficient vector ever exits the four-dimensional hull, with the witness allowed to change, would settle MOC4. [Exact minor-law obstruction](../theorems/profile_geometry/algebra_local_marginal_obstruction.md)

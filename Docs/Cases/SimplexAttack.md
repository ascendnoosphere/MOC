# A global reduction for the 48 mixed facets

For every order-four unitary, **at most one** of the 48 mixed permutation-profile facet inequalities can fail. The profiles violating a specified facet lie in the convex hull of its thirteen permutation profiles and one explicit additional point. That point satisfies all squared-minor nonnegativity constraints but violates a scalar MOC support inequality. Thus replacing the unitary profiles by this entire simplex would make the proposed theorem false.

Write $P_\pi(I,J)=\mathbf1_{\pi(I)=J}$ for the coordinates of a permutation profile, using degrees zero through two. The 82 permutation-hull facets consist of nonnegative individual coordinates and one orbit of 48 mixed facets. We use the same ordered profile columns as in the [spin certificate](../spin/PROOF.md) and [symplectic calculation](Symplectic.md). Denote the matrix of these columns by $L$. With one-based indices the first thirteen permutations are
$$
1324,\ 1342,\ 1423,\ 1432,\ 2143,\ 2314,\ 2341,\ 2413,\ 3124,\ 3142,\ 3214,\ 3412,\ 4123 .
$$
The last permutation, $4231$, is the anchor. The mixed facet is $p=2w_{14}=0$ in the coordinates $y=Lw$. Every unitary profile has such coordinates by the real part of the complementary-minor determinant expansion. They sum to one.

Let $E=\{1,4,7,8,10,11,13\}$. Each coordinate $v_i=w_i+\mathbf1_{i\in E}w_{14}$ for $1\le i\le13$ is an individual squared minor. In order, row and column sets for these coordinates are
$$
(14,14),\ (13,14),\ (14,13),\ (3,3),\ (12,12),\ (14,24),\
(4,1),\ (12,24),\ (13,23),\ (13,34),\ (2,2),\ (12,34),\ (1,4).
$$
These are identities between rows in the permutation basis, so they hold throughout the column span. Define
$$
 Z=\frac16\left(\sum_{i\in E}L_i-L_{14}\right).
$$
Then for any unitary profile violating this facet,
$$
 y=\sum_{i=1}^{13}v_i L_i +6(-w_{14})Z.
$$
All displayed coefficients are nonnegative and sum to one. This calculation applies to complex unitary and real orthogonal mixers alike. The 48 mixed facet functionals take the values $-1/3,1/3,2/3,1$ at $Z$ with multiplicities $1,24,20,3$. Evaluate the facet under the 576 pairs of row and column permutations and identify equal functionals by their values on the 24 permutation columns. Since each is nonnegative at every $L_i$, the only one which can be negative at $y$ is the originally chosen facet. Together with the complete facet list, this proves the claim for all profiles. [Facet completeness](../MOC4_Hermitian_Proof.md) · [Exact enumeration](../../Code/verify_mixed_facet_apex.py)

The apex itself is too large a relaxation. For the sum convention take
$$
 a=(20,0,1,3-5i),\qquad b=(-1-i,-2,1+i,i).
$$
Set $h_\pi=\Re\{(1+i)\prod_j(a_j+b_{\pi(j)})\}$. The maximum over all permutations is $164$. Linear extension of this support to $Z$ gives $(\sum_{i\in E}h_{\pi_i}-h_{4231})/6=168$. Moreover $Z$ cannot be an actual unitary profile. After relabeling columns to make the anchor the identity, its singleton entries have zero diagonal and every off-diagonal entry equals $1/3$. Every principal two-by-two determinant squared of a realizing matrix would therefore equal $1/9$. Entries of $Z$ are integer multiples of $1/6$. This contradiction also explains why its scalar failure supplies no normal-pair counterexample.

For any direction and spectra the exact remaining bound on this cap is
$$
 6(-w_{14})\,[h(Z)-H]\ \le\
 \sum_{i=1}^{13}v_i[H-h_{\pi_i}],\qquad H=\max_\pi h_\pi .
$$
Only supports with $h(Z)>H$ require control beyond minor nonnegativity. The seven indices in $E$ automatically satisfy $w_i\ge-w_{14}$, hence their minimal positive simplex radii $-2w_{14}/w_i$ are at most two. For the other six indices $w_i$ is a squared minor and can approach zero. The new cap identity and the apex example establish neither a global choice of Bernstein radii nor a bound for all realizable $v_i$ in the last display. The two open sets with verified radii are documented separately. [Verified certificates](Symplectic.md)

Replay the finite identities and the integer-spectrum obstruction with `python3 -B Code/verify_mixed_facet_apex.py` from the repository root.

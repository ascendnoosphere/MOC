# Spin gauge and the compact symplectic group in order four

Write $d(W)=\det(D_a+W D_bW^*)$ and $z_\pi=\prod_i(a_i+b_{\pi(i)})$.
Here $K=\operatorname{Sym}^3(SU(2))$ in the normalized monomial basis.
The subgroup $Sp(2)$ preserves the alternating form on binary cubics. We use paired coordinates for this form when giving explicit matrices. They differ from the weight basis by a fixed signed permutation.

## Which eigenbasis changes preserve the problem? (P, Q, BC, BG, BR)

Let $T$ be the diagonal unitary group and $N=T\rtimes S_4$ the monomial group. If $W=E^*F$ for ordered orthonormal eigenbases of $A,B$, replacing the bases by $EL,FR$ replaces $W$ by $L^*WR$. For $L,R\in N$, relabel the diagonal lists by $L^*D_a L,R^*D_b R$. The new sum is unitarily conjugate to the old sum by $L$, and the 24 vertices are permuted. This proves invariance of the determinant and hull, including all diagonal phases and permutations.

Consequently a specified eigenbasis pair admits a spin representative by rephasing and reordering exactly when
$$
 NWN\cap K\ne\varnothing\quad\Longleftrightarrow\quad W\in NKN .
$$
Indeed, undo the left and right factors of a point in the intersection. If $D_4$ denotes diagonals alone the corresponding equivalence holds for rephasing alone. The reversal and all other column and row permutations must be included when the lists can be reordered. For example, outside the diagonal/antidiagonal endpoints, a cubic rotation has a corner row with four nonzero entries. At the endpoints its permutation is either identity or reversal. An elementary transposition is spin after reordering but does not belong to $TKT$.

There is a finite membership test for Q. For each pair of orderings let $X$ be the reordered mixer. Set $c=|X_{11}|^{1/3}$ and $s=\sqrt{1-c^2}$. Form $V=\operatorname{Sym}^3\left(\begin{smallmatrix}c&s\\-s&c\end{smallmatrix}\right)$ in the normalized monomial basis. These parameters exhaust the possibilities because left and right diagonal special unitaries reduce every $SU(2)$ matrix to a rotation in this quadrant, and its $(1,1)$ cubic entry is $c^3$. Compare the entrywise moduli of $X,V$. If they agree, record $q_{ij}=X_{ij}/V_{ij}$ on each nonzero edge of the bipartite graph of row and column indices. Seek unit phases $l_i,r_j$ with $q_{ij}=l_ir_j$. Choose one phase in each connected component and propagate the equations along a spanning tree. The remaining edges either agree or disprove feasibility, since the only freedom left in that component is a common row phase and its inverse on the columns. Thus any successful ordering produces the two gauge factors, and failure for all orderings excludes $NKN$. The test includes sparse matrices and the two monomial endpoints.

For repeated eigenvalues, rephasing and reordering need not reach every eigenbasis. For fixed orderings the complete test for the *normal pair* to admit some spin eigenbasis is intersection of $K$ with $G_a W G_b$, where $G_a,G_b$ are the unitary centralizers of the respective diagonal lists. Allow separate reorderings as well for unordered lists. For example $A=aI$ allows an eigenbasis with $W=I$ for every $B$, even if a prescribed eigenbasis produces the non-spin matrix below.

For a given $W\in Sp(2)\setminus K$, membership in $NKN$ settles precisely whether it belongs to a spin eigenbasis orbit under the specified gauge. Its complement gives the genuinely additional symplectic mixers in Q. An explicit case in this complement is proved below. A symplectic conjugation of the mixer *alone* need not preserve the determinant at fixed spectra. For instance take $W=\mathrm{diag}(i,-i,i,-i)$ and conjugate in its first quaternionic line by the real $SU(2)$ rotation through $\pi/4$. The new first two coordinates interchange the entries of $D_b$ under conjugation by the new mixer. For $a=b=(1,2,3,4)$ the determinants are $384$ and $432$. Simultaneous unitary conjugation of the actual pair always preserves its sum determinant.

## A certified open set beyond the spin gauge (H, L, T, AD, AL, AM, BY)

The following set of symplectic examples works for **all complex spectra**. It contains a mixer squaring to $-I$, regular symplectic mixers, and mixers with pairwise distinct eigenvalues arbitrarily close to that center. The scalar certificate also holds on an open neighborhood in $U(4)$.

Write $J=\mathrm{diag}(J_2,J_2)$, $J_2=\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$. In these coordinates $W\in Sp(2)$ means $W$ is unitary and $WJ=J\bar W$. Take
$$
 a_0=\frac1{101}\begin{pmatrix}99i&20\\-20&-99i\end{pmatrix},\quad
 v=\frac15\begin{pmatrix}3&4\\-4&3\end{pmatrix},\quad
 W_0=\begin{pmatrix}
 (3/5)a_0&(4/5)v\\
 -(4/5)v^*&-(3/5)v^*a_0v
 \end{pmatrix}.
$$
All four blocks commute with the quaternionic structure $J_2\circ\mathrm{conjugation}$. Since $a_0^*=-a_0$, $a_0^2=-I$ and $v^*v=I$, multiplication gives $W_0^*=-W_0$ and $W_0^2=-I$. The product
$W_{11}W_{24}\overline{W_{14}W_{21}}$ is nonzero and purely imaginary at $W_0$. Every cubic spin matrix can be rephased to be real, since a two-by-two special unitary is a real rotation between two diagonal special unitaries, and their cubic symmetric powers remain diagonal. Reality of *all* such four-entry products is invariant under row and column phases and permutations. Hence $W_0\notin NKN$, and this same nonreal product excludes $NKN$ in a neighborhood.

Here is an exact certificate transferring the scalar argument of the [cubic spin proof](../spin/PROOF.md) to $W_0$. Put $X=W[(3,1,2,4),(4,2,1,3)]$, using one-based indices, and let $y(X)$ consist of the 53 squared minor moduli in degrees $0,1,2$. Write $P_\pi(I,J)=\mathbf1_{\pi(I)=J}$, and let $L$ have columns $P_\pi$ in the order
$$
 1324,1342,1423,1432,2143,2314,2341,2413,3124,3142,3214,3412,4123,4231.
$$
For every $X\in U(4)$, $Lw=y(X)$ has unique real coordinates. In fact all 24 permutation columns together have rank 14, and these 14 columns are independent, as verified by exact row reduction. Grouping the determinant expansion by $\pi(I)=J$ gives
$$
 \sum_{\pi(I)=J}\frac{\mathrm{sgn}(\pi)\prod_j X_{j,\pi(j)}}{\det X}
    =|\det X[I,J]|^2
$$
by the complementary-minor formula. Taking real parts places the profile in this column space. The degree-zero row gives $\sum_i w_i=1$.

For $p=2w_{14}$ and
$R=(1,3,3,2,1,3,1,1/2,3,1/2,2,4,1)$, exact elimination at $W_0$ gives
$$
 p=-\frac{2903967}{159390625},\qquad
 \min_{1\le i\le13}(R_iw_i+p)=\frac{1148103}{63756250}>0.
$$
The functional $p$ on the 24 permutation columns takes value zero 13 times, one ten times, and two once. Thus a positive law reproducing all these minor moduli is impossible. For the scalar determinant the signed coordinates are sufficient here. The inequalities $p<0$, $R_iw_i+p\ge0$ are precisely the sufficient conditions proved by the first Bernstein simplex in the cubic spin proof. Briefly, a strict separating cost with anchor cost normalized to two would lie in that simplex with positive barycentric coefficient on its anchor. The cost polynomial vanishes on all genuine separating costs and is positive at every such simplex point. This contradiction proves MOC. The two displayed strict inequalities persist by continuity of the minor moduli and their fixed linear coordinates. The exact arithmetic can be replayed with `python3 -B Code/verify_symplectic_case.py` from the repository root. [Certificate verifier](../../Code/verify_symplectic_case.py)

For the regular examples, diagonalize $W_0$ in a quaternionic orthonormal eigenbasis, pairing eigenvalues $i,-i$ by the antiunitary. Replace its two angles $\pi/2,\pi/2$ by distinct angles close to $\pi/2$ and conjugate back by that same symplectic basis. All four eigenvalues can be made distinct while keeping the strict certificate. This proves a portion of each spectral stratum H and L, the regular case T, and examples on both sides of $W^2=-I$.

### An additional open set requiring different Bernstein radii

The same block construction yields an example outside *every relabeling* of both simplex tests supplied with the cubic spin proof. Set $c=-9/41$, $s=40/41$,
$$
 A=\frac1{17}\begin{pmatrix}-9i&12+8i\\-12+8i&9i\end{pmatrix},\qquad
 V=\frac1{79}\begin{pmatrix}-29+50i&50+20i\\-50+20i&-29-50i\end{pmatrix},\qquad
 W_1=\begin{pmatrix}cA&sV\\-sV^*&-cV^*AV\end{pmatrix}.
$$
Again $W_1$ is symplectic, $W_1^2=-I$, and its nonreal four-entry product excludes the spin gauge. Use rows $(1,3,4,2)$ and columns $(2,4,3,1)$ in the certificate above. With $d=31808386132789249$ and
$$
 R'=(121,262,262,31,4,262,42,3,262,3,31,3,42)/100
$$
the exact values are $p=-224829494664111/d$ and $\min_i(R_i'w_i+p)=437635081521/d>0$. The old $R$ and the second radii list from the cubic checker both fail. Of the $24^2$ row and column reorderings, twelve give a negative anchor facet. The best minimum margin over those twelve is $-77120738391213/(2d)$ for the first old list and $-203334539535711/d$ for the second. A nonnegative common law is ruled out by the negative facet itself.

To apply the spin proof with $R'$, its cost polynomial needs a new Bernstein sign check on this simplex. In the established normalization and integer scaling, the smallest of its 497,420 coefficients is
$$
4954866182527184873153196953201366217523200 .
$$
The exact computation uses the same matching tensor, signed square-root interpolation and degree-nine basis change as the cubic proof, with the 13 new numerators and denominator 100 in the final basis change. All coefficients are strictly positive, so a separating cost is impossible. The [symplectic verifier](../../Code/verify_symplectic_case.py) recomputes the full grid, tests both old simplices in every ordering and checks the new signs with integer arithmetic.

Continuity gives an open scalar-MOC neighborhood of $W_1$ for all spectra. It can be chosen disjoint from the regions given by the two old tests. For reorderings with $p<0$, each old test has a strictly negative margin at $W_1$. Reorderings with $p>0$ keep that sign on a neighborhood. At $p=0$ a nonnegative minimum margin would make all coordinates nonnegative, contradicting the already detected negative permutation facet. There are only finitely many reorderings. Thus both the new inclusion and the failure of the two old tests persist on a common neighborhood.

## What a convexity proof for the full symplectic group must bound

The invariant quaternionic structure in AD is the defining property of $Sp(2)$ in its fixed embedding. It yields the following exact low-dimensional support test. It applies to arbitrary complex spectral lists and reduces the last two sphere variables to one matrix inequality.

If AD permits *some* invariant quaternionic structure after an eigenbasis gauge, it places no restriction in order four. Multiply any mixer by a scalar to put it in $SU(4)$. Left-multiply along the path $\mathrm{diag}(e^{it},e^{it},e^{-it},e^{-it})$ from $I$ to $-I$. The imaginary part of the trace changes sign, so at some point the mixer $V$ has real trace. For $V\in SU(4)$, the coefficients of its characteristic polynomial satisfy $e_2=\bar e_2$ and $e_3=\bar e_1$, by complementary eigenvalue products. Its characteristic polynomial is therefore real. The nonreal eigenvalues occur in conjugate pairs, the multiplicity of $-1$ is even by determinant one, and that of $+1$ is then even by dimension. In an orthonormal eigenbasis pair each vector $u$ with a vector $v$ of conjugate eigenvalue, pairing vectors within the real eigenspaces. The antiunitary sending $u\mapsto v$, $v\mapsto-u$ commutes with $V$ and squares to $-I$. The diagonal left multiplier merely conjugates the original sum by a diagonal unitary. Thus an MOC proof for this variable-structure interpretation would imply unrestricted MOC4.

Every $W\in Sp(2)$ has the form
$$
 W=\mathrm{diag}(L_1,L_2)\!
 \begin{pmatrix}cI&sI\\-sI&cI\end{pmatrix}
 \mathrm{diag}(R_1,R_2),\qquad L_i,R_i\in SU(2),\quad
 c,s\ge0,\ c^2+s^2=1 .
$$
Indeed each quaternionic block is a nonnegative scalar times a special unitary, and the block norms have the displayed pattern by unitarity. For $cs>0$, assign three of the four unit-quaternion factors by choosing $L_1=I$, then $R_1,R_2,L_2$. Orthogonality forces the fourth block. The endpoint block diagonal and antidiagonal matrices have the same factorization.

After conjugation of the full sum by the left factor, each of its two $a$-blocks and two $b$-blocks is of the form $mI+\delta (n\cdot\sigma)$, with $m,\delta$ the paired mean and half-difference, $n\in S^2$ real and $\sigma$ the Pauli matrices. All four axes are independently selectable. The middle rotation commutes with simultaneous $SU(2)$ conjugation, inducing all common spatial rotations of the four axes. We may therefore fix the two $a$-axes to be $e_3,\sqrt{1-x^2}e_1+xe_3$, $-1\le x\le1$.

Fix $x,c$ and a support direction $\eta$. With remaining unit axes $b,d$, the real support functional has the form
$$
 F=\Re(\eta d(W))=f+u^Tb+v^Td+b^TMd
$$
for real $f,u,v,M$. To see separate affinity, the contribution of each selected block $B$ is an update $Y B Y^*$ with fixed two-column $Y$. By multilinearity of the determinant, terms quadratic in $B$ are all constant multiples of $\det B$. This determinant is the fixed product of its two spectral values. The linear and constant terms thus suffice on the unit sphere. This proof also gives a way to compute the coefficients by determinants at signed coordinate axes.

Put $h=\max_\pi\Re(\eta z_\pi)$ and $k=h-f$. Maximizing over $b$ first shows that $F\le h$ for every $b,d$ exactly when $k\ge\|v\|$ and there is a real $\lambda$ such that
$$
 \begin{pmatrix}
 vv^T-M^TM+\lambda I_3&-kv-M^Tu\\
 (-kv-M^Tu)^T&k^2-\|u\|^2-\lambda
 \end{pmatrix}\succeq0.
$$
Indeed the remaining inequality is $k-v^Td\ge\|u+Md\|$ on $S^2$. The first condition guarantees the left side is nonnegative. The second tests the squared inequality on that sphere. For the latter equivalence minimize the quadratic form of the displayed matrix with $\lambda=0$ over $Z\succeq0$ with top-block trace and bottom entry both equal to one, pairing by trace. Every extreme point has rank one. A face supported in rank $r\ge2$ admits $r(r+1)/2>2$ symmetric perturbation directions, so one preserves both constraints and allows a two-sided perturbation. The rank-one matrices are exactly $(d,1)(d,1)^T$. The primal has a strictly feasible diagonal point. Semidefinite duality then gives the stated multiplier if its minimum is nonnegative (absorb any nonnegative dual lower bound into the bottom diagonal entry).

A proof for all $H,L,T,AD,AL,AM$ would in particular need to handle unrestricted symplectic parameters for their respective spectra or provide a different bound. The preceding calculation gives the equivalent test for all symplectic mixers at fixed spectra when imposed for every $x,c,\eta$. The strict example shows why convexity of the full minor profile on permutation columns cannot give that bound.

## Conjugacy, limits and equality (E, BL, BO, BY)

* **E.** Given an arbitrary $W\in U(4)$, choose a unit scalar $s$ with $s^4\det W\ne1$. The entire $U(4)$-conjugacy class of $sW$ misses $K\subset SU(4)$ by determinant, yet $d(sW)=d(W)$. Consequently proving E for every qualifying conjugacy class is equivalent to unrestricted order-four MOC. The argument works in order $n$ with any excluded subgroup of $SU(n)$, including the $n$-dimensional irreducible symmetric power. Individual qualifying classes can be easier. For instance, central mixers are scalar and give a single vertex. Classes with an eigenvalue of multiplicity $n-1$ consist, up to a scalar, of rank-one unitary updates. The [Householder result](../theorems/finite_and_spin_geometry/continuous_householder_meta_proof.md) applies.
* **BL.** The compact subgroup $K$ is closed of dimension three in the connected ten-dimensional $Sp(2)$. Thus $Sp(2)\setminus K$ is dense, while $K$ has only itself as its closure. At fixed spectra, membership in the vertex hull passes to a mixer limit because the determinant is continuous and the hull is compact. The known proof on $K$ alone cannot reach the complement by taking such limits. Regular symplectic mixers are also dense, by perturbing the two eigenangles in a quaternionic eigenbasis.
* **BO.** For specified diagonal lists and $W\in K$, the normal pair $A=D_a,B=WD_bW^*$ realizes the determinant by construction. An explicit supporting equality is $W=I$, $a=b=(1,2,3,4)$, with support direction $-1$. The inequality $i+\pi(i)\ge2\sqrt{i\pi(i)}$ gives $z_\pi\ge384=z_{\mathrm{id}}$. For any exposed vertex and any spectra, a permutation basis realizes that vertex and belongs to the monomial gauge orbit of the identity. Membership of a prescribed permutation matrix in raw $K$ is a different condition.
* **BY.** In any symplectic eigenspace decomposition, nonreal eigenvalues occur in conjugate pairs and real eigenspaces have even complex dimension. Indeed $v\mapsto J\bar v$ is antiunitary, squares to $-I$, and commutes with $W$. These constraints describe multiplicities and supply the paired basis used above. They do not change the 24 determinant vertices. For instance $W^2=-I$ forces the two paired angles to be $\pi/2$ in a symplectic diagonalization. Its entire class is reached by symplectic conjugation of the diagonal model, under which $d(W)$ at fixed spectra generally varies.

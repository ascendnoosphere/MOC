# Open complex unitary neighborhoods with a common minor law

In every positive order, the Marcus–de Oliveira inclusion holds **for
all spectra at once** on a nonempty relatively open subset of the
complex unitary group. On this subset one probability law on permutations
simultaneously realizes all squared minors; the determinant lies in the
relative interior of its matching hull. The subset includes a complex
unitary neighborhood of every real orthogonal mixer whose alternating
graph chart is strictly totally positive, in particular every
distinct-node real Cauchy orthogonal mixer after suitable relabeling and
entry phases. The nearby mixers need not be real or have Cauchy form.

The combinatorial input is T. Lam, *Dimers, webs, and positroids*,
[J. London Math. Soc. 92 (2015), 633–656, DOI 10.1112/jlms/jdv039](https://doi.org/10.1112/jlms/jdv039),
[open preprint DOI 10.48550/arXiv.1404.3317](https://doi.org/10.48550/arXiv.1404.3317):
Theorems 2.4(2), 3.1, Proposition 3.4, and Corollary 3.5. The real
Cauchy application occurs in Zheng, Appendix C.5
([preprint DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923)).
The proof below uses the complementary identity as a polynomial
identity at complex points, not positivity in the complex Grassmannian.

## Chart and uniform complementary sign

For $U\in U(n)$, use the $n\times2n$ chart
$$
A(U)=[e_1,u_1,e_2,u_2,\ldots,e_n,u_n],
$$
where $e_i$ are coordinate columns and $u_j$ are the columns of $U$.
Label columns by $0,\ldots,2n-1$ in this order. Let $S_0$ be the
coordinate labels, and let $\Delta_S$ be the minor on columns $S$
in increasing order, for $|S|=n$. Write
$D=\operatorname{diag}(1,-1,1,-1,\ldots)$.
Since $ADA^*=I-UU^*=0$, the row space of $AD$ is the Hermitian
orthogonal complement of the row space of $A$. The exterior
complement identity gives, up to one nonzero scalar independent of $S$,
$$
\Delta_S(AD)=
\lambda(-1)^{\sum_{s\in S}s-\binom n2}\overline{\Delta_{S^c}(A)}.
$$
Indeed, the conjugate Hodge star applied to the wedge of an orthonormal
row basis has coordinate $S$ equal to the conjugate of its coordinate
$S^c$ times the sign of the complementary shuffle, up to an overall
orientation sign. Returning to $A,AD$ by invertible changes of basis
only multiplies these exterior vectors by scalar determinants.
On the other hand
$\Delta_S(AD)=(-1)^{\sum_{s\in S}s}\Delta_S(A)$.
The signs cancel, leaving
$\Delta_{S^c}(A)=\lambda'\overline{\Delta_S(A)}$ with one
nonzero $\lambda'$ for all $S$. Because
$\Delta_{S_0}=1$ and $\Delta_{S_0^c}=\det U$,
$$
 \frac{\Delta_S(A)\Delta_{S^c}(A)}
 {\Delta_{S_0}(A)\Delta_{S_0^c}(A)}
 = |\Delta_S(A)|^2 .
$$
For $S=(S_0\setminus I)\cup J$, where $I$ denotes a set of
coordinate labels and $J$ a set of mixer labels with $|I|=|J|$,
Laplace expansion along the coordinate columns gives
$|\Delta_S(A)|^2=|\det U[I,J]|^2$.

## Continuous signed law, and why it becomes positive

For complementary $S,S^c$, Lam's Theorem 3.1 gives
$$
\Delta_S(A)\Delta_{S^c}(A)
=\sum_{\substack{\mu\text{ noncrossing perfect matching}\\
\text{each pair meets }S\text{ and }S^c}}F_\mu(A).
$$
This is an identity of degree-two homogeneous functions in the
Plücker embedding, hence applies to $A(U)$ for complex $U$.
Proposition 3.4 and Corollary 3.5 give the $F_\mu$ as real linear
combinations of degree-two Plücker monomials. Define continuous signed
real weights on $U(n)$ by
$$
w_\mu(U)=\operatorname{Re}
 \frac{F_\mu(A(U))}{\Delta_{S_0}(A(U))\Delta_{S_0^c}(A(U))}.
$$
Taking real parts does not change the complementary sum, which is real
by the previous identity. A noncrossing perfect matching on the
$2n$ boundary points always joins an even point to an odd point:
the points strictly between the endpoints of a chord must match
internally, so their number is even. Thus $\mu$ defines a permutation
$p_\mu$ from mixer labels to coordinate labels. Compatibility with
$S=(S_0\setminus I)\cup J$ says precisely $p_\mu(J)=I$.
All $\mu$ are compatible with $S_0$, so
$$
\sum_\mu w_\mu(U)=1,\qquad
|\det U[I,J]|^2=\sum_{\mu:p_\mu(J)=I}w_\mu(U).
$$
The weights can have either sign in general.

Suppose $A(U_0)$ lies in the strictly totally positive cell (all
maximal minors positive in the normalization $\Delta_{S_0}=1$).
Each $F_\mu$ is strictly positive there. To see this, fix the
single planar bipartite graph that parametrizes the entire top positive
positroid cell, with some edge weights $t_1,\ldots,t_d>0$ and other
edge weights $1$, from Lam's Theorem 2.4(2). By the double-dimer
definition in Lam's Section 3.1, each $F_\mu$ on this graph is a
polynomial in those parameters with nonnegative coefficients: each
contributing configuration contributes a monomial with positive
multiplicity. The polynomial is not identically zero. Otherwise the
basis element $F_\mu$ of Corollary 3.5 would vanish at every projective
point of the top positive cell; this cell is Zariski dense in the
Grassmannian (following Theorem 2.4), contradicting nonvanishing
of the basis element. Each polynomial therefore contains a positive
monomial and is positive at every positive parameter vector. Normalizing
Plücker coordinates only multiplies numerator and denominator by
the same square. At $U_0$ the denominator is positive, so
$w_\mu(U_0)>0$ for every $\mu$. There are finitely many $\mu$;
continuity yields a neighborhood of $U_0$ relative to the
**complex** unitary group in which all $w_\mu(U)>0$.
Fixed row/column permutations and diagonal unitary factors transport
this statement to equivalent centers.

For any $U$, Cauchy–Binet and the determinant expansion in squared
minors translate the signed law into
$$
\det(\operatorname{diag}a+U\operatorname{diag}b\,U^*)
=\sum_\mu w_\mu(U)\prod_j(a_{p_\mu(j)}+b_j).
$$
Thus a single probability vector works for all complex spectra on the
neighborhood. The determinant is in the relative interior of the full
matching hull: each permutation mixer realizes its own matching product,
so the signed identity and total mass one imply that every matching
product lies in the real affine span of the fixed noncrossing products.
If a supporting functional were tight at a strictly positive average
of those products, it would be tight at each of them, hence constant
on the affine span of the full hull. It cannot expose a proper face.
The convention includes line and singleton hulls.

The Lean interface [AlternatingMinorLaw.lean](MOC/AlternatingMinorLaw.lean)
checks compatibility, normalization, the determinant consequence,
and persistence of positivity for a continuous finite signed law.
Lam's theorem and the complementary graph-chart identity above are
external inputs, not Lean-verified statements in that module.

## Nonemptiness in every order

Choose $t_0<t_1<\cdots<t_{2n-1}$ in $\mathbb R$ and put
$\chi(t)=\prod_\ell(t-t_\ell)$. Let the $\ell$-th column of $C$ be
$$
|\chi'(t_\ell)|^{-1/2}(1,t_\ell,\ldots,t_\ell^{n-1})^\top .
$$
Every maximal minor of $C$ is positive by the Vandermonde formula.
The Lagrange interpolation identities
$\sum_\ell t_\ell^k/\chi'(t_\ell)=0$ for $0\le k\le2n-2$
follow by comparing the leading coefficient in the interpolant for
$t^k$. The signs of $\chi'(t_\ell)$ alternate, so the identities give
$CDC^\top=0$. Let $C_0$ consist of the even columns. Left multiplication
by $C_0^{-1}$, whose determinant is positive, puts those columns
equal to $I$, preserves strict Plücker positivity, and leaves the
isotropy equation unchanged. The odd columns form a real orthogonal
matrix $O$, a center for the theorem.

In these coordinates $O$ is the weighted Lagrange evaluation matrix.
With $r_i=t_{2i-2}$ and $s_j=t_{2j-1}$ for one-based matrix indices,
$$
O_{ij}=
\sqrt{\frac{|\chi'(r_i)|}{|\chi'(s_j)|}}
\prod_{k\ne i}\frac{s_j-r_k}{r_i-r_k}.
$$
This has the Cauchy form $u_i v_j/(r_i-s_j)$ after absorbing one
minus sign in the column factors. Conversely, the moment argument
in [the order-five note](OrderFiveContactReduction.md) proves that the
labels of any distinct-node orthogonal real Cauchy matrix alternate
after sorting; its rational normal curve representation makes its
graph chart strictly totally positive after signs and relabeling.
The neighborhood theorem applies to that entire Cauchy class, but
does not settle the determinant comparison outside these open sets.

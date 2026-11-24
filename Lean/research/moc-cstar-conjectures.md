# Marcus-de Oliveira: eleven C-star algebraic conjectures

These eleven statements retain the numbering in *C-star-algebraic forms of the Marcus–de Oliveira conjecture*. All dimensions are finite. The statements below contain the definitions necessary to read them without that paper.

## Setting and notation

Let $n\ge1$, and let $\mathcal A=M_n(\mathbb C)$ with the usual matrix trace $\operatorname{Tr}$, determinant $\det$, and adjoint $*$. Write $U(n)=\{u:u^*u=uu^*=I\}$ for the unitary group. An element $a$ is normal if $a^*a=aa^*$. For a normal element $a$, its spectrum $\sigma(a)$ is the set of its distinct eigenvalues. Its spectral projection $p_\lambda^a$ is the orthogonal projection onto the eigenspace of $\lambda$, and its multiplicity is $m_a(\lambda)=\operatorname{Tr}p_\lambda^a$. Thus $a=\sum_{\lambda\in\sigma(a)}\lambda p_\lambda^a$ and $\sum_\lambda m_a(\lambda)=n$.

A spectral list $(\lambda_1,\ldots,\lambda_n)$ repeats each $\lambda$ according to $m_a(\lambda)$; the list $(\mu_1,\ldots,\mu_n)$ is defined in the same way for $b$. Let $S_n$ be the set of permutations of $\{1,\ldots,n\}$. Define

$$
V(a,b)=\left\{\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)}):\pi\in S_n\right\},
\qquad P(a,b)=\operatorname{conv}V(a,b).
$$

Here $\operatorname{conv}$ denotes real-affine convex hull: a finite convex combination has real nonnegative coefficients with sum one. The unitary orbit of a normal element $b$ is $\mathcal O(b)=\{ubu^*:u\in U(n)\}$. These definitions are independent of the order of the spectral lists.

## Conjecture 1 — Matrix form

For every positive integer $n$, all normal matrices $a,b\in M_n(\mathbb C)$, and every $u\in U(n)$,

$$
\det(a+ubu^*)\in\operatorname{conv}\left\{
\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)}):\pi\in S_n
\right\}.
$$

Equivalently, for each such triple there are real numbers $w_\pi\ge0$, $\sum_\pi w_\pi=1$, such that the determinant is $\sum_\pi w_\pi\prod_j(\lambda_j+\mu_{\pi(j)})$. The coefficients may depend on the two matrices and on $u$.

## Conjecture 2 — Orbit form

Let $a,b\in\mathcal A$ be normal. For every normal $y\in\mathcal A$ with $\sigma(y)=\sigma(b)$ and $m_y(\mu)=m_b(\mu)$ for every $\mu\in\sigma(b)$,

$$
\det(a+y)\in P(a,b).
$$

Normal matrices have the same unitary orbit if and only if they have the same spectrum with multiplicity. Thus this statement and Conjecture 1 quantify over the same possible sums without requiring a specified unitary.

## Conjecture 3 — Commutant form

Let $a,b\in\mathcal A$ be normal. Define the commutant $\{a\}'=\{c\in\mathcal A:ca=ac\}$. For every $y\in\mathcal O(b)$,

$$
\det(a+y)\in\operatorname{conv}\{\det(a+z):z\in\mathcal O(b)\cap\{a\}'\}.
$$

The right side uses the commuting part of the orbit. Since two commuting normal matrices admit a common orthonormal eigenbasis, the determinants on this part are exactly $V(a,b)$. Each permutation of the spectral list of $b$ occurs by putting its eigenvalues on the eigenbasis of $a$ in that order.

## Conjecture 4 — Coupling (transport) form

Let $a,b\in\mathcal A$ be normal. Define the set of integer couplings of their multiplicities by

$$
\mathcal T(m_a,m_b)=
\left\{(m_{\lambda\mu})_{\lambda\in\sigma(a),\,\mu\in\sigma(b)}:
m_{\lambda\mu}\in\mathbb Z_{\ge0},\
\sum_\mu m_{\lambda\mu}=m_a(\lambda),\
\sum_\lambda m_{\lambda\mu}=m_b(\mu)\right\}.
$$

For every $u\in U(n)$,

$$
\det(a+ubu^*)\in\operatorname{conv}\left\{
\prod_{\lambda\in\sigma(a)}\prod_{\mu\in\sigma(b)}
(\lambda+\mu)^{m_{\lambda\mu}}:m\in\mathcal T(m_a,m_b)
\right\}.
$$

A factor with exponent zero is one, including when its base is zero. For a commuting representative $z\in\mathcal O(b)\cap\{a\}'$, the joint multiplicity is $\operatorname{Tr}(p_\lambda^a p_\mu^z)$. Conversely, each integer coupling gives a commuting pair by assigning the prescribed dimensions to simultaneous eigenspaces. Integer couplings give exactly the permutation products, including repeated eigenvalues.

## Conjecture 5 — Cartesian form

Let $h_1,h_2,k_1,k_2\in\mathcal A$ be self-adjoint, with $h_1h_2=h_2h_1$ and $k_1k_2=k_2k_1$. Let $(s_j,t_j)_{j=1}^n$ and $(r_j,q_j)_{j=1}^n$ be the joint real eigenvalue lists of $(h_1,h_2)$ and $(k_1,k_2)$, with their joint multiplicities. For every $u\in U(n)$,

$$
\det\left((h_1+uk_1u^*)+i(h_2+uk_2u^*)\right)
\in\operatorname{conv}\left\{
\prod_{j=1}^n\left((s_j+r_{\pi(j)})+i(t_j+q_{\pi(j)})\right):\pi\in S_n
\right\}.
$$

The matrices $a=h_1+ih_2$ and $b=k_1+ik_2$ are normal. Conversely, the real and imaginary self-adjoint parts of each normal matrix commute. Their eigenvalues are $s_j+it_j$ and $r_j+iq_j$, respectively.

## Conjecture 6 — Functional calculus form

Let $a,b\in\mathcal A$ be normal and let $f:\sigma(a)\to\mathbb C$, $g:\sigma(b)\to\mathbb C$ be any functions on their finite spectra. Define their functional calculus by

$$
f(a)=\sum_{\lambda\in\sigma(a)} f(\lambda)p_\lambda^a,\qquad
g(b)=\sum_{\mu\in\sigma(b)} g(\mu)p_\mu^b.
$$

For every $u\in U(n)$,

$$
\det(f(a)+ug(b)u^*)\in\operatorname{conv}\left\{
\prod_{j=1}^n(f(\lambda_j)+g(\mu_{\pi(j)})):\pi\in S_n
\right\}.
$$

The maps $f$ and $g$ need not be injective. The lists of the images retain multiplicities even if values coincide. Identity functions give Conjecture 1, and the image matrices are normal, so Conjecture 1 applied to them gives this form.

## Conjecture 7 — Affine and characteristic polynomial form

Let $a,b\in\mathcal A$ be normal. For every $u\in U(n)$ and every $s,t,z\in\mathbb C$,

$$
\det(sa+tubu^*+zI)\in\operatorname{conv}\left\{
\prod_{j=1}^n(s\lambda_j+t\mu_{\pi(j)}+z):\pi\in S_n
\right\}.
$$

In particular, at $s=t=1$, for every $z\in\mathbb C$,

$$
\det(zI+a+ubu^*)\in\operatorname{conv}\left\{
\prod_{j=1}^n(z+\lambda_j+\mu_{\pi(j)}):\pi\in S_n
\right\}.
$$

The characteristic-polynomial comparison is pointwise in the scalar variable. The weights may vary with $z$. The statement follows from Conjecture 6 by affine functions; $s=t=1,z=0$ gives Conjecture 1. It does not require one set of weights that works for the entire polynomial.

## Conjecture 8 — Universal free product form

Let $X,Y\subset\mathbb C$ be nonempty finite sets. Let $C(X)$ and $C(Y)$ denote the unital complex C-star algebras of all complex functions on these finite sets, with pointwise operations, conjugation as adjoint, and supremum norm. Let $\mathcal U=C(X)*_{\mathbb C}C(Y)$ be their full unital free product: its two copies have the same identity and satisfy their separate algebra relations, with no additional commutation relations between them. Write $\iota_X,\iota_Y$ for their canonical maps into $\mathcal U$.

Define $x=\iota_X(\operatorname{id}_X)$ and $y=\iota_Y(\operatorname{id}_Y)$. The coordinate functions are $\operatorname{id}_X(\lambda)=\lambda$ and $\operatorname{id}_Y(\mu)=\mu$. Let $q:\mathcal U\to C(X\times Y)$ be the unital quotient that makes the two copies commute, sending the generators to the two coordinate functions on $X\times Y$.

Fix integer multiplicity functions $m_X:X\to\mathbb Z_{\ge0}$ and $m_Y:Y\to\mathbb Z_{\ge0}$ with $\sum_Xm_X=\sum_Ym_Y=n$. Let $\operatorname{Rep}_n(\mathcal U;m_X,m_Y)$ consist of all unital adjoint-preserving representations $\rho:\mathcal U\to M_n(\mathbb C)$ such that the images of the indicator functions $\iota_X(1_{\{\lambda\}})$ and $\iota_Y(1_{\{\mu\}})$ have ranks $m_X(\lambda),m_Y(\mu)$. Let $\operatorname{Rep}^{\rm ab}_n(\mathcal U;m_X,m_Y)$ be the subset that factors through $q$.

For every $\pi\in\operatorname{Rep}_n(\mathcal U;m_X,m_Y)$,

$$
\det(\pi(x+y))\in\operatorname{conv}\{\det(\rho(x+y)):
\rho\in\operatorname{Rep}^{\rm ab}_n(\mathcal U;m_X,m_Y)\}.
$$

The two normal images $\pi(x),\pi(y)$ may have arbitrary relative spectral projections of the specified ranks. The abelian representations have commuting images. This is the determinant comparison between all relative positions and their commuting subset.

## Conjecture 9 — Compound (Cauchy-Binet) form

Let $\alpha,\beta\in\mathbb C^n$ and $W\in U(n)$. For subsets $S,T\subseteq\{1,\ldots,n\}$ of equal size, let $W[S,T]$ be the square submatrix with row indices in $S$ and column indices in $T$ (both in increasing order). Use $\det W[\varnothing,\varnothing]=1$. Let $S^c$ be the complement of $S$. Define $\alpha_S=\prod_{i\in S}\alpha_i$ and $\beta_T=\prod_{j\in T}\beta_j$, with empty products one. Define the real vector $v(W)$ by $v(W)_{S,T}=|\det W[S,T]|^2$ and the complex linear expression in its coordinates

$$
\ell_{\alpha,\beta}(v)=\sum_{k=0}^n\ \sum_{\substack{|S|=|T|=k}}\alpha_{S^c}\beta_T\,v_{S,T}.
$$

For each permutation $\pi$, let $P_\pi$ be the permutation matrix with its unit entry in row $i$ at column $\pi(i)$. Then for all $\alpha,\beta,W$,

$$
\ell_{\alpha,\beta}(v(W))\in
\operatorname{conv}\{\ell_{\alpha,\beta}(v(P_\pi)):\pi\in S_n\}.
$$

The determinant expansion by principal minors and the Cauchy-Binet formula give

$$
\ell_{\alpha,\beta}(v(W))=\det(\operatorname{diag}(\alpha)+W\operatorname{diag}(\beta)W^*).
$$

For a permutation matrix, $v(P_\pi)_{S,T}$ is one if $T=\pi(S)$ and zero otherwise. Thus the comparison terms are the products of the matched spectral sums.

## Conjecture 10 — Strong form (compound Birkhoff property)

For every positive integer $n$ and every $W\in U(n)$, there is one probability distribution $(w_\pi(W))_{\pi\in S_n}$ on permutations such that

$$
w_\pi(W)\ge0,\qquad \sum_{\pi\in S_n}w_\pi(W)=1,
$$

and, simultaneously for every pair of subsets $S,T\subseteq\{1,\ldots,n\}$ with $|S|=|T|$,

$$
|\det W[S,T]|^2=\sum_{\pi\in S_n}w_\pi(W)\,\mathbf1_{\{\pi(S)=T\}}.
$$

Here $\mathbf1_{\{\pi(S)=T\}}$ is one if the condition holds and zero otherwise. The minor convention includes the empty minor of value one. The same weights must apply to every size of minor and must not depend on any choices of eigenvalues.

This statement implies Conjecture 9 by applying $\ell_{\alpha,\beta}$, and thus implies Conjecture 1. It also gives two determinant-polynomial comparisons. For normal $a,b$ with spectral lists $\lambda,\mu$ and relative unitary position $u$, suitable weights give

$$
\det(tI-a-ubu^*)=\sum_{\pi\in S_n}w_\pi
\prod_{j=1}^n(t-\lambda_j-\mu_{\pi(j)})\quad\text{for every }t\in\mathbb C.
$$

Define $e_k(M)=\sum_{|R|=k}\det M[R,R]$, the $k$th elementary coefficient of the characteristic polynomial (with the usual alternating signs in that polynomial). Then the same weights also give

$$
e_k(a+ubu^*)=\sum_{\pi\in S_n}w_\pi
\sum_{|R|=k}\prod_{j\in R}(\lambda_j+\mu_{\pi(j)})\quad(1\le k\le n).
$$

Conjecture 1 does not demand such uniform weights: its weights may depend on the input eigenvalues. The source proves Conjecture 10 in orders at most three by complementary minors and the ordinary Birkhoff-von Neumann theorem; that proof does not settle higher orders.

## Conjecture 11 — Abelianization convexity principle

Let $X,Y\subset\mathbb C$ be nonempty finite sets and let $\mathcal U=C(X)*_{\mathbb C}C(Y)$, with inclusions $\iota_X,\iota_Y$ and abelianization quotient $q:\mathcal U\to C(X\times Y)$, as defined in Conjecture 8. Fix a positive integer $n$ and multiplicity functions $m_X,m_Y$ with nonnegative integer values and total $n$ each. Use the representation sets $\operatorname{Rep}_n(\mathcal U;m_X,m_Y)$ and $\operatorname{Rep}^{\rm ab}_n(\mathcal U;m_X,m_Y)$ of Conjecture 8.

Define the linear subspace

$$
\mathcal W=\{\iota_X(f)+\iota_Y(g): f\in C(X),\ g\in C(Y)\}\subseteq\mathcal U.
$$

For a matrix $M\in M_n(\mathbb C)$ define the following three types of maps:
- $\Psi(M)=\det M$, valued in $\mathbb C$;
- $\Psi(M)=e_k(M)=\sum_{|R|=k}\det M[R,R]$, valued in $\mathbb C$, for each $1\le k\le n$;
- $\Psi(M)=\chi_M$, the monic characteristic polynomial $\chi_M(t)=\det(tI-M)$ of degree $n$.

In the polynomial case take the real-affine convex hull of coefficient vectors of monic polynomials. Thus a single convex combination represents the polynomial for all $t$, not a new convex combination for each evaluation point.

For every $\pi\in\operatorname{Rep}_n(\mathcal U;m_X,m_Y)$, every $w\in\mathcal W$ and every choice of $\Psi$ above,

$$
\Psi(\pi(w))\in\operatorname{conv}\{\Psi(\rho(w)):
\rho\in\operatorname{Rep}^{\rm ab}_n(\mathcal U;m_X,m_Y)\}.
$$

The determinant case includes the free-product, orbit, commutant, integer-coupling, Cartesian, functional-calculus, affine and matrix forms. The coefficient and polynomial cases assert the additional coefficientwise and simultaneous polynomial comparisons. They allow the weights to depend on the chosen functions and on the representation. Conjecture 10 would supply weights independent of the eigenvalues. Conjecture 11 applies to sums of functions from the two copies of the free product; arbitrary products or other words in the free product are not included.

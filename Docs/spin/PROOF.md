# Scalar MOC for the full cubic symmetric-power family

Let $g\in SU(2)$. Set $U=\operatorname{Sym}^3(g)$ in the orthonormal monomial basis of binary cubics. For arbitrary $a,b\in\mathbb C^4$,

$$
 \det(D_a+UD_bU^*)\in\operatorname{conv}\{z_\pi:\pi\in S_4\},
 \qquad z_\pi=\prod_i(a_i+b_{\pi(i)}).
$$

The proof also applies after independent row and column phases or permutations of the mixer. The spectra have no restrictions.

## 1. The profile and the cost test

For a unitary $V$, let $y(V)_{I,J}=|\det V[I,J]|^2$, taking all equal-cardinality subsets. For permutation matrices write $P_\pi(I,J)=1_{\pi(I)=J}$. If $y(V)=\sum w_\pi P_\pi$, then the determinant expansion gives $d(V)=\sum w_\pi z_\pi$, for real signed weights of sum one. Jacobi's complementary-minor formula means that the orders zero through two determine the profile in dimension four.

Row and column phases reduce $g$ to a real rotation. Set $t=|g_{12}|^2$. Reversal of one basis changes $t$ to $1-t$, so take $0\le t\le1/2$. The supplied exact facet calculation verifies a positive common law unless

$$
 p(t)=1-4t-3t^2+22t^3-15t^4<0.
$$

The exceptional interval is inside $[3/10,47/100]$. We handle all its points below.

Use this order of thirteen permutations, followed by the anchor $4231$,

$$
 1324,1342,1423,1432,2143,2314,2341,2413,3124,3142,3214,3412,4123.
$$

Denote the set of the thirteen by $F_0$. These fourteen profile columns are linearly independent. The verifier expands the symmetric power on monomials and proves the polynomial identity

$$
 y(U)=\sum_{i\in F_0}w_i(t)P_i+\tfrac12p(t)P_{4231}.
$$

For the thirteen radii, in the displayed order, use

$$
 R=(1,3,3,2,1,3,1,1/2,3,1/2,2,4,1).
$$

The thirteen univariate inequalities $R_i w_i(t)+p(t)\ge0$ hold on the entire interval $[3/10,47/100]$. The verifier checks each by exact polynomial root counts.

A strict separation from the vertex hull would give real costs $h_\pi=\Re(\eta z_\pi)-c\ge0$ for all vertices and $\Re(\eta d(U))-c<0$. Because $w_i>0$ when $p<0$, the anchor cost is strictly positive. Rescale all costs by the same positive factor to have $h_{4231}=2$. Write $h=f+u$ in the fourteen selected coordinates, where $f=(0,\ldots,0,2)$ and $u_{14}=0$. Strict separation gives

$$
 u_i\ge0,\qquad \sum_i w_i u_i<-p,\qquad
 \sum_i u_i/R_i<1.
$$

Thus the violating cost would be inside the simplex with vertices $f$ and $f+R_i e_i$, with a strictly positive barycentric coefficient on $f$.

## 2. A polynomial that vanishes on all actual costs

Interpret the product coordinates as brackets of eight binary spinors, with the first four and last four giving the two spectral lists. In the fourteen chosen coordinates every perfect matching $M$ gives a linear form $\ell_M$. We use **twice** these forms in the computation, to obtain integer coefficients. The forms are uniquely determined by matching the coefficients of the 70 squarefree bracket-expansion monomials. Orient each pair in increasing order and let $\epsilon_M$ be the sign of the flattened matching. Define

$$
 F(x)=\tfrac16\sum_M\epsilon_M(2\ell_M(x))^3,\qquad
 H(x)=\operatorname{Hess}F(x),\qquad e=(1,\ldots,1),\qquad Q(x)=D_eF(x).
$$

This is a nonzero multiple of the Howard–Millson–Snowden–Vakil skew cubic. On a product point $x$, its derivative in any product-point direction $y$ is a multiple of the Pfaffian of the skew matrix with entries $[x_i,x_j]^2[y_i,y_j]$. Its underlying alternating space $\operatorname{Sym}^2(\mathbb C^2)\otimes\mathbb C^2$ has dimension six. Hence this order-eight Pfaffian vanishes. Product points span all fourteen coordinates, so they are singular points of $F$. Alternatively this is the singular-locus theorem of Howard et al.

The real parts of complex product points are on the secant variety since each is the average of the point and its complex conjugate. This includes any choice of the direction $\eta$ by complex homogeneity. On that variety $F=0$ and the Hessian determinant vanishes. Here one can also check Hessian singularity directly from $H(x+y)(x-y)=2(\nabla F(x)-\nabla F(y))$ at singular endpoints, using Euler's identity when the endpoints agree. The paper proves that on $F=0$, the Hessian determinant is a nonzero constant times the square of a degree-seven polynomial. The source is Howard, Millson, Snowden and Vakil, *The geometry of eight points in projective space*, Proposition 3.19 and the paragraph immediately following it, [arXiv:1103.5255](https://arxiv.org/pdf/1103.5255).

As $e$ is itself singular, $F(x+z e)=F(x)+zQ(x)$. Removing the arbitrary cost height gives the rational expression

$$
 N(x)=Q(x)^2\det H\bigl(x-F(x)e/Q(x)\bigr).
$$

This expression is a homogeneous polynomial of degree eighteen. Here are the denominator details. The symmetric matrix $H(e)$ has rank four and $e$ lies in its kernel, as verified exactly. In a basis with first vector $e$, followed by nine vectors completing this kernel, then four complementary vectors, write the nondegenerate four-by-four block of $H(e)$ as $J$. The $(1,1)$ and $(1,2)$ blocks of $H(x)$ vanish, since $e' H(x)v=x' H(e)v$. Its remaining first-row block is $\ell'=x_S'J$. If the nine-by-nine middle block of $H(x)$ is $K$, the coefficient of $z^3$ in $\det H(x+ze)$, in these coordinates, is

$$
 -\det K\det J\,\ell'J^{-1}\ell=-2Q(x)\det K\det J.
$$

There is no term above degree three. These claims follow by cofactor expansion of the first row and column. A fixed nonzero change-of-basis factor has no effect on divisibility by $Q$. Consequently multiplying by $Q^2$ clears the denominators after $z=-F/Q$.

The published square identity on the cubic makes $N$ a rational square up to a constant. A rational square that is a polynomial has a polynomial square root over the complex numbers, by unique factorization. At $f$, the checker obtains $F(f)=Q(f)=-8$ and $N(f)=-2^{48}$. Normalize the sign and write $-N=P^2$, $P(f)=2^{24}$. Then $P$ is a polynomial of degree nine with rational coefficients. Rationality follows either by uniqueness of this normalization or by Taylor recursion at $f$.

For $Q(h)\ne0$, any cost $h$ made from a spectral real part and any real constant lifts back to the secant on this cubic, so $P(h)=0$. This identity also holds when $Q(h)=0$, by polynomial continuity in the real and imaginary parts of the original parameters. The nonvanishing required for density is concrete. For both lists $(0,1,2,i)$, $Q=-32$ at the real cost vector. Thus every actual violating cost would satisfy $P(h)=0$.

## 3. Exact positivity certificate

The C++ verifier computes all coefficients of $P$ in the degree-nine Bernstein basis on the simplex from Section 1, with one common positive scaling. Of the 497,420 coefficients, 480,297 are positive and 17,123 vanish. The coefficient at the vertex $f$ is positive. All basis functions are nonnegative, and the one corresponding to the vertex $f$ is the ninth power of its barycentric coordinate. Hence $P(h)>0$ whenever the coefficient of $f$ in $h$ is positive. This contradicts the necessary equality $P(h)=0$. It proves the original scalar MOC for the family.

To reproduce, run `python3 -B Code/spin/verify_scalar.py` from the repository root. It requires SymPy, a C++17 compiler with OpenMP, and GMP. The script constructs the matching tensor, verifies the spin inequalities, compiles the exact arithmetic evaluator, and performs the following steps.

1. For each nonnegative integer vector $\alpha$ in 13 coordinates with $|\alpha|\le9$, put $h=f+11\alpha$, keeping the last coordinate equal to two. Evaluate $-N(h)=-\det(Q(h)H(h)-F(h)H(e))/Q(h)^{12}$ exactly. The code uses fraction-free elimination and checks exact divisibility and a perfect-square remainder.
2. Choose the square root congruent to $2^{24}$ modulo eleven. Indeed $Q(f)=-8$ is a unit modulo eleven, so the Taylor series of $-N(f+u)$ has coefficients integral at eleven. Its normalized square root has the same property by the recursive coefficient equations, since $2P(f)$ is a unit. Consequently $P(f+11\alpha)\equiv2^{24}\pmod{11}$. This distinguishes both signs at every grid point.
3. The total-degree-nine simplex grid is unisolvent. Coordinatewise forward differences give the coefficients in the product of univariate binomial polynomials. Signed Stirling numbers of the first kind convert these to ordinary monomial coefficients. A common positive factor $9!$ clears interpolation denominators. Every asserted integer division during this conversion is checked.
4. Apply $u_i=R_i y_i/11$. For a power coefficient $a_\alpha$ after this substitution, its contribution to the degree-nine Bernstein coefficient indexed by $\gamma$ equals
   $$
     a_\alpha\frac{(9-|\alpha|)!}{9!}\prod_i\alpha_i!\binom{\gamma_i}{\alpha_i}.
   $$
   The final coordinate is $1-\sum_i y_i$. The program computes the product of binomial transforms independently in each coordinate. It checks the exact zero count and the positive coefficient on $f$.

The same proof applies to any four-dimensional profile with the signed expansion in Section 1 and the thirteen inequalities $R_i w_i+p\ge0$, if $p<0$. Relabeling rows and columns gives further such regions. The scalar result for arbitrary $U(4)$ requires control of the profiles outside these regions.

## 4. A second certified simplex

The matrix

$$
V=\frac1{14}
\begin{pmatrix}
-7&7&7&7\\
-11&-7&-5&1\\
1&7&-11&5\\
-5&7&-1&-11
\end{pmatrix}
$$

is rational and orthogonal. It lies outside all 576 labeled copies of the preceding simplex criterion. Its smallest facet value is $-3/98$. Among the twelve labelings with a negative facet value, the largest minimum of the thirteen inequalities is $-3/196$. Thus this first set of certificates does not cover all orthogonal matrices.

The same method proves scalar MOC for $V$ after replacing $R$ with

$$
(1/3,6,6,3/2,6,1/4,3/2,1/3,1/4,1/3,1/6,1/4,3/2).
$$

For this simplex every one of the 497,420 Bernstein coefficients is strictly positive. The main verifier checks this sign result, and `python3 -B Code/spin/check_coverage.py` checks both the original coverage gap and membership in the second criterion.

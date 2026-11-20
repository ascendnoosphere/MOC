# Exact coverage under finite spectral distributions

These are theorems about explicit probability models for normal 4-by-4 matrices. They are not a proof of the unrestricted Marcus–de Oliveira conjecture, and the uncovered event is not asserted to contain a counterexample. No literature-priority claim is made.

## 1. The four-dimensional sufficient event

Let \(A=\operatorname{diag}(a_1,\ldots,a_4)\), \(B=\operatorname{diag}(b_1,\ldots,b_4)\), and \(U\in U(4)\) be arbitrary. The determinant inclusion holds if at least one of the following occurs:

1. The spectrum of \(A\) has a repeated entry.
2. The spectrum of \(B\) has a repeated entry.
3. Some \(a_i+b_j=0\).

Equivalently, it holds whenever the eight numbers

\[
a_1,a_2,a_3,a_4,-b_1,-b_2,-b_3,-b_4
\]

are not all distinct. The proofs of the two required special cases are given below. They do not assume the general conjecture.

### 1.1 A self-contained proof for a repeated eigenvalue

The following argument works in any dimension when one matrix has an eigenvalue of multiplicity at least \(n-2\). This is an established special case; the proof is included to make the coverage calculation independent of an uncertain citation.

Write the conjugated matrix as

\[
UBU^*=\beta I+\delta_1xx^*+\delta_2yy^*,\qquad
x^*x=y^*y=1,\quad x^*y=0.
\]

Set \(X_i=|x_i|^2\), \(Y_i=|y_i|^2\), and

\[
q_{ij}=|x_i y_j-x_j y_i|^2\quad(i<j).
\]

We construct numbers \(p_{ij}\ge0\), \(i\ne j\), satisfying

\[
p_{ij}+p_{ji}=q_{ij},\qquad
\sum_{j\ne i}p_{ij}=X_i,\qquad
\sum_{i\ne j}p_{ij}=Y_j,\qquad
\sum_{i\ne j}p_{ij}=1.
\]

Regard each undirected edge \(\{i,j\}\) as carrying mass \(q_{ij}\), to be allocated to its endpoints. The mass allocated to endpoint \(i\) is called \(p_{ij}\). Prescribe total incoming allocation \(X_i\) at vertex \(i\). The source–edge–vertex–sink network has capacities \(q_{ij}\) from the source to each edge, infinite capacities from an edge to its two endpoints, and capacities \(X_i\) from vertices to the sink. The max-flow/min-cut condition for a flow of total mass one is precisely

\[
\sum_{i<j,\ i,j\in S}q_{ij}\le\sum_{i\in S}X_i
\quad\text{for every vertex subset }S,
\]

together with equality of the total edge mass and total prescribed mass. Indeed, a finite cut with vertex set \(S\) on the source side has minimum capacity

\[
1-\sum_{i<j,\ i,j\in S}q_{ij}+\sum_{i\in S}X_i.
\]

Let \(X_S=\sum_{i\in S}X_i\), \(Y_S=\sum_{i\in S}Y_i\), and \(Z_S=\sum_{i\in S}\overline{x_i}y_i\). Cauchy–Binet gives

\[
\sum_{i<j,\ i,j\in S}q_{ij}=X_SY_S-|Z_S|^2\le X_S,
\]

because \(Y_S\le1\). The total edge mass is one. Therefore the flow exists. Finally,

\[
\sum_{j\ne i}q_{ij}=X_i+Y_i
\]

by orthonormality, so the second marginal equals \(Y_i\), as required.

For \(C=\operatorname{diag}(c_i)\), compare the constant, \(\delta_1\), \(\delta_2\), and \(\delta_1\delta_2\) coefficients in the determinant. The marginal identities imply the exact polynomial identity

\[
\det(C+\delta_1xx^*+\delta_2yy^*)
=\sum_{i\ne j}p_{ij}(c_i+\delta_1)(c_j+\delta_2)
\prod_{\ell\notin\{i,j\}}c_\ell.
\]

Taking \(c_i=a_i+\beta\) expresses the determinant as a convex combination of permutation vertices. No inverse of \(C\) is used. In dimension four, any repeated eigenvalue has multiplicity at least \(n-2=2\), so this covers either repeated spectrum; swapping the two matrices treats repetition in \(A\).

### 1.2 Independent audit and proof for one zero paired sum

The proof in `zero_paired_sum_n4.md` passes independent audit. The essential argument is reproduced here.

Relabel and apply opposite scalar shifts to arrange \(a_0=b_0=0\), with the remaining index set \(T=\{1,2,3\}\). Define

\[
r=1-|U_{00}|^2,\quad x_i=|U_{i0}|^2,\quad y_\ell=|U_{0\ell}|^2,
\quad Q_{i\ell}=|\det U_{\{0,i\},T\setminus\{\ell\}}|^2.
\]

Cauchy–Binet and complementary unitary minors give

\[
\sum_\ell Q_{i\ell}=r-x_i,\quad
\sum_i Q_{i\ell}=r-y_\ell,\quad
\sum_i x_i=\sum_\ell y_\ell=r.
\]

If \(r>0\), the matrix

\[
\frac1r\begin{pmatrix}Q&x\\y^T&0\end{pmatrix}
\]

is doubly stochastic. A Birkhoff decomposition induces a probability law on two-edge matchings of \(K_{3,3}\). The edge, missing-row, and missing-column marginals are \(Q_{i\ell}/r\), \(x_i/r\), and \(y_\ell/r\), respectively.

For matching edges \((i_1,\ell_1),(i_2,\ell_2)\), missing row \(h\), and missing column \(k\), define

\[
\pi(0)=h,\quad\pi(k)=0,\quad
\pi(\ell_1)=i_2,\quad\pi(\ell_2)=i_1.
\]

The two matched assignments must be crossed. This bijects the 18 matchings and the 18 permutations with \(\pi(0)\ne0\). Its vertex is

\[
z_\pi=a_Tb_k+a_hb_T+
\sum_{(i,\ell)\in M}a_{T\setminus\{i\}}b_{T\setminus\{\ell\}}.
\]

The determinant's minor expansion has exactly the same terms with coefficients \(y_k\), \(x_h\), and \(Q_{i\ell}\). Consequently, \(r\) times the matching expectation equals the determinant. Assign the remaining mass \(1-r\) to the identity permutation, whose vertex is zero. If \(r=0\), all the relevant coefficients vanish, so the determinant itself is zero. This proves the assertion.

There is no use of a universal probability law matching all minors: only the 15 minors whose monomials survive \(a_0=b_0=0\) are represented. The singular and endpoint cases are included.

## 2. Exact coverage for a uniform finite distribution

Let \(S\subset\mathbb C\) have cardinality \(m\). Sample the eight variables \(a_1,\ldots,a_4,-b_1,\ldots,-b_4\) independently and uniformly from \(S\). Equivalently, sample the \(a_i\) uniformly from \(S\) and the \(b_j\) uniformly from \(-S\). If \(S=-S\), both spectra use the same distribution.

The relative unitary \(U\) can follow any law, even a law depending on the sampled spectra: every covered pair satisfies the inclusion for every \(U\).

Let \((m)_k=m(m-1)\cdots(m-k+1)\), interpreted as zero for \(k>m\), and let \(\left\{\begin{smallmatrix}4\\k\end{smallmatrix}\right\}\) denote a Stirling number of the second kind. The probability of at least one zero paired sum is exactly

\[
P_0(m)=1-\frac1{m^8}
\sum_{k=1}^4 (m)_k
\left\{\begin{matrix}4\\k\end{matrix}\right\}(m-k)^4.
\]

Indeed, exactly \((m)_k\left\{\begin{smallmatrix}4\\k\end{smallmatrix}\right\}\) ordered \(a\)-tuples use \(k\) distinct values. An independent \(-b\)-tuple avoids them in exactly \((m-k)^4\) ways. Here the four Stirling numbers are \(1,7,6,1\).

When the repeated-spectrum case is also included, the uncovered event is simply that all eight draws are different. Therefore the sufficient event has probability

\[
\boxed{P_{\rm covered}(m)=1-\frac{(m)_8}{m^8}.}
\]

This is an exact probability of a sufficient event, and hence a **lower bound**, not an asserted equality, for the probability that MOC holds.

| Support | Zero paired sum alone | Including either repeated spectrum |
|---|---:|---:|
| \(m=16\) | \(171755011/268435456\), about \(63.98372762\%\) | \(14750191/16777216\), about \(87.91798949\%\) |
| \(m=25\) | \(116741497/244140625\), about \(47.81731717\%\) | \(871830293/1220703125\), about \(71.42033760\%\) |

Concrete symmetric supports are

\[
S_{16}=\{x+iy:x,y\in\{-3,-1,1,3\}\},\qquad
S_{25}=\{x+iy:x,y\in\{-2,-1,0,1,2\}\}.
\]

The stronger coverage probability is at least one half for every \(m\le42\); at \(m=42\) it is approximately \(0.50850479\), while at \(m=43\) it is approximately \(0.49977387\). This threshold follows from exact integer comparison and monotonicity of \(\prod_{j=0}^7(1-j/m)\) for \(m\ge8\). For \(m\le7\), coverage is exactly one by the pigeonhole principle.

The finite support model is essential. These collision conditions have probability zero for independent spectra from continuous densities and do not establish any positive fraction of full-dimensional continuous spectral space.

## 3. Nonuniform distributions and an information-theoretic bound

More generally, let the eight variables \(a_i,-b_j\) be independent with the same finite distribution \(p=(p_1,\ldots,p_m)\). This requires mirrored distributions for \(a\) and \(b\); if both spectra are instead sampled from the same law, that law must be symmetric under negation for this statement to apply.

The exact sufficient-event probability is

\[
P_{\rm covered}(p)=1-8!e_8(p),
\]

where \(e_8\) is the eighth elementary symmetric polynomial. The factor \(8!\) counts the orderings of each eight-element support subset.

Uniform probabilities minimize this coverage over all distributions on the given \(m\)-point support:

\[
e_8(p)\le\binom m8m^{-8},\qquad
P_{\rm covered}(p)\ge1-\frac{(m)_8}{m^8}.
\]

For an elementary proof, fix all probabilities except \(p_i,p_j\). The terms involving these two are

\[
p_ip_j e_6(p_{\rm rest})+(p_i+p_j)e_7(p_{\rm rest})+e_8(p_{\rm rest}).
\]

Replacing \(p_i,p_j\) by their average preserves the sum and increases their product, so cannot decrease \(e_8\). Repeated averaging tending to the uniform vector and continuity prove the bound. Thus the 16- and 25-point guarantees also hold for arbitrary nonuniform mirrored laws on these supports.

A bound expressed through collision moments is available without evaluating \(e_8\). Put

\[
S_2=\sum_jp_j^2,\qquad S_3=\sum_jp_j^3,
\]

and let \(C\) count the equal pairs among the eight draws. There are 28 pairs, 168 unordered pairs of pairs sharing one index, and 210 disjoint unordered pairs of pairs. Hence

\[
\mathbb E C=28S_2,\qquad
\mathbb E C^2=28S_2+336S_3+420S_2^2.
\]

Cauchy–Schwarz gives

\[
\boxed{P_{\rm covered}(p)=\Pr(C>0)
\ge\frac{(28S_2)^2}{28S_2+336S_3+420S_2^2}.}
\]

In terms of the Rényi entropies \(H_2=-\log S_2\) and \(H_3=-\tfrac12\log S_3\), the bound is

\[
\frac{28}{e^{H_2}+12e^{2H_2-2H_3}+15}.
\]

For the uniform law, this simplifies to \(28/(m+27)\). It already proves coverage of at least one half for \(m\le29\), including \(28/43\) for the 16-point grid and \(7/13\) for the 25-point grid. The exact counting formula gives the stronger percentages above.

## 4. Verification and presentation limits

`exact_coverage.py` uses only Python's standard library and exact rational arithmetic. It independently checks the zero-pair formula by direct enumeration for support sizes one through four, checks the injection counts, computes the exact fractions and the half-coverage threshold, and verifies a nonuniform example. Its output is `exact_coverage.json`.

No Monte Carlo result is required for these guarantees. The matrices remain normal because the random quantities are eigenvalues and the relative basis is unitary. These statements concern a finite spectral distribution, not iid unrestricted matrix entries, not Haar-almost-everywhere truth for arbitrary fixed spectra, and not a p-adic order or notion of convexity.

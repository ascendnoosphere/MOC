# Exact Fourier permutation laws and certified neighborhoods

This note proves the Marcus–de Oliveira enclosure for arbitrary complex spectra when the relative eigenbasis is the normalized Fourier matrix of order 6, 7, or 8. It also proves the enclosure throughout explicit full-dimensional neighborhoods of the Fourier matrices of orders 5 and 7.

The fixed Fourier results use finite exact algebraic certificates, checked with rational arithmetic in cyclotomic fields. The neighborhood results then follow analytically from strictly positive base laws. Neither numerical optimization nor the unrestricted Marcus–de Oliveira conjecture is used as a lemma. Publication novelty has not been established.

## 1. The stronger property being certified

Index coordinates by \(\{0,\ldots,n-1\}\). For a unitary matrix \(U\), a common permutation law means nonnegative numbers \(p_\pi\), summing to one, such that

\[
|\det U_{I,J}|^2=\sum_{\pi:\,\pi(J)=I}p_\pi
\tag{1}
\]

for every pair of subsets \(I,J\) of equal size.

This is a property of \(U\), with no dependence on spectra. It is stronger than what Marcus–de Oliveira requires and fails for some unitary matrices. The assertions below concern specified matrices and neighborhoods only.

If (1) holds, the elementary determinant expansion gives, for arbitrary complex \(a_i,b_j\),

\[
\begin{aligned}
\det(\operatorname{diag}(a)+U\operatorname{diag}(b)U^*)
&=\sum_{|I|=|J|}a_{I^c}b_J|\det U_{I,J}|^2\\
&=\sum_\pi p_\pi\prod_{j=0}^{n-1}(a_{\pi(j)}+b_j).
\end{aligned}
\tag{2}
\]

Thus every common law below proves the desired determinant enclosure for all spectra at that relative eigenbasis.

## 2. Orbit notation

Let

\[
\zeta_n=e^{2\pi i/n},\qquad (F_n)_{ij}=n^{-1/2}\zeta_n^{ij}.
\]

For a permutation \(\pi\) of \(\mathbb Z/n\mathbb Z\), define

\[
\mathcal O_n(\pi)=
\left\{j\longmapsto r\,\pi(rj+t)+s:
r\in(\mathbb Z/n\mathbb Z)^\times,\ s,t\in\mathbb Z/n\mathbb Z
\right\}.
\tag{3}
\]

Repeated permutations in this set are counted only once. A listed mass \(w\) on an orbit means that each of its members receives probability \(w/|\mathcal O_n(\pi)|\).

This orbit action comes from affine row and column changes that preserve all Fourier minor magnitudes, up to the corresponding reindexing. The verifier nevertheless checks every subset pair directly; it does not assume an unverified reduction to orbit representatives.

## 3. Exact common laws for \(F_6,F_7,F_8\)

For \(F_6\), use:

| Representative \((\pi(0),\ldots,\pi(5))\) | Orbit size | Mass |
|---|---:|---:|
| \((0,3,4,5,2,1)\) | 36 | \(1/4\) |
| \((0,4,2,5,1,3)\) | 36 | \(3/4\) |

For \(F_7\), put

\[
\tau=2\cos(2\pi/7).
\]

It is the unique root greater than one of

\[
\tau^3+\tau^2-2\tau-1=0,
\]

and \(6/5<\tau<5/4\). Use:

| Representative | Orbit size | Mass |
|---|---:|---:|
| \((0,3,5,1,4,6,2)\) | 49 | \((16+2\tau-\tau^2)/27\) |
| \((0,2,4,3,5,1,6)\) | 98 | \((25-7\tau-10\tau^2)/27\) |
| \((0,2,6,3,1,5,4)\) | 98 | \((-20+11\tau+8\tau^2)/27\) |
| \((0,1,4,5,6,2,3)\) | 49 | \((2-2\tau+\tau^2)/9\) |

These masses sum to one. Their positivity follows by substituting the endpoints \(6/5,5/4\) in the positive and negative coefficient terms. For example, the second numerator is decreasing on this interval and exceeds its value \(5/8\) at \(5/4\).

For \(F_8\), use:

| Representative | Orbit size | Mass |
|---|---:|---:|
| \((0,4,7,5,1,3,6,2)\) | 256 | \(3/4-\sqrt2/2\) |
| \((0,6,5,1,3,7,2,4)\) | 256 | \(\sqrt2-5/4\) |
| \((0,3,6,2,5,4,7,1)\) | 256 | \(3/4-\sqrt2/2\) |
| \((0,5,2,4,1,6,3,7)\) | 256 | \(1/4\) |
| \((0,4,6,1,3,7,5,2)\) | 128 | \(1/2\) |

The masses sum to one and are positive, for example using \(7/5<\sqrt2<10/7\).

### Exact verification of the finite certificates

For each listed orbit \(\mathcal O_\ell\), form the integer count

\[
C_{\ell,I,J}
=\#\{\pi\in\mathcal O_\ell:\pi(J)=I\}.
\]

The verified identities are

\[
\sum_\ell \frac{w_\ell C_{\ell,I,J}}{|\mathcal O_\ell|}
=n^{-k}\left|
\det(\zeta_n^{ij})_{i\in I,j\in J}
\right|^2,\qquad |I|=|J|=k.
\tag{4}
\]

The program exact_fourier_laws.py checks these identities exactly in

\[
\mathbb Q[X]/(\Phi_n(X)),
\]

using

\[
\Phi_6=X^2-X+1,\quad
\Phi_7=1+X+\cdots+X^6,\quad
\Phi_8=X^4+1.
\]

It expands each determinant as an integer linear combination of powers of \(\zeta_n\), multiplies by its conjugate using \(\overline{\zeta_n}=\zeta_n^{-1}\), and compares the resulting rational coefficient vectors. It checks 662 identities for \(F_6\), 1716 for \(F_7\), and 8885 for \(F_8\), covering all \(k\leq\lfloor n/2\rfloor\). Jacobi's complementary-minor identity supplies the remaining sizes:

\[
|\det U_{I,J}|^2=|\det U_{I^c,J^c}|^2.
\]

For permutations, \(\pi(J)=I\) is equivalent to \(\pi(J^c)=I^c\), so the probability identities also pass to complements.

For the \(F_7\) field representation, the program's weights reduce to the displayed polynomials in \(\tau\) by

\[
\tau=-1-\zeta_7^2-\zeta_7^3-\zeta_7^4-\zeta_7^5,
\qquad
\tau^2=2+\zeta_7^2+\zeta_7^5.
\]

For \(F_8\), \(\sqrt2=\zeta_8-\zeta_8^3\).

An independent checker also verified the same counts using determinants of Gram matrices \(MM^*\), rather than multiplying \(\det M\) by its conjugate. The independent common integer denominators were 144, 2646, and 1024.

Consequently (1) and hence (2) hold for \(U=F_6,F_7,F_8\). In matrix terms, this includes arbitrary diagonal \(A\) and arbitrary circulant \(B\) in these dimensions.

## 4. A signed law for every unitary matrix

For any unitary \(U\), set

\[
\rho_\pi(U)=
\operatorname{Re}\left(
\frac{\operatorname{sgn}(\pi)\prod_jU_{\pi(j),j}}{\det U}
\right).
\tag{5}
\]

These numbers need not be positive. They nevertheless satisfy every common-law linear identity:

\[
\sum_\pi\rho_\pi(U)=1,\qquad
\sum_{\pi:\pi(J)=I}\rho_\pi(U)=|\det U_{I,J}|^2.
\tag{6}
\]

To prove this, group the Leibniz determinant expansion according to \(\pi(J)=I\). Before taking real parts, its numerator is

\[
(-1)^{\sum I+\sum J}\det U_{I,J}\det U_{I^c,J^c}.
\]

Jacobi's identity and \(U^{-1}=U^*\) give

\[
(-1)^{\sum I+\sum J}
\frac{\det U_{I^c,J^c}}{\det U}
=\overline{\det U_{I,J}},
\]

which proves (6).

Suppose a reference unitary \(U_0\) has a strictly positive common law \(p^0_\pi\). Then

\[
p_\pi(U)=p^0_\pi+\rho_\pi(U)-\rho_\pi(U_0)
\tag{7}
\]

automatically satisfies all the common-law equalities for \(U\). Positivity follows whenever

\[
\max_\pi|\rho_\pi(U)-\rho_\pi(U_0)|
<\min_\pi p^0_\pi.
\tag{8}
\]

This is a local transfer of an already proved positive law; it does not assume positivity for arbitrary \(U\).

## 5. An explicit perturbation bound at Fourier matrices

Let \(U\) be unitary and

\[
\delta=\max_{i,j}|U_{ij}-(F_n)_{ij}|,\qquad m=n^{-1/2}.
\]

Telescoping a product of \(n\) entries gives

\[
\left|\prod_jU_{\pi(j),j}
-\prod_j(F_n)_{\pi(j),j}\right|
\le n\delta(m+\delta)^{n-1}.
\]

Telescoping the determinant column by column and applying Hadamard's inequality gives

\[
|\det U-\det F_n|\le n\sqrt n\,\delta.
\]

Every mixed column occurring in this telescoping expansion is a unit column of \(U\) or \(F_n\); the one difference column has norm at most \(\sqrt n\,\delta\). Since both determinants have modulus one, (5) therefore gives

\[
\boxed{
|\rho_\pi(U)-\rho_\pi(F_n)|
\le n\delta\left[
(n^{-1/2}+\delta)^{n-1}+n^{(1-n)/2}
\right].
}
\tag{9}
\]

This bound is uniform over all permutations and all spectra.

## 6. A full-dimensional neighborhood of \(F_5\)

Let

\[
\alpha=1-\frac1{\sqrt5},\qquad
\mathcal A=\{j\mapsto rj+s:r\in\{2,3\},\ s\in\mathbb F_5\}.
\]

The ten affine permutations in \(\mathcal A\), together with the uniform law on all 120 permutations, define

\[
p^0_\pi=\frac{\alpha}{120}
+\frac1{10\sqrt5}\mathbf1_{\{\pi\in\mathcal A\}}.
\tag{10}
\]

This is a common law for \(F_5\). Here is an elementary verification.

All singleton probabilities are \(1/5\). For two-element subsets with differences \(c,d\), the uniform law gives probability \(1/10\). The uniform law on \(\mathcal A\) gives probability zero when \(cd\equiv\pm1\pmod5\), and \(1/5\) when \(cd\equiv\pm2\pmod5\). The mixture (10) therefore gives

\[
\frac{5-\sqrt5}{50}
\quad\hbox{or}\quad
\frac{5+\sqrt5}{50},
\]

respectively, exactly

\[
|\det(F_5)_{I,J}|^2
=\frac4{25}\sin^2\frac{\pi cd}{5}.
\]

Complements give sizes three and four, and normalization gives sizes zero and five.

Moreover,

\[
\min_\pi p^0_\pi=\frac{1-1/\sqrt5}{120}>\frac{11}{2400}.
\tag{11}
\]

If \(\delta\le1/100\), then \(1/\sqrt5<9/20\) and (9) imply

\[
|\rho_\pi(U)-\rho_\pi(F_5)|
<
\frac1{20}\left[\left(\frac{23}{50}\right)^4+\frac1{25}\right]
=\frac{529841}{125000000}
<\frac{11}{2400}.
\]

Thus (7), with base law (10), is strictly positive.

**Theorem.** For every unitary \(U\) satisfying

\[
\max_{i,j}|U_{ij}-(F_5)_{ij}|\le\frac1{100},
\]

and every pair of complex spectra \(a,b\), the weights (7) give the convex identity (2).

This is a full-dimensional region of the unitary group. The perturbations need not preserve any Fourier or circulant structure.

## 7. A full-dimensional neighborhood of \(F_7\)

There is a different \(F_7\) law with a positive uniform component. Use the following orbit masses, with the same \(\tau=2\cos(2\pi/7)\):

| Representative or distribution | Size | Mass |
|---|---:|---:|
| \((0,2,6,4,1,5,3)\) | 49 | \((7+\tau-4\tau^2)/5\) |
| \((0,2,5,4,1,6,3)\) | 98 | \((-38+6\tau+21\tau^2)/20\) |
| \((0,1,4,6,2,5,3)\) | 98 | \((-6+2\tau+7\tau^2)/20\) |
| \((0,3,6,2,5,1,4)\) | 21 | \(6(3-\tau-\tau^2)/35\) |
| Uniform distribution on \(S_7\) | 5040 | \(\kappa=3(3-\tau-\tau^2)/7\) |

The masses sum to one. The exact verifier exact_interior7.py checks all 1716 subset-pair equalities in \(\mathbb Q(\zeta_7)\). An independent Gram-determinant verifier checked them again with common denominator 11760.

The polynomial \(g(t)=t^3+t^2-2t-1\) is strictly increasing for \(t>1\), with

\[
g(31/25)<0<g(5/4).
\]

Thus \(31/25<\tau<5/4\). Direct interval substitution proves every displayed mass positive and gives

\[
\kappa>\frac9{112}.
\]

Since the uniform component reaches every permutation, this law satisfies

\[
\min_\pi p^0_\pi>\frac9{112\cdot5040}=\frac1{62720}.
\tag{12}
\]

For \(\delta\le1/3000\), use \(1/\sqrt7<19/50\) in (9):

\[
|\rho_\pi(U)-\rho_\pi(F_7)|
<
\frac7{3000}
\left[\left(\frac{381}{1000}\right)^6+\frac1{343}\right]
<\frac1{62720}.
\]

All inequalities in this radius calculation are checked as rational inequalities by verify_neighborhood_bounds.py.

**Theorem.** For every unitary \(U\) satisfying

\[
\max_{i,j}|U_{ij}-(F_7)_{ij}|\le\frac1{3000},
\]

the corrected law (7), with the base law above, is strictly positive and proves (2) for arbitrary complex spectra.

## 8. Reproduction and scope

The three exact scripts use only the Python standard library:

    python exact_fourier_laws.py
    python exact_interior7.py
    python verify_neighborhood_bounds.py

They can be run from any working directory. They write their JSON audit summaries beside the corresponding script, using paths relative to their own file locations.

The exact Fourier laws and both neighborhood theorems are proved here by the displayed formulas and finite exact checks. The computations establish no universal common-law theorem and no full solution of Marcus–de Oliveira. The tested two-parameter order-six Hadamard deformation is not included as a theorem: numerical feasibility alone was insufficient to prove it.

Searches did not locate a primary publication explicitly containing these particular Fourier certificates or radii. That absence is not a proof of novelty. Known results about two commuting circulants, circular spectra, or selected circulant/skew-circulant pairs should not be confused with the unrestricted spectra at the fixed relative eigenbases or their neighborhoods treated here.

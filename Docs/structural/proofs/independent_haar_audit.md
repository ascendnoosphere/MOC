# Independent audit: Haar variance, covariance, and explicit coverage

**Verdict: the variance theorem, real covariance extension, exact four-dimensional example, explicit spectral neighborhood, and Gaussian corollary pass this mathematical audit.** The result is probabilistic over Haar relative eigenbases; it does not prove the inclusion for every unitary or solve unrestricted MOC. No literature-priority assertion is made.

## 1. The integration identity and its spectral gap

Let \(U\) be Haar on \(U(n)\), \(n\ge2\), and put

\[
d=\det(A+UBU^*),\quad z_\pi=\prod_j(a_{\pi(j)}+b_j),\quad
c=\frac1{n!}\sum_\pi z_\pi.
\]

With \(m_\pi(U)=\prod_jU_{\pi(j),j}\), define

\[
q_\pi(U)=\frac{\operatorname{sgn}(\pi)m_\pi(U)}{\det U}.
\]

Leibniz expansion of \(\det(AU+UB)/\det U\) gives

\[
d=\sum_\pi q_\pi z_\pi,\qquad\sum_\pi q_\pi=1.
\]

The \(q_\pi\) need not be real or nonnegative. They are not asserted to form convex weights.

Index a matrix \(G\) by permutations and set

\[
G_{\pi\sigma}=n^{\#\operatorname{cycles}(\pi^{-1}\sigma)},\qquad
S_{\pi\pi}=\operatorname{sgn}(\pi),\qquad H=SG^{-1}S.
\]

The unitary Weingarten formula gives

\[
\mathbb E[m_\pi\overline{m_\sigma}]=(G^{-1})_{\pi\sigma},
\qquad \mathbb E[q_\pi\overline{q_\sigma}]=H_{\pi\sigma}.
\]

Here the matrix dimension and monomial degree are both \(n\), so all partitions are admissible and the Gram matrix is invertible. The sign vector is a \(G\)-eigenvector with eigenvalue \(n!\); hence \(H\mathbf1=\mathbf1/n!\). Using \(\sum q_\pi=1\) proves \(\mathbb E q_\pi=1/n!\), and therefore \(\mathbb E d=c\).

The eigenvalues of \(G\), from Schur–Weyl duality and the hook-content formula, are

\[
C_\lambda(n)=\prod_{(i,j)\in\lambda}(n+j-i).
\]

The column partition gives \(C_{(1^n)}(n)=n!\). Every other partition satisfies

\[
C_\lambda(n)\ge(n+1)n!.
\]

An independent elementary check of this minimum avoids any ambiguity about dominance order. If \(\lambda\) has \(\ell=n-q\) rows, its first-column product is \(n!/q!\), and there are \(q\ge1\) remaining boxes. The box \((1,2)\) contributes \(n+1\); each of the other \(q-1\) boxes contributes at least \(q+2\). Thus

\[
C_\lambda(n)\ge\frac{n!}{q!}(n+1)(q+2)^{q-1}\ge(n+1)n!.
\]

Equality occurs at \((2,1^{n-2})\). The sign twist sends the exceptional column representation to the constant vectors. Consequently

\[
\boxed{\mathbb E|d-c|^2\le
\frac1{n+1}\frac1{n!}\sum_\pi|z_\pi-c|^2.}
\]

The primary integration input was checked in Collins–Śniady, *Integration with respect to the Haar measure on unitary, orthogonal and symplectic group*, Proposition 2.3 and Corollary 2.4:
`https://arxiv.org/pdf/math-ph/0402073`.
The variance deduction and its use below do not invoke MOC.

## 2. The real covariance extension is valid

A complex scalar variance bound alone would not imply the desired real covariance comparison. The additional required identity does hold:

\[
d(\overline a,\overline b;U)=\overline{d(a,b;U)}.
\]

This follows from the squared-minor determinant expansion, whose coefficients \(|\det U_{I,J}|^2\) are real. In particular, the equality uses the **same** \(U\); it is not merely an equality in distribution.

It follows that for every real-linear functional \(L:\mathbb C\to\mathbb R\),

\[
L(d-c)=\sum_\pi q_\pi L(z_\pi-c).
\]

The right side is real for these vertex data. Apply the same centered kernel bound to the real vector \((L(z_\pi-c))_\pi\). If \(\Sigma\) is the covariance matrix of the uniformly sampled permutation vertex in \(\mathbb R^2\), then

\[
\boxed{\operatorname{Cov}_{\mathbb R^2}(d)\preceq\Sigma/(n+1).}
\]

More precisely, if \(X\) has centered real and imaginary vertex coordinates as its two columns, then

\[
\operatorname{Cov}_{\mathbb R^2}(d)=X^T H X.
\]

Thus any positive-definite quadratic form can be used for an ellipsoidal Markov bound. Whitening requires a nonsingular covariance; a singular case must be treated separately.

## 3. Independent exact arithmetic for the nontrivial example

The example is

\[
a=(-3+3i,\ i,\ 2+2i,\ 1-6i),\qquad
b=(2-3i,\ -2-3i,\ 0,\ 6i).
\]

The spectra are simple and nonconcyclic, and no paired sum is zero. Unlike the team's second covariance example, this pair is not automatically covered by the zero-paired-sum theorem.

I wrote `check_haar_independent.py`, which differs from the originating verifier in two material ways: it solves the rational \(24\times24\) Gram systems directly without a table of Weingarten values, and it enumerates supporting lines directly without a convex-hull routine. It confirms

\[
c=-3+\frac{181}{6}i,
\qquad
C=\begin{pmatrix}
444339/20&-2051/10\\
-2051/10&4591039/180
\end{pmatrix},
\]

\[
\operatorname{Var}(d)=\operatorname{tr}C=\frac{859009}{18},\qquad
r^2=\frac{99633028609}{198900},
\]

where the disk of radius \(r\) around \(c\) is contained in the permutation hull. Therefore

\[
\Pr\{d\in\operatorname{conv}(z_\pi)\}
\ge 1-\frac{\operatorname{Var}(d)}{r^2}
=\frac{4744262061}{5243843611}>0.90.
\]

This numerical fraction uses the **exact Haar variance**, not merely the coarser universal upper bound \(V/(n+1)\). All quantities and comparisons were checked with rational arithmetic. No numerical integration or Monte Carlo variance is used. Results are in `haar_independent_check.json`.

## 4. The explicit full-dimensional neighborhood is certified

Assume that each of the eight complex spectral coordinates is displaced from the example by modulus at most

\[
\delta=10^{-4}.
\]

This is a product of complex disks, not a claim that both real and imaginary parts may independently move by \(10^{-4}\). The latter convention would require a revised radius.

Every original factor satisfies \(|a_i+b_j|\le10\). A telescoping product estimate gives

\[
|z'_\pi-z_\pi|\le\eta:=8\delta(10+2\delta)^3<1.
\]

The vertex centroid moves by at most \(\eta\). Every support function moves by at most \(\eta\), so the new centered inradius satisfies

\[
r'\ge r-2\eta>700-2=698.
\]

This does not assume that the hull's list of facets remains unchanged. The universal kernel bound applies to the difference of the two vertex vectors, even though that difference need not itself be the vertex vector of a single pair of spectra. Thus

\[
\operatorname{Var}(d'-d)\le\eta^2/5,
\qquad
\sqrt{\operatorname{Var}(d')}\le
\sqrt{\operatorname{Var}(d)}+\eta/\sqrt5<219+1=220.
\]

The first inequality concerns centered differences; the second is the triangle inequality in centered \(L^2\). Therefore every pair in the spectral neighborhood has conditional Haar coverage at least

\[
\boxed{p_*:=1-\frac{220^2}{698^2}
=\frac{109701}{121801}>0.90.}
\]

The neighborhood has nonempty interior in \(\mathbb C^8\), so this is a continuous full-dimensional spectral result, unlike the earlier finite-support collision probability. It remains a Haar-probability result, not an all-unitary result.

## 5. Gaussian and arbitrary-noise corollaries

Take independent standard circular complex Gaussians \(g_i,h_j\), normalized by \(\mathbb E|g_i|^2=1\), and set

\[
a'_i=a_i+\sigma g_i,\qquad b'_j=b_j+\sigma h_j,
\qquad \sigma=\delta/4=1/40000.
\]

Let the relative basis be independent Haar, or equivalently conditionally Haar given the spectra. Since \(|g_i|^2\) is exponential of mean one, the probability that all eight coordinates remain in the certified spectral neighborhood is exactly

\[
q=(1-e^{-16})^8.
\]

Hence the joint probability of the MOC inclusion obeys

\[
\Pr(\mathrm{MOC})\ge p_*(1-e^{-16})^8
\ge p_*(1-8e^{-16})>0.90.
\]

Even the coarse bound \(e^{-16}<10^{-6}\) gives the exact rational lower bound

\[
\frac{13712515299}{15225125000}>0.90.
\]

This is a **concentrated noncentral Gaussian eigenvalue model**. It says nothing by itself about centered Gaussian eigenvalues, Ginibre matrix entries, or an arbitrary spectral noise level. The resulting matrices are normal because the random values are used as eigenvalues and the conjugations are unitary.

For any other spectral noise law assigning probability \(q\) to the same certified neighborhood, the joint lower bound is \(q p_*\), provided the relative basis remains conditionally Haar. No independence among the spectral coordinates is required for this last statement once \(q\) is known.

## 6. Additional audit of the explicit probabilistic large-shift argument

The elementary result in Section 4 of `../coverage_independent/haar_coverage_theorems.md` also passes. It uses the condition \(\min_{ij}|U_{ij}|^2\ge m\), which forces the trace-assignment point a distance at least \(nm r_T\) inside its hull. The determinant remainder and shifted vertex remainder are both bounded by

\[
E(s)=\sum_{k=3}^n\binom nk M^k/|s|^{k-2}.
\]

The sufficient condition \(2E(s)\le nm r_T\) is correct, including its factor two. The Haar entry union bound is at most \(n^2(n-1)m\). Setting \(m=\varepsilon/[n^2(n-1)]\) therefore gives coverage at least \(1-\varepsilon\) when

\[
|s|\ge\max\left\{2nM,
\frac{4n(n-1)\binom n3M^3}{\varepsilon r_T}\right\}.
\]

The estimate is uniform in the argument of \(s\). It requires a planar trace-assignment hull with positive centered inradius \(r_T\); it makes no finite all-unitary claim. The separate extension to collinear spectra uses an established essentially-Hermitian result and should remain identified as such.

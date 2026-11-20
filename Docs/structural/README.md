# MOC: structural probability bounds and valued-field results

These results have complete mathematical proofs and independent exact-arithmetic checks where indicated. They do not prove the unrestricted complex Marcus–de Oliveira conjecture. No claim of publication novelty is made.

The meaning of “half” is specified in each result. A probability over Haar relative eigenbases is different from a class of spectra for which every unitary works. A finite spectral law is different from a continuous spectral law. The non-Archimedean result uses a different transformation group and a different enclosure.

## Reading guide

- [Haar coverage](proofs/haar_coverage_theorems.md) and the [exact 90% class](proofs/exact_90_percent_class.md) give the continuous probability bounds summarized below. The [Haar audit](proofs/independent_haar_audit.md) checks the moment and geometry arguments.
- [Discrete coverage and information](proofs/discrete_coverage_and_information.md) uses the [order-four zero-paired-sum theorem](proofs/zero_paired_sum_n4.md).
- [Large shifts for every unitary](proofs/large_shift_all_U.md) and [large-shift distributions](proofs/large_shift_distributions.md) treat a separate spectral regime.
- [The non-Archimedean exact range](proofs/nonarchimedean_exact_range.md) has a separate [independent audit](proofs/independent_nonarchimedean_audit.md).

[Exact checkers and ensemble experiments](../../code/structural/) accompany the proofs. See the [reproduction guide](../reproduction.md) for execution conventions.

## 1. An all-dimensional RMT criterion

For fixed complex spectra, let

\[
d(U)=\det(A+UBU^*),\quad z_\pi=\prod_i(a_i+b_{\pi(i)}),\quad
K=\operatorname{conv}\{z_\pi\},\quad c=\frac1{n!}\sum_\pi z_\pi.
\]

If \(U\) is complex Haar distributed, then

\[
\mathbb E d=c,\qquad
\boxed{\mathbb E|d-c|^2\le\frac1{n+1}\frac1{n!}\sum_\pi|z_\pi-c|^2.}
\]

This holds for **every pair of complex spectra**. No MOC assumption is used. The factor is sharp in general. The proof uses the exact identity

\[
d(U)\det U=\det(AU+UB)
=\sum_\pi\operatorname{sgn}(\pi)z_\pi\prod_iU_{i,\pi(i)},
\]

and the spectrum of the Haar Weingarten matrix. After removing the mean, the largest remaining eigenvalue is \(1/((n+1)n!)\). Collins–Śniady's integration formula is the established input; the probability deductions are written out in the accompanying proof.

More strongly, identify the complex plane with \(\mathbb R^2\), and let \(\Sigma\) be the covariance of the uniformly labeled permutation values. Then

\[
\operatorname{Cov}_{\mathbb R^2}(d)\preceq\frac{\Sigma}{n+1}.
\]

When \(\Sigma\) is positive definite, let \(\rho\) be the centered inradius of \(\Sigma^{-1/2}(K-c)\). Applying Markov's inequality to squared distance gives

\[
\boxed{\Pr_U(d\in K)\ge\max\left\{0,1-\frac{2}{(n+1)\rho^2}\right\}.}
\]

Thus the explicit spectral class \(\rho^2\ge4/(n+1)\) has **at least half Haar coverage**. Any spectral distribution supported on this class has the same joint guarantee if the conditional relative eigenbasis is Haar. The criterion is unchanged by any invertible real affine change of determinant-plane coordinates. For rational complex spectra, its facet test can be checked by rational arithmetic without taking a matrix square root.

It also gives a conditional asymptotic statement: for a sequence of spectral pairs with \(\rho_n\) uniformly bounded below by a positive constant, Haar inclusion probability tends to one as \(n\to\infty\). This does not by itself establish that condition for a particular unconditioned Gaussian or Ginibre spectral model.

Full proof: [haar_coverage_theorems.md](proofs/haar_coverage_theorems.md).

## 2. A fully complex example and a continuous Gaussian class above 90%

Take

\[
a=(-3+3i,i,2+2i,1-6i),\qquad
b=(2-3i,-2-3i,0,6i).
\]

Both spectra are distinct, have trace zero, and are neither collinear nor concyclic. None of the 16 pair sums is zero. Exact Haar integration and exact integer convex geometry give

\[
c=-3+\frac{181}{6}i,\qquad
v=\mathbb E|d-c|^2=\frac{859009}{18},\qquad
r^2=\frac{99633028609}{198900},
\]

where the disk centered at \(c\) of radius \(r\) is inside \(K\). Therefore

\[
\boxed{\Pr_U(d\in K)\ge1-v/r^2
=\frac{4744262061}{5243843611}\approx90.472989\%.}
\]

This exact variance is stronger than the universal variance bound for this example. No sampled variance is used in the guarantee.

Every pair with \(\max_i|a'_i-a_i|\le10^{-4}\) and \(\max_j|b'_j-b_j|\le10^{-4}\) has the uniform lower bound

\[
\Pr_U(d'\in K')\ge\frac{109701}{121801}>90\%.
\]

The proof controls every permutation vertex displacement by less than one, the perturbed centered inradius by more than 698, and the determinant standard deviation by less than 220. This is an explicit full-dimensional spectral neighborhood, not an equality constraint on the eigenvalues.

For a continuous distributional example, take independent standard circular complex Gaussians \(g_i,h_j\), normalized by \(\mathbb E|g_i|^2=1\), and set

\[
a'_i=a_i+g_i/40000,\qquad b'_j=b_j+h_j/40000.
\]

With independent Haar \(U\), the joint inclusion probability is at least

\[
\frac{109701}{121801}(1-e^{-16})^8>90\%.
\]

This is a **noncentral, concentrated Gaussian eigenvalue ensemble**. It is not a theorem giving 90% coverage for centered Gaussian spectra or iid Gaussian matrix entries. Arbitrary bounded eigenvalue noise in the displayed neighborhood has the uniform guarantee above; more generally, neighborhood mass \(q\) gives a lower bound \(q\,109701/121801\).

Full proof: [exact_90_percent_class.md](proofs/exact_90_percent_class.md). Two independent rational checkers verify the moments and polygon geometry.

## 3. Discrete spectral laws: all-unitary coverage

For normal 4-by-4 matrices, MOC holds for **every unitary** whenever the eight numbers

\[
a_1,a_2,a_3,a_4,-b_1,-b_2,-b_3,-b_4
\]

have a repeated value. A repetition within a spectrum is the rank-two case after a scalar shift; a cross-spectrum repetition is the zero-paired-sum case. The accompanying proof constructs the required nonnegative laws explicitly by max-flow and Birkhoff decompositions, respectively.

If those eight values are iid uniform on an \(m\)-point set, the sufficient event has exact probability

\[
\boxed{1-\frac{(m)_8}{m^8}.}
\]

| Symmetric complex spectral support | Proved lower bound on inclusion probability |
|---|---:|
| \(\{x+iy:x,y\in\{-3,-1,1,3\}\}\), 16 points | \(14750191/16777216\), **87.917989%** |
| \(\{x+iy:x,y\in\{-2,-1,0,1,2\}\}\), 25 points | \(871830293/1220703125\), **71.420338%** |
| Any symmetric support of size at most 42 | **At least 50%** |

The law of \(U\) can be arbitrary, even dependent on the spectra. The formula counts a sufficient event; the remaining samples are not asserted to fail MOC. For nonsymmetric support, the \(b_j\) are sampled from the reflected law, so that \(a_i,-b_j\) have the same distribution.

For a nonuniform mirrored law \(p\), the exact sufficient-event probability is \(1-8!e_8(p)\), and the uniform law is the worst case at a fixed support size. An information-theoretic bound follows by counting equal pairs. With \(S_2=\sum p_j^2\) and \(S_3=\sum p_j^3\),

\[
\Pr(\text{covered})\ge
\frac{(28S_2)^2}{28S_2+336S_3+420S_2^2}.
\]

This connects the result to Rényi collision entropies. The collision proof has zero coverage for independent continuous spectral laws; it is not a continuous-volume argument.

Full proof: [discrete_coverage_and_information.md](proofs/discrete_coverage_and_information.md).

## 4. A complete non-Archimedean analogue

Let \(F\) be any non-Archimedean valued field, \(\mathcal O\) its valuation ring, and \(A,B\) diagonal over \(F\). For any permutation vertex \(z_0\),

\[
\boxed{\{\det(A+UBU^{-1}):U\in GL_n(\mathcal O)\}
=\{x\in F:|x-z_0|\le\max_\pi|z_\pi-z_0|\}.}
\]

The same is true with \(SL_n(\mathcal O)\). No completeness assumption is needed. The determinant range is exactly the smallest ultrametric closed ball containing all pairing vertices.

Containment follows because the signed Leibniz coefficients are in \(\mathcal O\) and sum to one. For equality, some transposition edge of the permutation graph attains the vertex diameter. Embedding \(G(t)=\left(\begin{smallmatrix}1&1\\t&1+t\end{smallmatrix}\right)\), \(t\in\mathcal O\), along that edge produces \((1+t)z_\alpha-tz_\beta\), filling the entire ball.

This solves a specified valued-field analogue, with integral similarities and ultrametric balls. It does not prove complex MOC, and it is not a statement about an unspecified p-adic adjoint or unitary group. With the trivial absolute value on a finite field, the same theorem says the range is a singleton when all vertices agree, and the entire field otherwise.

Full proof: [nonarchimedean_exact_range.md](proofs/nonarchimedean_exact_range.md).


## Sources and status

- Collins and Śniady, *Integration with respect to the Haar measure on unitary, orthogonal and symplectic group*, Commun. Math. Phys. 264 (2006), 773–795; Proposition 2.3 and Corollary 2.4: https://arxiv.org/pdf/math-ph/0402073 .
- Drury, *Essentially Hermitian matrices revisited*, Electronic Journal of Linear Algebra 15 (2006), 285–296: https://journals.uwyo.edu/index.php/ela/article/download/403/403/403 . Used only for the established collinear-spectra extension in the large-shift note.
- Independent review notes are included under `proofs/`. These are mathematical audits, not proof-assistant formalizations or a completed literature-priority review.


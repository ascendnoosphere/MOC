# An exact Haar-probability certificate and an open spectral class

This establishes a probability bound for the Marcus-de Oliveira inclusion.
It does not establish that inclusion for every unitary in the featured class.
No novelty claim is made.

## Featured theorem

Let

\[
a=(-3+3i,\ i,\ 2+2i,\ 1-6i),\qquad
b=(2-3i,\ -2-3i,\ 0,\ 6i),
\]

and let \(U\) have Haar probability distribution on \(U(4)\). Put

\[
d(U)=\det(\operatorname{diag}(a)+U\operatorname{diag}(b)U^*),\quad
z_\pi=\prod_{j=1}^4(a_{\pi(j)}+b_j),\quad
P=\operatorname{conv}\{z_\pi:\pi\in S_4\}.
\]

Then

\[
\boxed{\Pr\{d(U)\in P\}\ge
\frac{4744262061}{5243843611}>0.9047.}
\]

Both spectra have distinct entries and sum to zero. Neither lies on a circle
or line: the determinants with rows \((\Re z,\Im z,|z|^2,1)\) are respectively
\(-640\) and \(744\). Every sum \(a_i+b_j\) is nonzero.

## Exact moment calculation

Write \(m_\pi(U)=\prod_jU_{\pi(j),j}\). The elementary identity

\[
d(U)\det U=\det(\operatorname{diag}(a)U+U\operatorname{diag}(b))
=\sum_\pi\operatorname{sgn}(\pi)z_\pi m_\pi(U)
\]

reduces the second moment to degree-four Haar entry moments. For permutations
\(\pi,\sigma\), these are

\[
\mathbb E[m_\pi\overline{m_\sigma}]
=\mathrm{Wg}_4(\pi^{-1}\sigma).
\]

This is the unitary Weingarten integration formula. A primary reference is
Collins and Śniady, *Integration with respect to the Haar measure on unitary,
orthogonal and symplectic group*, Commun. Math. Phys. 264 (2006), 773–795,
Corollary 2.4, equation (11), with the inverse formula in Proposition 2.3:
https://arxiv.org/pdf/math-ph/0402073 .

Here the Weingarten matrix is the inverse of the 24 by 24 Gram matrix
\(G_{\pi\sigma}=4^{\#\mathrm{cycles}(\pi^{-1}\sigma)}\). Its five values are:

| Cycle type | \(\mathrm{Wg}_4\) |
|---|---:|
| \(1^4\) | \(67/10080\) |
| \(2,1,1\) | \(-1/420\) |
| \(2,2\) | \(11/10080\) |
| \(3,1\) | \(29/20160\) |
| \(4\) | \(-1/1008\) |

Define

\[
H_{\pi\sigma}=\operatorname{sgn}(\pi^{-1}\sigma)
\mathrm{Wg}_4(\pi^{-1}\sigma).
\]

The mean is exactly the vertex barycenter
\(c=24^{-1}\sum_\pi z_\pi\). This follows independently by averaging the
squared-minor expansion: each order-\(k\) squared minor has Haar mean
\(\binom4k^{-1}\), exactly the proportion of permutations taking one fixed
\(k\)-set to another. Hence

\[
\mathbb E|d-c|^2=(z-c\mathbf1)^*H(z-c\mathbf1).
\]

Exact rational evaluation gives

\[
c=-3+\frac{181}{6}i,\qquad
\mathbb E|d|^2=\frac{194567}{4},\qquad
v:=\mathbb E|d-c|^2=\frac{859009}{18}.
\]

## Exact convex geometry

The vertices of the convex hull, in counterclockwise order, are

\[
(-875,70),\ (-420,-840),\ (432,-576),\ (936,72),\
(312,840),\ (-462,1008),
\]

where pairs denote real and imaginary coordinates. The squared radius of the
largest disk centered at \(c\) contained in this polygon is

\[
r^2=\frac{99633028609}{198900}.
\]

For example, its minimizing edge joins \((-420,-840)\) to \((432,-576)\).
The edge vector is \((852,264)\), and its cross product with the vector from
the first endpoint to \(c\) is \(631294\). Its squared distance is therefore
\(631294^2/(852^2+264^2)=r^2\). The other five edges have larger distances;
the exact checker verifies every edge and every candidate vertex.

Since the disk is contained in the polygon, the event \(d\notin P\) implies
\(|d-c|>r\). Markov's inequality applied to \(|d-c|^2\) gives

\[
\Pr\{d\in P\}\ge1-\frac{v}{r^2}
=1-\frac{499581550}{5243843611}
=\frac{4744262061}{5243843611}.
\]

## A quantitative open spectral neighborhood

The same argument gives a uniform bound greater than 90 percent for every
pair of spectra \(a',b'\) satisfying

\[
\max_i|a'_i-a_i|\le10^{-4},\qquad
\max_j|b'_j-b_j|\le10^{-4}.
\]

The probability is over Haar \(U\), conditional on the chosen spectra.

First, all original pair sums have modulus at most 10. Product telescoping
therefore bounds every vertex displacement by

\[
\eta=8\delta(10+2\delta)^3<1,\qquad \delta=10^{-4}.
\]

The barycenter moves by at most \(\eta\). Support functions of the centered
convex hull consequently move by at most \(2\eta\). Since the original
inradius exceeds 700, the perturbed inradius exceeds 698.

For completeness, the same exact 24 by 24 kernel satisfies

\[
H\preceq \frac1{120}I+\frac1{720}J,
\]

where \(J\) is the all-ones matrix. This can be checked from the five
eigenvalues \(1/24,1/120,1/240,1/360,1/840\), with multiplicities
\(1,9,4,9,1\), or by the accompanying exact rational PSD elimination.
For a centered vector \(w\), this implies
\(w^*Hw\le\|w\|^2/120\).

Apply this to the centered vertex displacement. Its mean squared modulus is
at most \(\eta^2\), so the standard deviation of the centered determinant
increment is at most \(\eta/\sqrt5<1\). The triangle inequality in \(L^2\)
then shows that the perturbed determinant has standard deviation less than
220, since the original one is less than 219. Thus, uniformly throughout
the spectral neighborhood,

\[
\boxed{\Pr\{d'(U)\in\operatorname{conv}\{z'_\pi\}\}
\ge1-\frac{220^2}{698^2}
=\frac{109701}{121801}>0.9.}
\]

## A continuous noncentral Gaussian eigenvalue ensemble

Let \(g_1,\ldots,g_4,h_1,\ldots,h_4\) be independent standard circular
complex Gaussians: their real and imaginary parts are independent
\(N(0,1/2)\), so \(\mathbb E|g_j|^2=1\). Set

\[
a'_j=a_j+\sigma g_j,\qquad b'_j=b_j+\sigma h_j,
\qquad \sigma=1/40000,
\]

and take \(U\) independently Haar distributed. All eight eigenvalue
perturbations lie in the preceding spectral neighborhood with probability
\((1-e^{-16})^8\). Therefore

\[
\boxed{\Pr\{d'(U)\in\operatorname{conv}\{z'_\pi\}\}
\ge\frac{109701}{121801}(1-e^{-16})^8>0.9.}
\]

This is a noncentral Gaussian **eigenvalue** ensemble concentrated near the
displayed spectra. It is not a model of centered Gaussian matrix entries.
More generally, any spectral law placing probability \(q\) in the explicit
neighborhood gives a lower bound \(q\,109701/121801\), provided the
conditional distribution of \(U\) remains Haar.

## Reproducibility and limits

Run `python verify_haar_certificates.py`. It uses only Python's standard
library and exact `Fraction` arithmetic to verify the Gram inverse, PSD
bound, all pairing vertices, polygon facets, moment values, probability
fractions, and neighborhood estimates. It writes
`haar_certificates_verified.json`.

Random integer spectra were used to discover this example. Neither its Haar
variance nor its probability guarantee uses Monte Carlo estimates. The
probability bound does not assert that the remaining fraction contains any
counterexamples; the actual inclusion probability could still be one.

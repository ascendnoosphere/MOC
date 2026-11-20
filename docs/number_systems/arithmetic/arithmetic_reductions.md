# Arithmetic restrictions that retain the full determinantal conjecture

These are reductions, not a proof of the Marcus–de Oliveira conjecture (MOC).
Every equivalence below holds in each fixed dimension \(n\). Distinguishing
matrix **entries** from matrix **eigenvalues** is essential.

For \(a,b\in\mathbb C^n\) and \(U\in U(n)\), write

\[
 d(a,b,U)=\det(\operatorname{diag}(a)+U\operatorname{diag}(b)U^*),
 \qquad
 z_\pi(a,b)=\prod_i(a_i+b_{\pi(i)}).
\]

Write \(\mathsf{M}(a,b,U)\) for the assertion
\(d(a,b,U)\in\operatorname{conv}\{z_\pi(a,b):\pi\in S_n\}\).

## 1. Two elementary invariances and a closure property

For \(c\ne0\) and \(x\in\mathbb C\), put

\[
 a'_i=ca_i+x,\qquad b'_j=cb_j-x.
\]

Then, with the same unitary \(U\),

\[
 d(a',b',U)=c^n d(a,b,U),\qquad
 z_\pi(a',b')=c^n z_\pi(a,b).
 \tag{1}
\]

Multiplication by a nonzero complex number commutes with taking real convex
hulls. Thus \(\mathsf M(a',b',U)\) and \(\mathsf M(a,b,U)\) are equivalent.
The two scalar translations in (1) have opposite signs. Arbitrarily shifting
just one matrix is not an invariance asserted here.

The set of triples satisfying \(\mathsf M\) is closed. Indeed, if
\((a^{(k)},b^{(k)},U_k)\to(a,b,U)\) and each triple satisfies MOC, select
weights \(p_\pi^{(k)}\ge0\), \(\sum_\pi p_\pi^{(k)}=1\), realizing its
inclusion. The finite-dimensional probability simplex is compact. Along a
subsequence the weights converge to \(p_\pi\); continuity of the determinant
and of each vertex then gives

\[
 d(a,b,U)=\sum_\pi p_\pi z_\pi(a,b).
 \tag{2}
\]

This uses weights only for the approximating triples for which MOC has been
assumed. It does not assume MOC for the target triple.

## 2. Rational, integer, and primitive Gaussian spectra

Let \(\mathbb Q(i)=\{r+is:r,s\in\mathbb Q\}\). Full MOC is equivalent to each
of the following restrictions:

1. \(a_i,b_j\in\mathbb Q(i)\), with arbitrary \(U\).
2. \(a_i,b_j\in\mathbb Z[i]\), with arbitrary \(U\).
3. \(a_i,b_j\in\mathbb Z[i]\), with arbitrary \(U\), and the ideal generated
   by all \(2n\) spectral entries is the whole ring \(\mathbb Z[i]\).

For the first equivalence, approximate arbitrary \(a,b\) by Gaussian-rational
vectors, retaining the same \(U\), and apply (2). For the second, multiply
all rational spectral entries by one positive integer clearing their
denominators, use the integer assertion, and undo the scaling by (1).

For the third, \(\mathbb Z[i]\) is a principal ideal domain. Any nonzero
integer spectral tuple has a greatest common divisor \(g\ne0\); dividing
every \(a_i,b_j\) by \(g\) gives a primitive tuple. Equation (1) restores the
original assertion after multiplying by \(g\). The all-zero tuple satisfies
MOC directly. This is a **global** gcd condition, not pairwise coprimality.

Therefore proving the conjecture for primitive Gaussian-integer spectral
tuples would already prove the entire conjecture.

## 3. Exact Gaussian-rational unitaries are dense

Let

\[
 U_{\mathbb Q(i)}(n)=U(n)\cap M_n(\mathbb Q(i)).
\]

This countable set is dense in \(U(n)\). Here is a construction preserving
unitarity exactly, unlike rounding a unitary matrix entry by entry.

For a Hermitian matrix \(H\), its Cayley transform

\[
 C(H)=(I+iH)(I-iH)^{-1}
 \tag{3}
\]

is unitary. The inverse exists because \(H\) has real eigenvalues. If \(H\)
has Gaussian-rational entries, (3) has Gaussian-rational entries as well.

Every unitary \(V\) without eigenvalue \(-1\) has the form (3), with

\[
 H=-i(V-I)(V+I)^{-1},
 \tag{4}
\]

which is Hermitian. Approximate the real diagonal entries and the complex
upper-triangular entries of \(H\) by rational coordinates, and impose
Hermitian symmetry on the lower triangle. Continuity of (3) supplies
Gaussian-rational unitaries tending to \(V\).

Finally, unitaries without eigenvalue \(-1\) are dense in \(U(n)\): for a
given \(V\), the matrices \(e^{it}V\) avoid that eigenvalue for all sufficiently
small \(t\) except finitely many prohibited phases. A diagonal approximation
argument completes the density proof.

Consequently full MOC is equivalent even to the countable restriction

\[
 a_i,b_j\in\mathbb Z[i],
 \qquad U\in U_{\mathbb Q(i)}(n).
 \tag{5}
\]

To see this, first pass from integer to rational spectra by common scaling;
then approximate both arbitrary spectra and the relative unitary and apply
closedness. One may impose the global primitive condition in (5) as well.

## 4. Gaussian-rational or Gaussian-integer matrix entries

Full MOC is also equivalent to its restriction to pairs of normal matrices
whose **entries** lie in \(\mathbb Q(i)\), or to pairs whose entries lie in
\(\mathbb Z[i]\).

The density argument must preserve normality. Given a normal matrix
\(N=V\operatorname{diag}(\lambda)V^*\), choose

\[
 V_k\in U_{\mathbb Q(i)}(n),\qquad
 \lambda^{(k)}\in\mathbb Q(i)^n,\qquad
 V_k\to V,\quad\lambda^{(k)}\to\lambda.
\]

Then

\[
 N_k=V_k\operatorname{diag}(\lambda^{(k)})V_k^*
\]

is exactly normal, has Gaussian-rational entries, has the prescribed
Gaussian-rational spectrum \(\lambda^{(k)}\), and converges to \(N\).
Construct such approximations for both matrices. Their determinant
inclusions pass to the limit by (2), with the displayed spectral labels.

For Gaussian-rational matrix pairs, one positive integer clears all entry
denominators of both matrices. Common multiplication preserves normality
and scales every determinant and permutation vertex by that integer to
the power \(n\). Therefore an integer-entry theorem implies the
rational-entry theorem and hence full MOC.

One can impose both Gaussian-integer entries and Gaussian-integer spectra
simultaneously: the approximating matrices above have rational entries
and rational spectra; clear all those denominators at once.

Arbitrary entrywise rational approximation is not enough for this argument:
it need not preserve normality. The rational-unitary construction is the
necessary step.

## 5. Even Gaussian-prime eigenvalues retain the entire problem

The required number-theoretic input is a proved theorem of Terence Tao:
every finite set \(F\subset\mathbb Z[i]\) has a translate-dilate
\(x+rF\) consisting entirely of Gaussian primes, with
\(x\in\mathbb Z[i]\) and \(r\in\mathbb Z\setminus\{0\}\).
See [Tao, Theorem 1.2](https://arxiv.org/pdf/math/0501314), pages 1–2.

**Theorem.** Full MOC is equivalent to MOC restricted to pairs whose
eigenvalues are all Gaussian primes. The relative unitary may also be
restricted to \(U_{\mathbb Q(i)}(n)\).

**Proof.** Start with any Gaussian-integer spectra \(a,b\), and take the
finite set of distinct values

\[
 F=\{a_1,\ldots,a_n,-b_1,\ldots,-b_n\}.
\]

Choose \(x,r\) by Tao's theorem and put

\[
 a'_i=x+ra_i,\qquad b'_j=rb_j-x.
 \tag{6}
\]

The \(a'_i\) are Gaussian primes. So are the \(b'_j\), because their
negatives belong to \(x+rF\), and multiplication by the unit \(-1\)
preserves Gaussian primality. Equation (1) gives an exact equivalence
between the primed and original determinant inclusions, with unchanged
\(U\). Sections 2–3 finish the reduction. \(\square\)

No conjecture about twin Gaussian primes is used. The dilation \(r\) is
allowed to vary; Tao's theorem does not assert prime patterns with a
prescribed fixed gap. Repeated spectral values are allowed, as in MOC.

This is a reduction for **eigenvalues**. Applying a translation to all
matrix entries adds \(xJ\), where \(J\) is the all-ones matrix, rather than
\(xI\). Such a translation can destroy normality. No corresponding
equivalence for matrices with all entries Gaussian prime is claimed.

## 6. Real primes and other real arithmetic sequences

If both normal matrices have real eigenvalues, they are Hermitian, and
Fiedler's established theorem applies. Consequently restricting the
eigenvalues to ordinary primes, members of twin-prime pairs, superabundant
integers, or any other subset of \(\mathbb R\) does not introduce a new
case. This does not depend on whether a proposed real sequence is known
to be infinite.

A normal matrix with spectrum on an affine complex line is essentially
Hermitian: \(N=\beta I+\alpha H\) with \(H=H^*\).
The established line/circle results cover pairs of this type.
For primary statements see
[Drury (2006), Theorem 1.2 and the introductory discussion](https://journals.uwyo.edu/index.php/ela/article/download/403/403/403);
the general line/circle class is also recorded explicitly in
[Shitov (2025), Section 1](https://www.mathnet.ru/eng/im9292).
A non-real affine offset should not silently be removed by a purported
invariance that shifts both matrices in the same direction.

Real **entries** do not force a normal matrix to be Hermitian. For example,

\[
 N=\begin{pmatrix}
 2&3&5\\
 5&2&3\\
 3&5&2
 \end{pmatrix}
\]

has positive prime entries and satisfies

\[
 NN^T=N^TN=
 \begin{pmatrix}
 38&31&31\\
 31&38&31\\
 31&31&38
 \end{pmatrix},
\]

but \(N\ne N^T\). Its eigenvalues are \(10,-2+i\sqrt3,-2-i\sqrt3\).
Thus it is normal and non-Hermitian. Two real symmetric prime-entry
matrices are covered by the Hermitian theorem. Two circulants of the
same size commute and are simultaneously unitarily diagonalizable, so
their determinant is itself a permutation vertex. Neither observation
settles arbitrary normal matrices with prime entries.

## 7. Bases and value fields

Changing the numeral base while retaining the same numerical values
does not change the matrices or the determinant question.

If the intended restriction is a field of allowable spectral values,
the relevant property is density:

- Any allowed spectral set containing \(\mathbb Q(i)\) retains full MOC
  by Section 2. In particular this applies to \(\mathbb Q(\beta,i)\)
  for any fixed complex \(\beta\), algebraic or transcendental.
- If \(\beta\notin\mathbb R\), already
  \(\mathbb Q+\beta\mathbb Q\subset\mathbb Q(\beta)\) is dense in
  \(\mathbb C\). Thus arbitrary eigenvalues in \(\mathbb Q(\beta)\),
  with arbitrary unitary relative basis, also retain full MOC.
- If the allowed spectral values are all real, the Hermitian theorem
  applies, regardless of whether their expansions use an irrational
  or transcendental base.

Finite digit strings with a prescribed unusual digit set may define a
different, sparse value set. No claim about such a set follows without
its precise definition. These statements concern eigenvalues; matrix
entry restrictions need a separate normality-preserving argument.

## 8. Consequence for exact counterexample searches

If full MOC is false in dimension \(n\), it has a counterexample with
Gaussian-integer spectra and an exactly Gaussian-rational unitary.
Indeed, separation from a finite convex hull is strict and persists
under small perturbations; use the dense rational parametrization and
then clear denominators. Dividing by the global gcd gives a primitive
spectral tuple. Applying (6) gives a counterexample with all spectral
values Gaussian prime and the same rational unitary.

For rational data, both the determinant and every vertex lie in
\(\mathbb Q(i)\). A strictly separating complex normal can also be
chosen in \(\mathbb Q(i)\), by density. Its finitely many strict
supporting inequalities are therefore exactly checkable rational
inequalities. This explains why exact arithmetic searches are
meaningful. A finite search returning no counterexample proves
neither the rational restriction nor full MOC.

## 9. Real-closed fields and infinitesimal extensions

Let \(R\) be a real-closed ordered field and let \(R(i)=R[X]/(X^2+1)\),
with conjugation \(x+iy\mapsto x-iy\). Define the convex hull of finitely
many points using coefficients \(p_\pi\in R\) satisfying
\(p_\pi\geq0\) and \(\sum p_\pi=1\).

**Transfer reduction.** For every fixed positive integer \(n\), MOC over
\(R(i)\), with this ordered-field meaning of convexity, has exactly the
same truth value as ordinary complex MOC in dimension \(n\).

To prove this, represent each complex spectral coordinate and unitary
entry by two \(R\)-coordinates. The assertion is the following single
first-order sentence in the language of ordered fields:

\[
\begin{split}
\forall a_{\mathrm R},a_{\mathrm I},b_{\mathrm R},b_{\mathrm I},
             U_{\mathrm R},U_{\mathrm I}\quad
 \bigl[\,U^*U=I\ \Longrightarrow\
 \exists(p_\pi)_{\pi\in S_n}\quad&
 \bigwedge_\pi p_\pi\geq0,\quad \sum_\pi p_\pi=1,\\
 &\operatorname{Re}d=\sum_\pi p_\pi\operatorname{Re}z_\pi,\quad
 \operatorname{Im}d=\sum_\pi p_\pi\operatorname{Im}z_\pi
 \,\bigr].
\end{split}
\tag{7}
\]

Here every complex equality stands for its real and imaginary parts;
conjugation is a sign change. Matrix multiplication and the determinant
are finite polynomials. Thus (7) uses only finitely many polynomial
equations and inequalities with integer coefficients.

Tarski's completeness theorem for real-closed fields says that such a
sentence has the same truth value in every real-closed ordered field.
Applying it to (7) proves the reduction. If one uses the version
quantifying over arbitrary normal matrices, their unitary
diagonalizability in fixed dimension is itself a first-order statement
that transfers from \(\mathbb R\); hence the two versions agree.

This applies to the real algebraic numbers and to any real-closed
non-Archimedean extension, including real closures with an ordered
infinitesimal and real-closed Puiseux or Hahn fields. It does not assert
a corresponding fact for the \(p\)-adic fields, which are not ordered
real-closed fields.

The transfer statement operates separately in each fixed dimension.
The assertion for all dimensions is a family of sentences, not the
single sentence (7). Fixed-dimensional quantifier elimination therefore
does not by itself give an algorithm that decides full MOC in all
dimensions at once.

The model-theoretic input is Tarski's theorem, not an assumption of MOC.
The original source is *A Decision Method for Elementary Algebra and
Geometry* (1951). An explicit formulation of transfer to real-closed
extensions of \(\mathbb R\) appears in the primary research paper
[Erickson (1999), Section 2.3](https://jeffe.cs.illinois.edu/pubs/pdf/linsat.pdf),
printed page 8.

## Source record

- Terence Tao, *The Gaussian primes contain arbitrarily shaped
  constellations*, arXiv:math/0501314v4, abstract and Theorem 1.2.
  Primary PDF: <https://arxiv.org/pdf/math/0501314>.
- S. W. Drury, *Essentially Hermitian matrices revisited*, Electronic
  Journal of Linear Algebra 15 (2006), 285–296.
  Primary PDF: <https://journals.uwyo.edu/index.php/ela/article/download/403/403/403>.
- Y. N. Shitov, *A further sufficient condition for the determinantal
  conjecture*, Izvestiya: Mathematics 89:4 (2025), 862–869.
  Full publisher text: <https://www.mathnet.ru/eng/im9292>.
- Alfred Tarski, *A Decision Method for Elementary Algebra and Geometry*,
  second revised edition, University of California Press (1951).
  Publisher record: <https://doi.org/10.1525/9780520348097>.
- Jeff Erickson, *Lower Bounds for Linear Satisfiability Problems*,
  Chicago Journal of Theoretical Computer Science, 1999, Article 8,
  Section 2.3. Author-hosted primary paper:
  <https://jeffe.cs.illinois.edu/pubs/pdf/linsat.pdf>.

The elementary density and invariance arguments above are supplied in full.
No priority claim is made for the reductions.

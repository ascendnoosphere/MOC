# Transport between crossed squared-minor arrays

This is stronger than the comparison of the two determinant terms in the
two-imaginary-outlier example. It gives a coupling before inserting any
spectral values.

## Statement

Let `U` be unitary and mark a row and a column (independently). Write its
blocks in the form

$$
U=\begin{pmatrix}z&s x^*\\ s y&Z\end{pmatrix},
\qquad s=(1-|z|^2)^{1/2}.
$$

When s is nonzero, x and y are unit vectors in the unmarked column and row
spaces respectively. For each degree r, the following two arrays, indexed
by unmarked subsets of the indicated sizes, are finite measures:

* Source: $A_{I,J}=|\det U[\{d_R\}\cup I,J]|^2$, where
  $|I|=r-1$, $|J|=r$.
* Target: $B_{K,L}=|\det U[K,\{d_C\}\cup L]|^2$, where
  $|K|=r$, $|L|=r-1$.

There is a nonnegative transport from A to B supported on
$I\subset K$ and $L\subset J$. This implies every corresponding
weighted Hall inequality, not just equality of the total masses.
If s=0, A and B are both zero.

## Proof

The two unitary equations give $Zx=-\bar z y$ and
$y^*Z=-\bar z x^*$. Thus $W=Z+\bar z yx^*$ kills x and has image
orthogonal to y. For $|I|=|L|=r-1$ put $w_{I,L}=\det W[I,L]$.
With a consistently ordered coordinate basis, put this array in the
exterior coefficient spaces by extending it by zero to other degrees.

For each fixed I, form the exterior product of the coordinate rows of W
indexed by I, treating each row as an ordinary coordinate vector (without
complex conjugation). Its coefficients are $w_{I,L}$; each factor is
orthogonal to $\bar x$ because $Wx=0$. Prepending $\bar x$ gives the
coefficients of $U[\{d_R\}\cup I,J]/s$ at the determinant level: one
adds multiples of the first row to the subsequent rows and uses
multilinearity. Ordering the marked row first affects only signs.
Similarly, for each fixed L the coordinate columns of W indexed by L
give the same coefficients $w_{I,L}$. Each factor is orthogonal to y;
prepending y gives the determinants of $U[K,\{d_C\}\cup L]/s$
by the column version of the same argument.

Deletion of an orthogonal unit exterior factor sends the extended
coefficient vector to the original vector and preserves its total squared
mass. Its shadow inequality gives an inclusion-supported transport by
weighted Hall. Use it backward to transport $(I,J)$ to $(I,L)$ and
forward to transport $(I,L)$ to $(K,L)$. The intermediate squared mass
is $|w_{I,L}|^2$ in both computations, so the two conditional transports
glue. Multiply by $s^2$. This is a two-sided application of the shadow
argument, not a single law on permutation labels. For the projection
shadow method see R. Lyons, *Determinantal probability measures*,
[DOI 10.1007/s10240-003-0016-0](https://doi.org/10.1007/s10240-003-0016-0),
[arXiv:math/0204325](https://arxiv.org/abs/math/0204325).

## Determinant consequence

In the two-imaginary-outlier setting, let the real unmarked spectra be
positive x_i and y_j, and let u and v be the outlier heights. In the
squared-minor expansion, the real coefficient of source $(I,J)$ is
$(\prod_{i\notin I\cup\{d_R\}} x_i)(\prod_{j\in J}y_j)$; that of
target $(K,L)$ is
$-uv(\prod_{i\notin K,d_R}x_i)(\prod_{j\in L}y_j)$. The other two
membership patterns give purely imaginary terms. On the transport edge
$K=I\cup\{i\}$, $J=L\cup\{j\}$ the positive coefficient is exactly
$x_i y_j$ times the nonnegative product in the target term. Hence each
edge contributes a nonpositive quantity if $uv\geq\max_{i,j}x_i y_j$.
This recovers the sharp permutation threshold with a local certificate for
every degree, unlike termwise complementary pairing. The comparison
itself is already checked by a different proof in
`MOC/SpectralTwoOutlierComparison.lean`.

## Formalization boundary

[CrossedMinorTransport.lean](MOC/CrossedMinorTransport.lean) formalizes
equal-mass weighted Hall, creation in a vacant unit mode, and two-sided
gluing for a common exterior array satisfying the two contraction
equations. [CrossedMinorBlocks.lean](MOC/CrossedMinorBlocks.lean)
formalizes the unitary spectator annihilation equations and determinant
row and column deflations. Degree and subset reindexing and the final
normalization that identify these arrays remain unformalized. The full
squared-minor transport is the mathematical argument above, not yet a
Lean theorem. Neither result proves unrestricted certificate coverage.

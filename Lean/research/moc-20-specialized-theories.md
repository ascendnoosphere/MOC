# Marcus-de Oliveira formulations: Additional specialized spectral and valuation theories

Atlas entries 232–243.

All eigenvalue lists use the indicated multiplicities. $`S_n`$ is the set of permutations of $`\{1,\ldots,n\}`$; $`U(n)`$ is the complex unitary group; $`*`$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. The Marcus-de Oliveira conjecture asserts that the determinant of the sum of two normal complex operators with fixed eigenvalues lies in the convex hull of products of pairwise matched eigenvalue sums. The statements below specify the spectral data, determinant and necessary scalar realization for each setting.

## Complex spectral form and equivalence

The following statement is part of each numbered formulation. Use the finite spectral realization specified in that entry. For continuous spectral data use a finite sample or a finite spectral resolution. For infinite-dimensional data use a finite spectral subspace. If an entry has fixed rank, take finite direct sums of its realizations and select the required number of modes. When the datum is not a linear operator, use one orthogonal complex coordinate for each selected occurrence of the datum.

Let the two selected spaces have the same positive dimension $`N`$. Choose orthonormal spectral bases in these spaces, with rank-one projections $`P_j,Q_j`$ onto the basis lines. In a repeated eigenspace, choose an orthonormal basis to distinguish its occurrences. Denote the associated scalar or labelled spectral data by $`s_j,t_j`$, respectively. Let $`f,g`$ be arbitrary complex-valued functions of the labelled data $`(s_j,j)`$ and $`(t_j,j)`$. Set

```math
A_f=\sum_{j=1}^N f(s_j,j)P_j,\qquad B_g=\sum_{j=1}^N g(t_j,j)Q_j.
```

For every unitary identification $`U`$ of the second selected space with the first, the conjecture is

```math
\det(A_f+UB_gU^*)\in\mathrm{conv}\left\{\prod_{j=1}^N\big(f(s_j,j)+g(t_{\pi(j)},\pi(j))\big):\pi\in S_N\right\}.
```

The permutation weights may depend on both evaluations and on $`U`$. If the spectra are simple, the occurrence labels are unnecessary: functions of the spectral values suffice.

The forward implication follows from normality of the two diagonal spectral evaluations. For the reverse implication, take any two normal complex matrices of order $`N`$ and list their eigenvalues in orthonormal eigenbases. Select $`N`$ modes in the stated realization of each object and assign these eigenvalues to the two lists through $`f`$ and $`g`$. The relative unitary is unrestricted. The determinant and every permutation product then agree with the original matrix conjecture. Thus the complex spectral form, with all finite ranks and evaluations, is equivalent in both directions. Direct sums and arbitrary unitary mixing here concern the selected linear realizations, not necessarily operations on the native objects. The specific reverse reductions below avoid the extra labels or sums when possible. The native determinant, norm, volume or signed invariant is retained in each entry; an intrinsic comparison not given by this matrix realization requires its own justification.

## 232 Berkovich analytic geometry

Let $`K`$ be a complete nonarchimedean field with a nontrivial absolute value, and let $`X,Y`$ be Berkovich analytic spaces. Choose finite sets of analytic points $`x_j,y_j`$ of equal cardinality $`n>0`$ and analytic functions $`f,g`$ nonzero at those points in the seminorm sense. Let $`s_j=\log|f(x_j)|`$, $`t_j=\log|g(y_j)|`$. For the positive seminorm-value operators $`A=\mathrm{diag}(e^{s_j})`$, $`B=\mathrm{diag}(e^{t_j})`$ on $`\mathbb C^n`$, for every unitary $`U`$,

```math
\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).
```

The product of values gives the modulus of the norm for a finite reduced fiber when the points enumerate its geometric fiber with the required multiplicities. For general points the product is a sampling invariant. A Berkovich point is a seminorm, not a complex eigenvalue.

**Equivalence reduction.** Use finitely many analytic points with distinct nonzero absolute values, such as points in the analytic multiplicative group over a discretely valued field. Select n seminorm-value occurrences as orthogonal coordinates. Arbitrary complex evaluation of them gives the matrix conjecture, rather than a claim about the field norm of a sum.

## 233 Nonarchimedean matrix analysis

Let $`K`$ be a discretely valued field with normalized valuation $`v`$. For invertible matrices $`X,Y\in GL_n(K)`$ choose either the Newton slope lists (valuations of eigenvalues in an algebraic closure) or Hodge slope lists (valuations of elementary divisors relative to a specified lattice). Use the same convention for both and denote the lists by $`s_j,t_j`$. Put $`A=\mathrm{diag}(e^{s_j})`$, $`B=\mathrm{diag}(e^{t_j})`$. For every unitary $`U`$,

```math
\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).
```

The separate sums of either kind of slope equal the determinant valuations. The displayed comparison uses the selected real slope realization and does not assert that actual determinant valuations of $`X+Y`$ are controlled without cancellation hypotheses.

**Equivalence reduction.** Use diagonal matrices over a discretely valued field with distinct integral valuations of the diagonal entries. Their Newton and Hodge slope lists are the same distinct values. Arbitrary complex functions on these values give all normal spectra.

## 234 Smith normal form over a principal ideal domain

Let $`R`$ be a principal ideal domain with a chosen prime element $`\varpi`$ and corresponding integer valuation $`v_\varpi`$. Let $`X,Y`$ be square full-rank matrices of order $`n`$ over $`R`$ with Smith invariant factors $`d_j,e_j`$ ordered by divisibility. Put $`s_j=v_\varpi(d_j)`$, $`t_j=v_\varpi(e_j)`$ and form positive diagonal operators $`A=\mathrm{diag}(e^{s_j})`$, $`B=\mathrm{diag}(e^{t_j})`$ on $`\mathbb C^n`$. For every unitary $`U`$,

```math
\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).
```

The log-determinants of the input operators equal $`v_\varpi(\det X),v_\varpi(\det Y)`$. This is a prime-specific invariant-factor realization. The Smith factors of a sum of original matrices are not invariant under independent left and right basis changes.

**Equivalence reduction.** Use diagonal matrices over a discrete valuation ring with successive powers of a uniformizer as invariant factors. Their distinct integral valuations give n spectral coordinates. Arbitrary complex functions on these coordinates and all unitary positions recover the complex form.

## 235 Module length over a discrete valuation ring

Let $`R`$ be a discrete valuation ring with uniformizer $`\varpi`$. Let $`M,N`$ be finite torsion modules with square diagonal presentations of common positive size $`n`$, allowing unit diagonal entries for zero summands. Write $`M=\bigoplus_{j=1}^n R/(\varpi^{s_j})`$ and $`N=\bigoplus_{j=1}^n R/(\varpi^{t_j})`$, $`s_j,t_j\ge0`$. Form positive length operators $`A=\mathrm{diag}(e^{s_j})`$, $`B=\mathrm{diag}(e^{t_j})`$. For every unitary $`U`$,

```math
\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).
```

The individual log-determinants are the module lengths and the valuations of the generators of the zeroth Fitting ideals. The sum operator is a real realization of elementary lengths, not a presentation matrix over $`R`$.

**Equivalence reduction.** Choose torsion modules that are direct sums of cyclic modules of distinct positive elementary lengths. The length coordinates then have distinct real values. Evaluate arbitrary complex functions on them and compare the complex determinants; module length itself remains additive.

## 236 Iwasawa theory

Let $`M,N`$ be finitely generated torsion modules over a one-variable Iwasawa algebra $`\Lambda=\mathcal O[[T]]`$ for the integers of a finite extension of $`\mathbb Q_p`$. Fix generators of their characteristic ideals, written as a power of a uniformizer times a distinguished polynomial times a unit. Assume the two distinguished polynomials have equal positive degree $`n`$ and nonzero roots. Let $`s_j,t_j`$ be the valuations of those roots, counted with multiplicity in an algebraic closure and in a fixed normalization. Define $`A=\mathrm{diag}(e^{s_j})`$, $`B=\mathrm{diag}(e^{t_j})`$. For every unitary $`U`$,

```math
\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).
```

The spectral length is the common distinguished polynomial degree (the $`\lambda`$ invariant in this setting). The powers of the uniformizer giving the $`\mu`$ invariants are separate and must be retained when reconstructing a characteristic ideal.

**Equivalence reduction.** Use direct sums of cyclic Iwasawa modules defined by distinct distinguished linear factors with nonzero roots of distinct positive valuations, for example powers of a uniformizer. Arbitrary complex evaluation on these root-valuation coordinates recovers every normal spectral list.

## 237 Differential modules and irregular connections

Let $`M,N`$ be formal meromorphic differential modules of equal positive rank $`n`$ over a characteristic-zero Laurent series field. Let $`s_j,t_j`$ be their nonnegative formal slopes in a common valuation convention, repeated by ranks of slope components. Define positive slope operators $`A=\mathrm{diag}(e^{s_j})`$, $`B=\mathrm{diag}(e^{t_j})`$ on complex Hilbert spaces of dimension $`n`$. For every unitary $`U`$,

```math
\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).
```

The two separate log-determinants are the irregularities $`\sum_j s_j`$ and $`\sum_j t_j`$. Formal exponential factors can cancel under taking a determinant connection; its slope need not equal the irregularity. The displayed sum compares slope realizations, not differential connections themselves.

**Equivalence reduction.** Use direct sums of rank-one formal meromorphic connections with distinct integral slopes, for example rank-one exponential factors with distinct pole orders. Their selected slope coordinates admit arbitrary complex evaluations. This gives the exact linear realization, not a determinant of a sum of differential modules.

## 238 Difference equations

Let $`M,N`$ be finite-rank difference modules of rank $`n>0`$ over the same valued difference field, with a chosen slope theory in which determinant slope equals the sum of intrinsic slopes. Let $`s_j,t_j`$ list these slopes with multiplicity. Use positive slope operators $`A=\mathrm{diag}(e^{s_j})`$, $`B=\mathrm{diag}(e^{t_j})`$. For every unitary $`U`$ on the common complex realization,

```math
\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).
```

The individual log-determinants are the slopes of the determinant difference modules. The chosen real realization avoids interpreting eigenvalues of a semilinear difference operator as complex numbers without a linearization.

**Equivalence reduction.** Use direct sums of rank-one difference modules with distinct integral slopes in the specified slope theory, or select labelled lines of finite slope realizations. Arbitrary complex evaluations on those lines recover all normal spectra.

## 239 Filtered vector spaces

Let $`V,W`$ be finite-dimensional complex vector spaces of dimension $`n>0`$, each with a finite exhaustive separated filtration by real weights. Choose Hermitian splittings into orthogonal graded components, and let $`s_j,t_j`$ be their jump weights repeated according to graded dimensions. Let $`A,B`$ be the positive operators acting by $`e^{s}`$ and $`e^{t}`$ on the respective components. For every unitary identification $`U:W\to V`$,

```math
\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).
```

The separate log-determinants equal the weights of the top exterior filtrations. The combined operator defines a new spectral filtration by the logarithms of its eigenvalues. It need not be the usual sum or intersection filtration.

**Equivalence reduction.** Take filtered complex spaces with n distinct real filtration jumps and one-dimensional graded components. Arbitrary complex values on the orthogonal jump coordinates give every normal spectral list. The top exterior weight itself is an additive invariant.

## 240 Metric entropy and singular-value pressure

Let $`X,Y`$ be invertible real matrices of order $`n`$, for example finite products of derivative matrices in a dynamical system. Write $`s_j=\log\sigma_j(X)`$, $`t_j=\log\sigma_j(Y)`$ for their log singular values, where $`\sigma_j`$ are positive singular values. Define $`A=(X^TX)^{1/2}`$, $`B=(Y^TY)^{1/2}`$. For every orthogonal $`Q`$,

```math
\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+QBQ^T)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).
```

The separate sums of the log singular values equal $`\log|\det X|`$ and $`\log|\det Y|`$. This is a full-rank log-volume comparison for the combined stretch. Singular-value pressure uses partial products and limiting growth of words; metric entropy requires dynamical hypotheses beyond this determinant inequality.

**Equivalence reduction.** Use invertible diagonal stretch matrices with arbitrary distinct positive singular values. Complex functions of their log singular values give all normal spectra. The log-volume identity applies only to the original positive stretch operators.

## 241 Fractal spectral geometry

Let two compact fractal metric-measure spaces have specified self-adjoint nonnegative Laplacians with discrete spectrum and finite eigenvalue multiplicities. Select $`n>0`$ orthonormal eigenmodes of each (positive modes if zero modes are excluded), and let $`A,B`$ be the restricted operators with eigenvalues $`\lambda_j,\mu_j`$. For every unitary identification $`U`$ of these mode spaces,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The finite spectral length is $`n`$. Spectral dimension obtained from eigenvalue counting and Hausdorff dimension are not the order of this determinant. Any full zeta determinant requires analytic continuation and a separate limit formulation.

**Equivalence reduction.** Use n positive orthogonal spectral modes of the specified compact fractal Laplacian, with labels for repeated eigenvalues. If the realization has bounded dimension, take finite direct sums of spectral spaces. Complex evaluation on the selected modes gives the exact finite comparison.

## 242 Nonlinear Perron-Frobenius theory

Let $`F,G`$ be order-preserving positively homogeneous maps of degree one on the positive cone in $`\mathbb R^n`$. Choose interior eigenvectors $`x,y`$ with $`F(x)=\lambda x`$ and $`G(y)=\mu y`$, and assume the maps are differentiable there. Let $`A=DF(x)`$, $`B=DG(y)`$ be their derivatives, normal after complexification for a fixed Euclidean product. Let $`\alpha_j,\beta_j`$ be all complex eigenvalues of these derivatives. For every unitary $`U`$ on the complex tangent space,

```math
\det(DF(x)+UDG(y)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\alpha_j+\beta_{\pi(j)}):\pi\in S_{n}\right\}.
```

By homogeneity $`A x=\lambda x`$ and $`B y=\mu y`$, so the positive cone eigenvalues are among the derivative eigenvalues. The remaining derivative spectrum supplies the determinant. A general nonlinear map has no intrinsic determinant of its cone eigenvalues.

**Equivalence reduction.** Use positive diagonal linear maps as a subclass of homogeneous order-preserving maps, allowing nonnegative boundary eigenvectors or simply using their constant derivative. More generally use finite direct sums of derivative spectral realizations. The labelled derivative coordinates and complex evaluations recover the full matrix comparison, not a claim that one cone eigenvalue determines a determinant.

## 243 Numerical-range theory for tuples

Let $`(A_1,\ldots,A_r)`$ and $`(B_1,\ldots,B_r)`$ be internally commuting normal tuples of order $`n`$ on a complex Hilbert space. Enumerate their joint spectra $`a_j,b_j\in\mathbb C^r`$ with joint eigenspace multiplicities. For every $`c\in\mathbb C^r`$ and unitary $`U`$, define $`L_c(x)=\sum_{\ell=1}^r c_\ell x_\ell`$. Then

```math
\det\left(\sum_{\ell=1}^r c_\ell(A_\ell+UB_\ell U^*)\right)\in\mathrm{conv}\left\{\prod_{j=1}^n L_c(a_j+b_{\pi(j)}):\pi\in S_n\right\}.
```

This is the scalar determinant comparison for every direction in the joint spectral data. The joint mixed-state numerical range of each tuple is the convex hull of its joint eigenvalues; the determinant hull uses matched spectral sums instead. Weights may depend on $`c`$; a simultaneous polynomial or vector hull is a stronger form. The case $`r=1`$ is the full matrix conjecture.

**Equivalence reduction.** Already equivalent by taking tuples with one coordinate. For several coordinates the scalar projection must be permitted to vary, and the weights may depend on that projection. Simultaneous vector or polynomial weights require a separate comparison.


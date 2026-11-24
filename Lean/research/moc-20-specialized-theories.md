# Marcus-de Oliveira formulations: Additional specialized spectral and valuation theories

Atlas entries 232–243.

All eigenvalue lists use the indicated multiplicities. $S_n$ is the set of permutations of $\{1,\ldots,n\}$; $U(n)$ is the complex unitary group; $*$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. The Marcus-de Oliveira conjecture asserts that the determinant of the sum of two normal complex operators with fixed eigenvalues lies in the convex hull of products of pairwise matched eigenvalue sums. The statements below specify the spectral data, determinant and necessary scalar realization for each setting.

## 232 Berkovich analytic geometry

Let $K$ be a complete nonarchimedean field with a nontrivial absolute value, and let $X,Y$ be Berkovich analytic spaces. Choose finite sets of analytic points $x_j,y_j$ of equal cardinality $n>0$ and analytic functions $f,g$ nonzero at those points in the seminorm sense. Let $s_j=\log|f(x_j)|$, $t_j=\log|g(y_j)|$. For the positive seminorm-value operators $A=\mathrm{diag}(e^{s_j})$, $B=\mathrm{diag}(e^{t_j})$ on $\mathbb C^n$, for every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The product of values gives the modulus of the norm for a finite reduced fiber when the points enumerate its geometric fiber with the required multiplicities. For general points the product is a sampling invariant. A Berkovich point is a seminorm, not a complex eigenvalue.

## 233 Nonarchimedean matrix analysis

Let $K$ be a discretely valued field with normalized valuation $v$. For invertible matrices $X,Y\in GL_n(K)$ choose either the Newton slope lists (valuations of eigenvalues in an algebraic closure) or Hodge slope lists (valuations of elementary divisors relative to a specified lattice). Use the same convention for both and denote the lists by $s_j,t_j$. Put $A=\mathrm{diag}(e^{s_j})$, $B=\mathrm{diag}(e^{t_j})$. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The separate sums of either kind of slope equal the determinant valuations. The displayed comparison uses the selected real slope realization and does not assert that actual determinant valuations of $X+Y$ are controlled without cancellation hypotheses.

## 234 Smith normal form over a principal ideal domain

Let $R$ be a principal ideal domain with a chosen prime element $\varpi$ and corresponding integer valuation $v_\varpi$. Let $X,Y$ be square full-rank matrices of order $n$ over $R$ with Smith invariant factors $d_j,e_j$ ordered by divisibility. Put $s_j=v_\varpi(d_j)$, $t_j=v_\varpi(e_j)$ and form positive diagonal operators $A=\mathrm{diag}(e^{s_j})$, $B=\mathrm{diag}(e^{t_j})$ on $\mathbb C^n$. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The log-determinants of the input operators equal $v_\varpi(\det X),v_\varpi(\det Y)$. This is a prime-specific invariant-factor realization. The Smith factors of a sum of original matrices are not invariant under independent left and right basis changes.

## 235 Module length over a discrete valuation ring

Let $R$ be a discrete valuation ring with uniformizer $\varpi$. Let $M,N$ be finite torsion modules with square diagonal presentations of common positive size $n$, allowing unit diagonal entries for zero summands. Write $M=\bigoplus_{j=1}^n R/(\varpi^{s_j})$ and $N=\bigoplus_{j=1}^n R/(\varpi^{t_j})$, $s_j,t_j\ge0$. Form positive length operators $A=\mathrm{diag}(e^{s_j})$, $B=\mathrm{diag}(e^{t_j})$. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The individual log-determinants are the module lengths and the valuations of the generators of the zeroth Fitting ideals. The sum operator is a real realization of elementary lengths, not a presentation matrix over $R$.

## 236 Iwasawa theory

Let $M,N$ be finitely generated torsion modules over a one-variable Iwasawa algebra $\Lambda=\mathcal O[[T]]$ for the integers of a finite extension of $\mathbb Q_p$. Fix generators of their characteristic ideals, written as a power of a uniformizer times a distinguished polynomial times a unit. Assume the two distinguished polynomials have equal positive degree $n$ and nonzero roots. Let $s_j,t_j$ be the valuations of those roots, counted with multiplicity in an algebraic closure and in a fixed normalization. Define $A=\mathrm{diag}(e^{s_j})$, $B=\mathrm{diag}(e^{t_j})$. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The spectral length is the common distinguished polynomial degree (the $\lambda$ invariant in this setting). The powers of the uniformizer giving the $\mu$ invariants are separate and must be retained when reconstructing a characteristic ideal.

## 237 Differential modules and irregular connections

Let $M,N$ be formal meromorphic differential modules of equal positive rank $n$ over a characteristic-zero Laurent series field. Let $s_j,t_j$ be their nonnegative formal slopes in a common valuation convention, repeated by ranks of slope components. Define positive slope operators $A=\mathrm{diag}(e^{s_j})$, $B=\mathrm{diag}(e^{t_j})$ on complex Hilbert spaces of dimension $n$. For every unitary $U$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The two separate log-determinants are the irregularities $\sum_j s_j$ and $\sum_j t_j$. Formal exponential factors can cancel under taking a determinant connection; its slope need not equal the irregularity. The displayed sum compares slope realizations, not differential connections themselves.

## 238 Difference equations

Let $M,N$ be finite-rank difference modules of rank $n>0$ over the same valued difference field, with a chosen slope theory in which determinant slope equals the sum of intrinsic slopes. Let $s_j,t_j$ list these slopes with multiplicity. Use positive slope operators $A=\mathrm{diag}(e^{s_j})$, $B=\mathrm{diag}(e^{t_j})$. For every unitary $U$ on the common complex realization,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The individual log-determinants are the slopes of the determinant difference modules. The chosen real realization avoids interpreting eigenvalues of a semilinear difference operator as complex numbers without a linearization.

## 239 Filtered vector spaces

Let $V,W$ be finite-dimensional complex vector spaces of dimension $n>0$, each with a finite exhaustive separated filtration by real weights. Choose Hermitian splittings into orthogonal graded components, and let $s_j,t_j$ be their jump weights repeated according to graded dimensions. Let $A,B$ be the positive operators acting by $e^{s}$ and $e^{t}$ on the respective components. For every unitary identification $U:W\to V$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+UBU^*)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The separate log-determinants equal the weights of the top exterior filtrations. The combined operator defines a new spectral filtration by the logarithms of its eigenvalues. It need not be the usual sum or intersection filtration.

## 240 Metric entropy and singular-value pressure

Let $X,Y$ be invertible real matrices of order $n$, for example finite products of derivative matrices in a dynamical system. Write $s_j=\log\sigma_j(X)$, $t_j=\log\sigma_j(Y)$ for their log singular values, where $\sigma_j$ are positive singular values. Define $A=(X^TX)^{1/2}$, $B=(Y^TY)^{1/2}$. For every orthogonal $Q$,

$$\min_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}})\le \log\det(A+QBQ^T)\le\max_{\pi\in S_n}\sum_{j=1}^{n}\log(e^{s_j}+e^{t_{\pi(j)}}).$$

The separate sums of the log singular values equal $\log|\det X|$ and $\log|\det Y|$. This is a full-rank log-volume comparison for the combined stretch. Singular-value pressure uses partial products and limiting growth of words; metric entropy requires dynamical hypotheses beyond this determinant inequality.

## 241 Fractal spectral geometry

Let two compact fractal metric-measure spaces have specified self-adjoint nonnegative Laplacians with discrete spectrum and finite eigenvalue multiplicities. Select $n>0$ orthonormal eigenmodes of each (positive modes if zero modes are excluded), and let $A,B$ be the restricted operators with eigenvalues $\lambda_j,\mu_j$. For every unitary identification $U$ of these mode spaces,

$$\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The finite spectral length is $n$. Spectral dimension obtained from eigenvalue counting and Hausdorff dimension are not the order of this determinant. Any full zeta determinant requires analytic continuation and a separate limit formulation.

## 242 Nonlinear Perron-Frobenius theory

Let $F,G$ be order-preserving positively homogeneous maps of degree one on the positive cone in $\mathbb R^n$. Choose interior eigenvectors $x,y$ with $F(x)=\lambda x$ and $G(y)=\mu y$, and assume the maps are differentiable there. Let $A=DF(x)$, $B=DG(y)$ be their derivatives, normal after complexification for a fixed Euclidean product. Let $\alpha_j,\beta_j$ be all complex eigenvalues of these derivatives. For every unitary $U$ on the complex tangent space,

$$\det(DF(x)+UDG(y)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\alpha_j+\beta_{\pi(j)}):\pi\in S_{n}\right\}.$$

By homogeneity $A x=\lambda x$ and $B y=\mu y$, so the positive cone eigenvalues are among the derivative eigenvalues. The remaining derivative spectrum supplies the determinant. A general nonlinear map has no intrinsic determinant of its cone eigenvalues.

## 243 Numerical-range theory for tuples

Let $(A_1,\ldots,A_r)$ and $(B_1,\ldots,B_r)$ be internally commuting normal tuples of order $n$ on a complex Hilbert space. Enumerate their joint spectra $a_j,b_j\in\mathbb C^r$ with joint eigenspace multiplicities. For every $c\in\mathbb C^r$ and unitary $U$, define $L_c(x)=\sum_{\ell=1}^r c_\ell x_\ell$. Then

$$\det\left(\sum_{\ell=1}^r c_\ell(A_\ell+UB_\ell U^*)\right)\in\mathrm{conv}\left\{\prod_{j=1}^n L_c(a_j+b_{\pi(j)}):\pi\in S_n\right\}.$$

This is the scalar determinant comparison for every direction in the joint spectral data. The joint mixed-state numerical range of each tuple is the convex hull of its joint eigenvalues; the determinant hull uses matched spectral sums instead. Weights may depend on $c$; a simultaneous polynomial or vector hull is a stronger form. The case $r=1$ is the full matrix conjecture.

# Marcus-de Oliveira formulations: Infinite-dimensional spectral and determinant theory

Atlas entries 061–072.

All finite eigenvalue lists include multiplicities unless stated otherwise. $`S_n`$ denotes the permutations of $`\{1,\ldots,n\}`$; $`U(n)`$ denotes the unitary group; $`*`$ denotes the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. An overline denotes closure. The original conjecture asserts that the determinant of a sum of two normal complex matrices with fixed eigenvalues is in the convex hull of the products of their pairwise matched eigenvalue sums. The statements below specify the operator, invariant and comparison data in each setting. New extensions require proof; an additional realization or finite spectral window is part of the statement when no intrinsic scalar determinant exists.

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

## 061 Compact operators

Let $`A,B`$ be compact normal operators on a separable Hilbert space. Choose a finite-dimensional common compression space $`E`$ with orthogonal projection $`P`$ such that $`A_E=P A|_E`$ and $`B_E=P B|_E`$ are normal. List their eigenvalues $`\lambda_j,\mu_j`$ with $`n=\dim E>0`$. For every unitary $`U`$ on $`E`$,

```math
\det_E(A_E+UB_EU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This is the finite spectral-block formulation. If $`A,B`$ are also trace class, the Fredholm version gives a convergent infinite determinant. Compactness alone does not imply a convergent eigenvalue product.

**Equivalence reduction.** Use finite-rank diagonal normal operators on a Hilbert space, and choose their nonzero finite invariant blocks. The finite-block comparison recovers arbitrary normal spectra by scalar evaluation, including zeros.

## 062 Trace-class operators

Let $`A,B`$ be normal trace-class operators on a separable infinite-dimensional complex Hilbert space. List the eigenvalues in complete orthonormal eigenbases as summable sequences $`\lambda_j,\mu_j`$. For every unitary $`U`$ on the space,

```math
\det_F(I+A+UBU^*)\in\overline{\mathrm{conv}}\left\{\prod_{j\ge1}(1+\lambda_j+\mu_{\pi(j)}):\pi\text{ a finite permutation of }\mathbb N\right\}.
```

The closed hull permits limits of finite permutations. Each product converges since the corresponding sum sequence is absolutely summable. Finite-rank truncation in trace norm connects this assertion to the matrix conjecture; the finite-dimensional version with $`I`$ removed is obtained by a scalar shift of the first matrix.

**Equivalence reduction.** Use the finite-dimensional Fredholm determinant as well as the infinite limit. On a finite space the shift of one normal input by minus the identity converts the Fredholm formula into the original determinant comparison; the eigenvalue products undergo exactly the same shift.

## 063 Hilbert-Schmidt operators

Let $`A,B`$ be normal Hilbert-Schmidt operators on a separable Hilbert space with eigenvalue sequences $`\lambda_j,\mu_j`$ in $`\ell^2`$, repeated according to complete eigenbases. For $`C`$ Hilbert-Schmidt define the second regularized determinant $`\det_2(I+C)=\prod_j(1+c_j)e^{-c_j}`$, using the algebraic eigenvalues $`c_j`$. Put $`E_2(z)=(1+z)e^{-z}`$. For every unitary $`U`$, propose

```math
\det_2(I+A+UBU^*)\in\overline{\mathrm{conv}}\left\{\prod_{j\ge1}E_2(\lambda_j+\mu_{\pi(j)}):\pi\text{ a finite permutation of }\mathbb N\right\}.
```

The products are convergent. For finite rank the exponential correction is independent of the relative unitary position because trace is additive; in general the determinant is continuous in Hilbert-Schmidt norm. No ordinary trace of an arbitrary Hilbert-Schmidt operator is required.

**Equivalence reduction.** For a finite block the regularization multiplies each determinant and each vertex by the same nonzero exponential of the negative sum of the two traces. Cancel that common factor, and use a scalar shift to remove the identity. This is the exact finite form; the Hilbert-Schmidt limit is its closed-hull consequence.

## 064 Schatten classes

Fix an integer $`p\ge1`$. Let $`A,B`$ be normal operators in the Schatten class $`S_p`$ (the $`p`$th powers of their singular values are summable). Let $`\lambda_j,\mu_j`$ be their eigenvalues from complete orthonormal eigenbases. Define $`E_p(z)=(1+z)\exp(\sum_{k=1}^{p-1}(-1)^k z^k/k)`$ and $`\det_p(I+C)=\prod_j E_p(c_j)`$. For all unitary $`U`$, the regularized determinant candidate is

```math
\det_p(I+A+UBU^*)\in\overline{\mathrm{conv}}\left\{\prod_{j\ge1}E_p(\lambda_j+\mu_{\pi(j)}):\pi\text{ a finite permutation of }\mathbb N\right\}.
```

For $`p=1,2`$ the finite-matrix conjecture and determinant continuity give the corresponding limit statement. For $`p\ge3`$ the higher trace corrections can depend on $`U`$; the displayed candidate is not an algebraic equivalent of the ordinary determinant conjecture.

**Equivalence reduction.** For regularization orders one and two use the common factor argument and finite blocks. At higher orders the orbit-dependent trace corrections must not be cancelled. The exact form at any order uses the ordinary determinant of the finite spectral evaluation, or undoes the regularization by its defining exponential before comparing vertices.

## 065 Integral operators

Let $`(X,\nu)`$ be a finite measure space and let $`A,B`$ be normal trace-class integral operators on the separable space $`L^2(X,\nu)`$, with kernels $`K_A,K_B`$ and eigenvalue sequences $`\lambda_j,\mu_j`$ in complete orthonormal eigenbases. For every unitary $`U`$ on $`L^2`$,

```math
\det_F(I+A+UBU^*)\in\overline{\mathrm{conv}}\left\{\prod_{j\ge1}(1+\lambda_j+\mu_{\pi(j)}):\pi\text{ a finite permutation of }\mathbb N\right\}.
```

Use the Fredholm determinant of the sum of integral operators, not an integral of pointwise kernel determinants. Kernel diagonal integrals give the traces only when the necessary diagonal regularity holds.

**Equivalence reduction.** On a finite probability space with n atoms, every complex matrix acts as an integral operator by a suitable kernel. Use arbitrary normal matrices on this finite space and apply the Fredholm identity with an affine shift to recover the ordinary determinant.

## 066 Elliptic operators on closed manifolds

Let $`M`$ be a closed Riemannian manifold and $`L_1,L_2`$ positive self-adjoint elliptic operators with compact resolvent on the same complex $`L^2`$ space. Choose $`n`$ orthonormal eigenfunctions of each, and let $`E,F`$ be their spans, with respective positive eigenvalues $`\lambda_j,\mu_j`$. For every unitary identification $`U:F\to E`$,

```math
\det_E(L_1|_E+U(L_2|_F)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This uses finite elliptic spectral windows. Zeta determinants of full unbounded operators require analytic continuation and are not limits of unnormalized products in this hull.

**Equivalence reduction.** Choose n positive elliptic eigenmodes with multiplicity, and apply arbitrary complex evaluations to their spectral coordinates. If an eigenvalue repeats, select independent labelled modes. Do not pass to an infinite zeta determinant in the reverse reduction.

## 067 Pseudodifferential calculus

Let $`A,B`$ be classical pseudodifferential operators on sections of a Hermitian vector bundle of rank $`n`$ over a closed manifold. Assume their principal symbols $`a(x,\xi),b(x,\xi)`$ have the same order and are normal endomorphisms at each nonzero cotangent vector $`(x,\xi)`$. At that vector let $`\lambda_j,\mu_j`$ be the symbol eigenvalues. For every unitary endomorphism $`u`$ of the fiber,

```math
\det(a(x,\xi)+u b(x,\xi)u^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This is a pointwise symbol determinant. It does not identify the Wodzicki residue or a regularized determinant of the entire operator with a pointwise product.

**Equivalence reduction.** Use order-zero multiplication operators by constant normal matrices on a trivial rank-n Hermitian bundle. Their principal symbols have arbitrary prescribed normal matrix spectra in each fiber. This realizes the original conjecture pointwise.

## 068 Spectral triples

Let $`(\mathcal A,H,D)`$ be a spectral triple with a self-adjoint Dirac operator $`D`$ of compact resolvent. Let $`D_1,D_2`$ be two self-adjoint Dirac-type operators on $`H`$ with compact resolvent. Choose $`n`$ eigenvectors of each spanning $`E_1,E_2`$, and let $`\lambda_j,\mu_j`$ be their signed Dirac eigenvalues. For every unitary $`U:E_2\to E_1`$,

```math
\det_{E_1}(D_1|_{E_1}+U(D_2|_{E_2})U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The rank is the finite spectral count. The dimension spectrum of the triple (poles of its zeta functions) is not this eigenvalue list.

**Equivalence reduction.** Use finite spectral windows of a compact-resolvent Dirac operator with at least n modes. Scalar evaluations on the selected spectral resolution give arbitrary complex eigenvalues; the dimension spectrum of zeta poles is not used.

## 069 Dixmier trace theory

Let $`A,B`$ be positive compact operators in the weak trace ideal $`\mathcal L^{1,\infty}`$ on a separable Hilbert space. Let $`A_N,B_N`$ be the positive diagonal operators on $`\mathbb C^N`$ with their first $`N`$ singular values $`s_j,t_j`$, respectively. For all $`U_N\in U(N)`$,

```math
\det(I_N+A_N+U_NB_NU_N^*)\in\mathrm{conv}\left\{\prod_{j=1}^{N}(1+s_j+t_{\pi(j)}):\pi\in S_{N}\right\}.
```

The shift by one occurs in every permutation factor. This is a finite product test of the singular data. A Dixmier trace is a generalized limit of logarithmically normalized sums, not a determinant; no unregularized infinite product is presumed.

**Equivalence reduction.** Finite-rank positive diagonal operators with distinct nonzero singular values lie in the weak trace ideal. Evaluate arbitrary complex functions on the first n spectral coordinates and use an affine shift in the finite determinant. No Dixmier trace is needed to recover the complex phase.

## 070 De la Harpe-Skandalis determinant

Let $`\mathcal A=M_n(\mathbb C)`$ with normalized trace $`\tau=\mathrm{Tr}/n`$. Let $`A,B`$ be normal with eigenvalues $`\lambda_j,\mu_j`$, and suppose $`C=A+UBU^*`$ is invertible for a unitary $`U`$. For a piecewise smooth invertible path $`g:[0,1]\to GL_n(\mathbb C)`$ from $`I`$ to $`C`$, define $`L(g)=(2\pi i)^{-1}\int_0^1\tau(g'(t)g(t)^{-1})\,dt`$. Then

```math
\exp(2\pi i n L(g))\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

Changing the path changes $`nL(g)`$ by an integer, so the exponential is well defined and equals $`\det C`$. Singular sums are included by continuity of the ordinary determinant. In general Banach algebras the period group need not admit this scalar exponential.

**Equivalence reduction.** For every invertible finite sum the path exponential is exactly its complex determinant. If a sum is singular, apply the statement to scalar shifts that are invertible and take the limit; the corresponding finite permutation hulls converge. This recovers the full conjecture in every order.

## 071 Perturbation determinants

Let $`A,B`$ be normal trace-class operators on a separable Hilbert space with eigenvalue sequences $`\lambda_j,\mu_j`$. Fix $`z\ne0`$ and consider the relative Fredholm determinant against the reference operator $`-zI`$, namely $`D_z(U)=\det_F((A+UBU^*-zI)(-zI)^{-1})`$. For each unitary $`U`$,

```math
D_z(U)\in\overline{\mathrm{conv}}\left\{\prod_{j\ge1}\left(1-\frac{\lambda_j+\mu_{\pi(j)}}{z}\right):\pi\text{ a finite permutation of }\mathbb N\right\}.
```

The relative operator is identity plus trace class. More general reference operators need not preserve the two spectra or reduce to the same permutation factors.

**Equivalence reduction.** Use the relative determinant on finite spectral blocks and set the reference scalar to a fixed nonzero value. Affine shifts and scaling of the normal inputs recover the unshifted ordinary determinant. General perturbation determinants in infinite dimension are not required for the reverse implication.

## 072 Scattering theory

At a fixed energy $`E`$, let $`S_1(E),S_2(E)`$ be unitary scattering matrices on a common $`n`$-channel Hilbert space. Let their eigenphases be $`\theta_j,\phi_j`$, so $`\lambda_j=e^{i\theta_j}`$ and $`\mu_j=e^{i\phi_j}`$. For every unitary channel mixing $`U`$,

```math
\det(S_1(E)+US_2(E)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The sum is a determinant comparison of scattering amplitudes; it need not itself be a unitary scattering matrix. Resonance poles are not included among channel eigenvalues.

**Equivalence reduction.** Use diagonal unitary scattering matrices on n channels with distinct phases. Complex spectral functions and arbitrary channel identifications realize arbitrary normal pairs. The phase-only form restricts those functions to the identity.


# Marcus-de Oliveira formulations: PDEs, spectral geometry and mathematical physics

Atlas entries 196–207.

All eigenvalue lists use the indicated multiplicities. $`S_n`$ is the set of permutations of $`\{1,\ldots,n\}`$; $`U(n)`$ is the complex unitary group; $`*`$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. For normal operators the Marcus-de Oliveira conjecture compares the determinant of the sum over relative unitary positions with the convex hull of products of matched eigenvalue sums. The statements below identify the operator, its spectral length, and the determinant used in each setting. When the native object has no such determinant, the specified realization is part of the formulation.

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

## 196 Laplace-Beltrami operator

Let $`(M,g)`$ and $`(N,h)`$ be closed Riemannian manifolds with nonnegative Laplace-Beltrami operators $`-\Delta_g,-\Delta_h`$. Select $`n>0`$ orthonormal positive-eigenvalue modes in each $`L^2`$ space. Let $`A,B`$ be the corresponding finite restrictions and $`\lambda_j,\mu_j>0`$ their eigenvalues. For every unitary identification $`U`$ between these mode spaces,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The formula uses the number of selected modes, not manifold dimension. The full zeta determinant excludes zero modes and uses analytic continuation; the finite determinant is not asserted to converge to it.

**Equivalence reduction.** Use n positive orthogonal Laplace modes of a compact manifold. A circle provides arbitrarily many distinct positive eigenvalues, and one eigenline may be selected for each. Arbitrary complex functions of these values recover every normal spectral list.

## 197 Schrodinger operators

Let $`H_1=-\Delta+V_1`$ and $`H_2=-\Delta+V_2`$ be self-adjoint Schrödinger operators on specified complex Hilbert spaces. Choose finite invariant subspaces of bound states, each of dimension $`n>0`$, and let $`A,B`$ be their restrictions with real energies $`\lambda_j,\mu_j`$. For every unitary identification $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The determinant is a product of energies of the combined finite operator. Continuous energy spectrum and spectral or relative determinants of unbounded operators require additional definitions.

**Equivalence reduction.** Use n selected bound-state spectral lines of self-adjoint Schrödinger operators, for example the one-dimensional harmonic oscillator with its distinct energies. Arbitrary complex spectral functions on these lines and the full relative unitary group give the exact form.

## 198 Dirac operators

Let $`D_1,D_2`$ be self-adjoint Dirac operators on compact spin manifolds with discrete spectra. Choose $`n>0`$ orthonormal spinor eigenmodes from each, and let $`A,B`$ be their finite restrictions, with signed eigenvalues $`\lambda_j,\mu_j`$. For each unitary identification $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The signs are retained; replacing eigenvalues by their absolute values would change the determinant. Eta invariants measure spectral asymmetry, and zeta determinants may require a spectral cut.

**Equivalence reduction.** Use the finite Dirac modes of a circle, with their distinct signed Fourier eigenvalues. Select n eigenlines and evaluate arbitrary complex functions. No spectral cut or eta regularization is required for the finite determinant.

## 199 Elliptic boundary problems

Let $`A_0,B_0`$ be self-adjoint elliptic differential operators on compact domains with specified self-adjoint elliptic boundary conditions and compact resolvent. Select invariant finite eigenmode spaces of common dimension $`n>0`$; denote the restrictions by $`A,B`$ and their real eigenvalues by $`\lambda_j,\mu_j`$. For every unitary identification $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The eigenvalues and finite-dimensional determinant depend on the specified boundary conditions. The combined mode operator is not assumed to define an elliptic boundary problem on the original domain.

**Equivalence reduction.** Use the Dirichlet Laplacian on an interval. Its positive eigenvalues are distinct and can supply n modes for any n. Apply arbitrary complex functions to those values before the determinant comparison.

## 200 Steklov spectral geometry

Let two compact smooth Riemannian manifolds with boundary have Dirichlet-to-Neumann operators $`\Lambda_1,\Lambda_2`$ (they map boundary values of harmonic functions to outward normal derivatives). Choose $`n>0`$ orthonormal boundary eigenmodes of each, with nonnegative Steklov eigenvalues $`\lambda_j,\mu_j`$. Let $`A,B`$ be the restrictions. For every unitary identification $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The determinant is taken on the selected boundary mode spaces; zero constant modes may be included or excluded in both specified lists. A regularized full Steklov determinant is a different construction.

**Equivalence reduction.** Use Steklov eigenmodes on a disk, selecting one mode for each of n distinct positive eigenvalues. Complex spectral evaluation gives arbitrary normal spectra; the complete boundary zeta determinant is a separate invariant.

## 201 Wave equations

Let two wave systems have nonnegative self-adjoint spatial generators $`L_1,L_2`$ in equations $`u_{tt}+L_i u=0`$. Select $`n>0`$ normal modes from each and use their nonnegative frequency operators $`A=L_1^{1/2}`$ and $`B=L_2^{1/2}`$ restricted to the mode spaces. Let $`\lambda_j,\mu_j`$ be the corresponding frequencies. For every unitary identification $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This bounds the product of frequencies of the combined frequency operator, not the product of frequencies of $`(L_1+UL_2U^*)^{1/2}`$. The latter uses squared-frequency eigenvalue factors before taking a square root.

**Equivalence reduction.** Use the positive frequencies of the Dirichlet wave equation on an interval. There are arbitrarily many distinct frequencies. Complex functions on n selected frequency modes recover arbitrary complex eigenvalue lists.

## 202 Quantum mechanics

Let $`A,B`$ be self-adjoint observables on a finite-dimensional complex Hilbert space of dimension $`n`$, with eigenvalue lists $`\lambda_j,\mu_j\in\mathbb R`$. For every unitary change of relative measurement basis $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The determinant is the product of the eigenvalues of the combined observable. An expectation $`\mathrm{tr}(\rho A)`$ in a density state $`\rho`$ is a different, linear invariant. Normal non-self-adjoint quantum operators give the complex version.

**Equivalence reduction.** Use self-adjoint observables of arbitrary finite dimension with distinct real spectra. Arbitrary complex functions on their spectral projections give all normal matrices. If normal non-self-adjoint observables are allowed directly, no additional spectral evaluation is required.

## 203 Quantum statistical mechanics

Let $`H,K`$ be finite-dimensional self-adjoint Hamiltonians on a common Hilbert space of dimension $`n`$, with energies $`E_j,F_j`$. At inverse temperature $`\beta>0`$, form the positive Boltzmann operators $`A=e^{-\beta H}`$ and $`B=e^{-\beta K}`$. For every unitary $`U`$,

```math
\det(e^{-\beta H}+Ue^{-\beta K}U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(e^{-\beta E_j}+e^{-\beta F_{\pi(j)}}):\pi\in S_n\right\}.
```

The traces of the input operators are partition functions. The exponential of the sum of Hamiltonians has orbit-independent determinant and is not the sum of Boltzmann operators.

**Equivalence reduction.** Use finite Hamiltonians of order n with distinct real energies. At any fixed positive inverse temperature the Boltzmann values are distinct. Complex functions of these values give arbitrary normal spectra. Keep the thermal interpretation only for the original positive values.

## 204 Quantum channels

Let $`\Phi,\Psi`$ be completely positive trace-preserving linear maps on $`M_d(\mathbb C)`$. Equip this operator space with the Hilbert-Schmidt inner product and assume the superoperators $`A=\Phi`$, $`B=\Psi`$ are normal for it. Their eigenvalues $`\lambda_j,\mu_j`$ have length $`n=d^2`$. For every unitary $`U`$ on the operator space,

```math
\det_{\rm super}\big((\Phi+U\Psi U^*)/2\big)\in\mathrm{conv}\left\{2^{-n}\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)}):\pi\in S_n\right\}.
```

For a unitary induced by conjugation on $`M_d(\mathbb C)`$, the average is again a quantum channel. Arbitrary superoperator unitaries need not preserve complete positivity. Normality is not implied by the channel axioms.

**Equivalence reduction.** Use the Hilbert-Schmidt space of finite matrix algebras of sufficiently large dimension, and select n labelled orthogonal modes of a normal channel such as the identity channel. Arbitrary complex evaluation distinguishes these modes, even at a repeated eigenvalue. The original complete-positivity condition need not hold for the evaluated operators.

## 205 Lindblad generators

Let $`\mathcal L,\mathcal K`$ be finite-dimensional generators of completely positive trace-preserving continuous semigroups on $`M_d(\mathbb C)`$. Assume both normal in the Hilbert-Schmidt operator inner product. With $`n=d^2`$ and generator eigenvalues $`\lambda_j,\mu_j`$, for every superoperator unitary $`U`$ and complex $`z`$,

```math
\det_{\rm super}(zI-\mathcal L-U\mathcal K U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(z-\lambda_j-\mu_{\pi(j)}):\pi\in S_n\right\}.
```

For $`U`$ induced by a unitary change of physical basis the sum is a Lindblad generator. The nonzero shift permits a characteristic determinant even though a trace-preserving generator has a zero eigenvalue. The determinant of its exponential is fixed by the trace of the generator.

**Equivalence reduction.** Use a zero or normal dephasing Lindblad generator in a sufficiently large finite Liouville space. Select n labelled orthogonal modes and apply arbitrary complex functions before the characteristic determinant. A zero characteristic parameter recovers the ordinary sum determinant; evaluated maps need not be Lindblad generators.

## 206 Random matrix theory

Let $`A,B`$ be random normal complex matrices of order $`n`$ on a common probability space. For each outcome, list their eigenvalues $`\lambda_j,\mu_j`$ with multiplicity. Let $`U`$ be any random unitary of order $`n`$, with no independence assumption. Then almost surely,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The hull is random and depends on the realized spectra. If the matrices are Hermitian and the products integrable, taking expectations gives the expected minimum and maximum as bounds on the expected determinant. A limiting empirical spectral law alone does not specify finite-dimensional extreme products.

**Equivalence reduction.** Take the random matrices and the random unitary to be constant on a one-point probability space. The almost-sure determinant comparison then gives every deterministic instance of the conjecture.

## 207 Transfer-matrix statistical mechanics

Let $`T,S`$ be normal complex transfer matrices of equal order $`n`$, representing specified finite sets of states, with eigenvalues $`\lambda_j,\mu_j`$. For every unitary change of relative state basis $`U`$,

```math
\det(T+USU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

For the combined transfer matrix $`C=T+USU^*`$, the periodic chain partition function of length $`m`$ is $`\mathrm{tr}(C^m)`$ when that transfer model applies. The conjecture bounds $`\det C`$, not this trace. Nonnegative transfer matrices are not necessarily normal; symmetric transfer matrices are included.

**Equivalence reduction.** Use finite diagonal transfer operators with distinct positive entries and arbitrary complex functions on those entries. If arbitrary normal complex transfer operators are allowed directly, the determinant comparison already gives every matrix instance.


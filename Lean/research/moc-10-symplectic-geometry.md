# Marcus-de Oliveira formulations: Symplectic, Hamiltonian and contact geometry

Atlas entries 112–123.

All finite eigenvalue lists include multiplicities unless stated otherwise. $`S_n`$ denotes the permutations of $`\{1,\ldots,n\}`$, $`U(n)`$ the unitary group, $`*`$ the Hermitian adjoint and $`\mathrm{conv}`$ the real-affine convex hull. For normal complex operators $`A,B`$ of order $`n`$, the Marcus-de Oliveira conjecture compares $`\det(A+UBU^*)`$ with the products $`\prod_{j=1}^n(\lambda_j+\mu_{\pi(j)})`$ of matched eigenvalue sums. The statements below specify the required operator and determinant for each object. An auxiliary realization is part of a formulation where the object itself has no scalar determinant.

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

## 112 Symplectic linear maps

Let $`(V,\omega)`$ be a real symplectic space of dimension $`2r`$, with a compatible positive inner product. Let $`A,B`$ be symplectic linear maps that are normal after complexification for this product. Their complex eigenvalues $`\lambda_j,\mu_j`$ occur in reciprocal pairs, $`n=2r`$. For every orthogonal symplectic $`Q`$,

```math
\det(A+QBQ^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

Each symplectic map has determinant one; their sum is not necessarily symplectic.

**Equivalence reduction.** Use independent reciprocal-pair symplectic blocks of the form diagonal positive stretch and inverse stretch. Select one spectral line from each pair and apply arbitrary complex functions to the resulting distinct values. The exact comparison uses complex unitaries on the selected modes.

## 113 Williamson theory

Let $`G,H`$ be positive definite real symmetric matrices of order $`2r`$ on a standard symplectic space. Let $`\nu_j,\eta_j>0`$ be their symplectic eigenvalues: the positive numbers in Williamson's diagonal normal forms $`\mathrm{diag}(\nu,\nu)`$ and $`\mathrm{diag}(\eta,\eta)`$. Write $`D_\nu,D_\eta`$ for these diagonal matrices. For every orthogonal symplectic $`Q`$, the Williamson-representative comparison is

```math
\det(D_\nu+QD_\eta Q^T)\in\mathrm{conv}\left\{\prod_{j=1}^{2r}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{2r}\right\},
```

where $`\lambda=(\nu,\nu)`$ and $`\mu=(\eta,\eta)`$. Each individual determinant is the product of squared symplectic eigenvalues. General symplectic congruence is not unitary conjugation and can change the determinant of a sum even with fixed symplectic spectra.

**Equivalence reduction.** Choose n independent Williamson frequency pairs, with distinct positive frequencies. Select one orthogonal mode per pair, and evaluate arbitrary complex functions on the n frequencies. This removes the duplicated spectral multiplicity and recovers arbitrary normal spectra on the selected complex space.

## 114 Hamiltonian linearization

Let $`J`$ be the standard symplectic matrix of order $`2r`$ and let $`H,K`$ be real symmetric Hamiltonian Hessians. Suppose $`A=JH`$ and $`B=JK`$ are normal on the complexified tangent space with the Euclidean inner product. Let $`\lambda_j,\mu_j`$ be their complex eigenvalues (Hamiltonian eigenvalues occur in symmetry-related pairs), with $`n=2r`$. For every orthogonal symplectic $`Q`$,

```math
\det(JH+QJKQ^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The sum remains a Hamiltonian linearization for such $`Q`$. Its trace is zero, and its determinant can vanish at a degenerate equilibrium.

**Equivalence reduction.** Use direct sums of two-dimensional harmonic oscillator linearizations, whose normal complex eigenvalues are opposite imaginary pairs. Select one eigenline in each pair and apply arbitrary complex functions. Allow arbitrary relative unitary positions on this selected block.

## 115 Hamiltonian torus actions

Let a torus $`T`$ act on two compact connected Hamiltonian manifolds with moment maps $`\Phi_1,\Phi_2`$ and finitely many isolated fixed points, each set of size $`n>0`$. Choose a complex linear scalar evaluation of real moment vectors $`L:\mathfrak t^*\to\mathbb C`$ (real-linear is sufficient). Enumerate $`\lambda_j=L(\Phi_1(p_j))`$, $`\mu_j=L(\Phi_2(q_j))`$ at the fixed points. On $`\mathbb C^n`$ set $`A=\mathrm{diag}(\lambda_j)`$, $`B=\mathrm{diag}(\mu_j)`$. For every unitary $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The diagonal operators use fixed-point moment data. The convexity theorem for the image of a moment map does not itself provide this determinant or the orbit weights.

**Equivalence reduction.** Choose a compact Hamiltonian torus action with at least n isolated fixed points, for example a projective space with its coordinate torus action. Select n fixed-point moment coordinates and label them by the fixed points. Arbitrary complex scalar evaluation gives the exact form.

## 116 Symplectic toric geometry

Let $`P,Q\subset\mathbb R^r`$ be moment polytopes of compact symplectic toric manifolds, each with $`n>0`$ vertices. Choose a real-linear functional $`L:\mathbb R^r\to\mathbb C`$, and put $`\lambda_j=L(p_j)`$ and $`\mu_j=L(q_j)`$ for enumerated vertices. Define normal vertex-value operators $`A=\mathrm{diag}(\lambda_j)`$ and $`B=\mathrm{diag}(\mu_j)`$ on $`\mathbb C^n`$. For every unitary $`U`$,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This product invariant uses the vertex values and not the symplectic volume, which is proportional to the volume of the polytope. The rank here is vertex count, not the manifold dimension.

**Equivalence reduction.** Use a simplex moment polytope of dimension n-1 with n vertices (for n=1 use a point). Evaluate arbitrary complex functions on its distinct labelled vertices, not only affine-linear functions of them, and allow full complex unitary mixing.

## 117 Geometric invariant theory

Let two finite-dimensional complex representations of a one-parameter torus $`\mathbb C^\times`$ have equal dimension $`n`$. Their integer weight lists are $`a_j,b_j`$, repeated by weight-space dimension. For each $`z\in\mathbb C^\times`$ choose Hermitian products with mutually orthogonal weight spaces and let $`A(z),B(z)`$ be the operators of $`z`$ in these representations. For every unitary identification $`U`$ of their spaces,

```math
\det(A(z)+UB(z)U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(z^{a_j}+z^{b_{\pi(j)}}):\pi\in S_n\right\}.
```

The determinant characters of the individual actions are $`z^{\sum_j a_j}`$ and $`z^{\sum_j b_j}`$. This scalar evaluation of weights differs from the weight polytope used in stability criteria.

**Equivalence reduction.** Use a direct sum of n one-dimensional torus representations with distinct integer weights. At a fixed positive real torus parameter different from one their character values are distinct. Complex spectral functions assign arbitrary normal eigenvalues.

## 118 Contact geometry

Let two closed Reeb orbits of contact manifolds of dimension $`2r+1`$ have linearized return maps $`A,B`$ on identified transverse contact spaces of dimension $`n=2r`$. Assume the maps normal for a compatible positive Hermitian structure after complexification. Let $`\lambda_j,\mu_j`$ be their transverse eigenvalues. For each orthogonal symplectic change of frame $`Q`$,

```math
\det(A+QBQ^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The flow direction is excluded. Return maps preserve the transverse symplectic form and have determinant one; their sum need not be a return map.

**Equivalence reduction.** Use finite direct sums of transverse symplectic return-map realizations, selecting one complex spectral line in each reciprocal pair as needed. Evaluate arbitrary complex functions on those modes and use unrestricted complex relative unitaries. Actual contact return maps remain subject to their symplectic constraints.

## 119 Geometric quantization

Let two observables on a quantizable symplectic manifold be represented by normal operators $`A,B`$ on a common finite-dimensional complex quantum Hilbert space of dimension $`n`$. Let $`\lambda_j,\mu_j`$ be their quantum eigenvalues (real for self-adjoint observables). For every unitary $`U`$ of the Hilbert space,

```math
\det(A+UBU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

If the operators come from torus weights, use the eigenvalues after the specified scalar evaluation of those weights. No classical moment-map volume is substituted for the quantum determinant.

**Equivalence reduction.** Use finite quantum Hilbert spaces of arbitrarily large dimension, and normal diagonal observables or complex spectral evaluations of simple self-adjoint observables. Every normal matrix pair is then realized on the selected quantum modes.

## 120 Poisson geometry

Let $`x`$ be a common equilibrium of two Hamiltonian vector fields on a Poisson manifold, and fix its symplectic leaf of dimension $`n=2r>0`$. Let $`A,B`$ be their linearizations restricted to the tangent of the leaf. Assume normality for a fixed compatible positive inner product on the complexified leaf tangent. For their eigenvalues $`\lambda_j,\mu_j`$ and every orthogonal symplectic change of leaf frame $`Q`$,

```math
\det(A+QBQ^{-1})\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The statement is leafwise. It makes no identification of transverse Casimir directions with leaf eigenmodes.

**Equivalence reduction.** On a symplectic Euclidean leaf, use quadratic Hamiltonians giving direct sums of independent oscillator blocks. Select one eigenmode per block, evaluate arbitrary complex functions, and mix the selected modes by arbitrary complex unitaries.

## 121 Floer homology

Let a chosen Floer theory over $`\mathbb C`$ have a finite-dimensional degree-$`k`$ group $`V=HF^k`$ of dimension $`n>0`$. Let two defined continuation, symmetry or other compatible endomorphisms induce $`F,G`$ on $`V`$. Fix a Hermitian product for which $`F,G`$ are normal, and list their eigenvalues $`\lambda_j,\mu_j`$. For every unitary $`U`$ on $`V`$,

```math
\det_V(F+UGU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The determinant acts on the top exterior power of the Floer group. Action-filtration values are not eigenvalues of these maps.

**Equivalence reduction.** Choose finite Floer cohomology realizations and take finite direct sums of nonzero graded groups as needed. Select n labelled orthogonal cohomology modes and arbitrary complex evaluations. The unitary identifications act on these realized groups rather than on the nonlinear Floer data.

## 122 Maslov index theory

Let $`L_1,L_2`$ be Lagrangian subspaces of a real symplectic space of dimension $`2n`$ with compatible complex coordinates. Fix a reference Lagrangian and represent $`L_a`$ by its symmetric unitary matrix $`S_a=V_aV_a^T`$, where $`V_a`$ is a unitary frame carrying the reference to $`L_a`$. Let $`e^{i\theta_j},e^{i\phi_j}`$ be the eigenvalues of $`S_1,S_2`$. For every unitary $`U`$,

```math
\det(S_1+US_2U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(e^{i\theta_j}+e^{i\phi_{\pi(j)}}):\pi\in S_n\right\}.
```

The determinant is a complex phase-sensitive comparison of the unitary representatives. The Maslov index of a path counts signed crossings or winding; no convex bound on a chosen phase lift follows from the complex hull alone.

**Equivalence reduction.** Diagonal symmetric unitary matrices realize arbitrary diagonal phase lists, since each phase has a square root. Use distinct phases for n coordinates, evaluate arbitrary complex functions, and allow unrestricted relative complex unitaries on their normal representatives.

## 123 Hamiltonian integrable systems

Let $`(A_1,\ldots,A_r)`$ and $`(B_1,\ldots,B_r)`$ be commuting self-adjoint tuples of quantum integrals of motion on a finite-dimensional complex Hilbert space of dimension $`n`$. Let $`a_j,b_j\in\mathbb R^r`$ be their joint eigenvalues with multiplicity. For each scalar map $`L(x)=\sum_{\ell=1}^r c_\ell x_\ell`$ with $`c_\ell\in\mathbb C`$ and each unitary $`U`$,

```math
\det\left(\sum_{\ell=1}^r c_\ell(A_\ell+UB_\ell U^*)\right)\in\mathrm{conv}\left\{\prod_{j=1}^n L(a_j+b_{\pi(j)}):\pi\in S_n\right\}.
```

The weights may depend on $`c`$. Classical integral-value images without a quantum or other finite linear realization do not specify an operator determinant.

**Equivalence reduction.** Use one quantum integral of motion with n distinct real eigenvalues, apply arbitrary complex spectral functions on that one coordinate, and permit the full relative unitary group. This recovers the matrix conjecture; a common set of weights for every direction is not required.


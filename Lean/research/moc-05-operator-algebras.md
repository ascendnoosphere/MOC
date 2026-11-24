# Marcus-de Oliveira formulations: Operator algebras and noncommutative analysis

Atlas entries 049–060.

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

## 049 Banach-space operators

Let $`X`$ be a complex Banach space and $`A,B`$ bounded operators with finite-dimensional common invariant subspace $`E`$ of positive dimension $`n`$. Fix a Hilbert inner product on $`E`$ for which both restrictions are normal. Let $`\lambda_j,\mu_j`$ be the eigenvalues of the restrictions. For every unitary $`U:E\to E`$,

```math
\det_E(A|_E+UB|_EU^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The determinant uses the finite-dimensional action, not the entire Banach-space spectrum. The inner product is part of the data. For nuclear determinants on infinite spaces, a separate continuity and summability condition is necessary.

**Equivalence reduction.** Finite-dimensional complex Hilbert spaces are Banach spaces, so taking the full invariant subspace and the usual determinant recovers every matrix instance.

## 050 Hilbert-space operators

Let $`H`$ be a separable infinite-dimensional complex Hilbert space, and let $`A,B`$ be normal trace-class operators on $`H`$. Fix complete orthonormal eigenbases, and list their eigenvalues $`\lambda_j,\mu_j`$ with multiplicity (including zeros for kernel basis vectors). For every unitary $`U`$ on $`H`$, the Fredholm determinant form is

```math
\det_F(I+A+UBU^*)\in\overline{\mathrm{conv}}\left\{\prod_{j\ge1}(1+\lambda_j+\mu_{\pi(j)}):\pi\text{ a finite permutation of }\mathbb N\right\}.
```

The Fredholm determinant of $`I+C`$ for trace-class $`C`$ is the convergent eigenvalue product $`\prod_j(1+c_j)`$. Finite-rank approximation in trace norm and continuity of this determinant reduce the closed-hull formulation to the finite matrix conjecture. A finite permutation fixes all but finitely many indices.

**Equivalence reduction.** Use finite Hilbert spaces as well as the trace-class limit, or restrict to a selected finite spectral block and apply the determinant there. Shifting one input by minus the identity converts the finite Fredholm determinant to the ordinary sum determinant. The infinite closed hull alone is not used for the reverse implication.

## 051 Unital Banach algebra

Let $`\mathcal A`$ be a complex unital Banach algebra with a continuous unital homomorphism $`\rho:\mathcal A\to M_n(\mathbb C)`$. Let $`a,b`$ have normal images, and let $`\lambda_j,\mu_j`$ be the eigenvalues of those images. For every unitary $`u\in U(n)`$, the determinant associated with this representation satisfies

```math
\det(\rho(a)+u\rho(b)u^*)\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

Its additive trace is $`\mathrm{Tr}\rho(a)`$. If an intrinsic trace-associated determinant instead takes values modulo a period group, this complex hull requires an additional scalar realization.

**Equivalence reduction.** Take the Banach algebra of complex matrices with its identity representation. All normal matrix pairs occur.

## 052 Commutative C-star algebra C(X)

Let $`X`$ be a compact space, $`\nu`$ a probability measure on $`X`$, and $`f,g:X\to(0,\infty)`$ continuous. Write $`\mu_f=f_*\nu`$, $`\mu_g=g_*\nu`$ for the distributions. A coupling $`\gamma`$ is a probability measure on $`\mathbb R_{>0}^2`$ with these two marginals. Define $`D_\nu(h)=\exp(\int_X\log h\,d\nu)`$. Then

```math
D_\nu(f+g)\in\left[\inf_\gamma\exp\int\log(s+t)\,d\gamma(s,t),\ \sup_\gamma\exp\int\log(s+t)\,d\gamma(s,t)\right].
```

The actual joint distribution $`(f,g)_*\nu`$ is a coupling, so this is the commuting continuous version. For equal-mass atoms the extremal couplings are permutation matchings. Positivity fixes the logarithm; this does not define a complex determinant for arbitrary continuous functions.

**Equivalence reduction.** Use a finite discrete space with n points of equal mass. Complex scalar evaluation of its two function-value lists gives the normal diagonal multiplication operators. Allow arbitrary relative unitary positions of those multiplication operators; the actual commuting integral is only a coupling specialization.

## 053 Unital C-star algebra

Let $`\mathcal A`$ be a unital complex C-star algebra and $`\rho:\mathcal A\to M_n(\mathbb C)`$ a unital adjoint-preserving representation. For normal $`a,b\in\mathcal A`$, let $`\lambda_j,\mu_j`$ be the spectra with multiplicity of $`\rho(a),\rho(b)`$. For every unitary $`u\in\mathcal A`$,

```math
\det(\rho(a+ubu^*))\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

This is the classical conjecture in each finite-dimensional representation. An algebra without such a representation needs a separate determinant, as in the tracial formulation below.

**Equivalence reduction.** Take the C-star algebra of complex matrices with its identity representation, in all orders. This recovers the matrix conjecture.

## 054 Normal C-star element

Let $`a,b`$ be normal in a unital C-star algebra with a finite-dimensional unital adjoint-preserving representation $`\rho`$ of dimension $`n`$. For any continuous $`f:\sigma(a)\to\mathbb C`$, $`g:\sigma(b)\to\mathbb C`$, let $`\lambda_j,\mu_j`$ be the represented eigenvalues of $`a,b`$. For every unitary $`U`$ on the representation space,

```math
\det(\rho(f(a))+U\rho(g(b))U^*)\in\mathrm{conv}\left\{\prod_{j=1}^n(f(\lambda_j)+g(\mu_{\pi(j)})):\pi\in S_n\right\}.
```

Continuous functional calculus preserves normality and gives the stated spectral values. Taking the identity functions gives the matrix form.

**Equivalence reduction.** Already equivalent by taking the matrix algebra and identity functions on its two spectra. Arbitrary continuous functions add no stronger requirement.

## 055 Finite von Neumann algebra

Let $`(\mathcal M,\tau)`$ be a finite von Neumann algebra with faithful normal tracial state $`\tau(1)=1`$. Let $`a,b`$ be positive invertible elements and let $`\nu_a,\nu_b`$ be their spectral probability measures under $`\tau`$. Write $`\Gamma(\nu_a,\nu_b)`$ for the set of probability couplings of these measures. For every unitary $`u\in\mathcal M`$, formulate the Fuglede-Kadison determinant version as

```math
\inf_{\gamma\in\Gamma(\nu_a,\nu_b)}\exp\int\log(s+t)\,d\gamma\ \le\ \Delta_\tau(a+ubu^*)\ \le\ \sup_{\gamma\in\Gamma(\nu_a,\nu_b)}\exp\int\log(s+t)\,d\gamma,
```

where $`\Delta_\tau(x)=\exp(\tau(\log|x|))`$. For normalized matrix trace the bounds are the positive $`n`$th roots of the extreme permutation products. This determinant retains the modulus, not the complex phase.

**Equivalence reduction.** Use finite matrix factors among finite von Neumann algebras and their positive, distinct-spectrum elements. Evaluate arbitrary complex functions of their spectral projections and use the ordinary complex determinant in these factors. The normalized Fuglede-Kadison determinant alone retains no phase.

## 056 Type II1 factor

Let $`\mathcal M`$ be a type II1 factor (a finite factor with diffuse projection ranks) with normalized trace $`\tau`$. Let $`a=\sum_i\lambda_i p_i`$ and $`b=\sum_j\mu_j q_j`$ be finite-spectrum positive invertible elements with orthogonal spectral projections summing to one. Define the transportation polytope $`\mathcal T=\{m_{ij}\ge0:\sum_j m_{ij}=\tau(p_i),\sum_i m_{ij}=\tau(q_j)\}`$. For every unitary $`u`$ the formulation is

```math
\Delta_\tau(a+ubu^*)\in\mathrm{conv}\left\{\exp\left(\sum_{i,j}m_{ij}\log(\lambda_i+\mu_j)\right):m\in\mathcal T\right\}.
```

The real masses are normalized projection dimensions. In the diffuse factor the commuting configurations can realize such masses by splitting projections. In a matrix factor integer rank constraints give the original positive matrix matching interval after normalization.

**Equivalence reduction.** In a type II1 factor choose n equivalent orthogonal projections summing to one and matrix units between them. They form a unital matrix subalgebra. Complex evaluation of finite spectral resolutions and the ordinary determinant on that subalgebra recover the full matrix conjecture. The positive trace determinant is the modulus specialization.

## 057 Semifinite von Neumann algebra

Let $`(\mathcal M,\tau)`$ have a faithful normal semifinite trace. Fix a projection $`p`$ with $`0<d=\tau(p)<\infty`$. Let $`a,b`$ be positive invertible in the corner $`p\mathcal Mp`$, with unit $`p`$. Let $`\nu_a,\nu_b`$ be their spectral measures for $`\tau/d`$. For every unitary $`u`$ of the corner, with $`\Gamma`$ the set of probability couplings of these measures,

```math
\exp\left(d^{-1}\tau(\log(a+ubu^*))\right)\in\left[\inf_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma,\ \sup_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma\right].
```

The logarithm is calculated in the finite-trace corner, not on the full infinite-trace identity.

**Equivalence reduction.** Choose a finite matrix subalgebra in a finite-trace corner, with the determinant in that subalgebra. Allow the semifinite algebra and corner to vary, so all matrix orders occur. The real trace-log formula does not retain complex phase.

## 058 Group von Neumann algebra

Let $`G`$ be a discrete group and $`\mathcal N G`$ its group von Neumann algebra on $`\ell^2(G)`$, with trace $`\tau(x)=\langle x\delta_e,\delta_e\rangle`$. Let $`a,b`$ be positive invertible convolution operators with spectral probability measures $`\nu_a,\nu_b`$. For each unitary $`u\in\mathcal N G`$ and the set $`\Gamma`$ of probability couplings of $`\nu_a,\nu_b`$, the log-determinant comparison is

```math
\tau(\log(a+ubu^*))\in\left[\inf_{\gamma\in\Gamma}\int\log(s+t)\,d\gamma,\ \sup_{\gamma\in\Gamma}\int\log(s+t)\,d\gamma\right].
```

Exponentiation gives the corresponding Fuglede-Kadison determinant interval. For a finite group the regular representation supplies a finite matrix specialization.

**Equivalence reduction.** Take finite cyclic groups of arbitrary order. Their Fourier spectral coordinates permit arbitrary complex convolution values. Use the ordinary determinant of the finite regular representation and unrestricted relative unitary position in that representation.

## 059 Free probability

Let $`(\mathcal M,\tau)`$ be a tracial von Neumann probability space with faithful normalized trace. Let $`a,b`$ be freely independent positive invertible self-adjoint variables, with compactly supported probability laws $`\nu_a,\nu_b`$. Write $`\nu_a\boxplus\nu_b`$ for their free additive convolution, that is, the law of $`a+b`$. If $`\Gamma`$ denotes the classical probability couplings of the two laws, the free determinant comparison is

```math
\exp\int\log x\,d(\nu_a\boxplus\nu_b)(x)\in\left[\inf_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma,\ \sup_{\gamma\in\Gamma}\exp\int\log(s+t)\,d\gamma\right].
```

This compares a noncommutative sum with commuting couplings. For nonnormal variables the Brown measure and the absolute determinant do not in general give a complex determinant hull.

**Equivalence reduction.** Use the finite-dimensional tracial matrix realization with normalized trace, and evaluate complex functions on arbitrary simple spectra. Permit arbitrary relative positions instead of requiring free independence. Free independence and the positive trace-log formula alone cannot recover the general complex determinant.

## 060 Calkin algebra

Let $`H`$ be an infinite-dimensional separable Hilbert space, $`\mathcal Q(H)=\mathcal B(H)/\mathcal K(H)`$ its Calkin algebra, and $`q`$ the quotient map. Fix a unital matrix subalgebra $`\mathcal F\subset\mathcal Q(H)`$ and an adjoint-preserving isomorphism $`\rho:\mathcal F\to M_n(\mathbb C)`$. Suppose $`q(A),q(B)\in\mathcal F`$ are normal, with represented eigenvalues $`\lambda_j,\mu_j`$. For each unitary $`v\in\mathcal F`$,

```math
\det(\rho(q(A)+vq(B)v^*))\in\mathrm{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.
```

The determinant is confined to the specified finite subalgebra and is insensitive to compact perturbations of the lifts. The full Calkin algebra has no ordinary scalar determinant of all elements. The Fredholm index is not such a determinant.

**Equivalence reduction.** For each n the Calkin algebra contains a unital copy of the n by n complex matrices, obtained by amplifying a matrix on an infinite-dimensional multiplicity space and passing to the quotient. This copy is faithful since no nonzero amplified matrix is compact. Use its ordinary matrix determinant.


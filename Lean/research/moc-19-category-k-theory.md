# Marcus-de Oliveira formulations: Category theory, K-theory and quantum algebra

Atlas entries 220–231.

All eigenvalue lists use the indicated multiplicities. $S_n$ is the set of permutations of $\{1,\ldots,n\}$; $U(n)$ is the complex unitary group; $*$ is the Hermitian adjoint. The convex hull uses real nonnegative weights of sum one. The Marcus-de Oliveira conjecture asserts that the determinant of the sum of two normal complex operators with fixed eigenvalues lies in the convex hull of products of pairwise matched eigenvalue sums. The statements below specify the spectral data, determinant and necessary scalar realization for each setting.

## 220 Rigid symmetric monoidal categories

Let $\mathcal C$ be a complex-linear rigid symmetric monoidal category with a symmetric monoidal realization functor $F$ into finite-dimensional complex vector spaces. Choose a dualizable object $X$ of realized dimension $n>0$ and a Hermitian product on $F(X)$. For endomorphisms $a,b:X\to X$ with normal images $A=F(a),B=F(b)$ and eigenvalues $\lambda_j,\mu_j$, for every unitary $U$ on $F(X)$,

$$\det(F(a)+UF(b)U^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The categorical trace is preserved by the realization; the determinant is the scalar on the top exterior line of the realized object. Categorical dimension alone does not define a scalar spectrum.

## 221 Additive and abelian categories

Let $\mathcal C$ be a complex-linear abelian category with a specified additive linear realization $F$ into finite-dimensional complex vector spaces. Choose an object $X$ with $V=F(X)$ of dimension $n>0$ and endomorphisms $a,b$ with normal images $A,B$ for a fixed Hermitian product. Let $\lambda_j,\mu_j$ list their eigenvalues. For every unitary $U$ of $V$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The determinant functor, if used, must realize to the ordinary scalar on the determinant line of $V$. Composition length of $X$ need not equal $n$.

## 222 Stable homotopy theory

Let $X$ be a finite spectrum (a finite cell object of the stable homotopy category). In a fixed degree $k$ with $V=H_k(X;\mathbb C)$ of finite positive dimension $n$, choose two stable self-maps $f,g$ whose induced linear maps $A,B$ are normal for a fixed Hermitian product. For their eigenvalues $\lambda_j,\mu_j$ and every unitary $U$ on $V$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This is the ordinary homological realization of stable endomorphisms. A homotopy spectrum is not a list of eigenvalues. The categorical trace of a stable map uses Euler signs across degrees and cannot replace the positive length $n$.

## 223 Algebraic K0

Let $R$ be a commutative unital ring with a chosen homomorphism $x:R\to\mathbb C$, and let $P,Q$ be finite projective $R$-modules, whose actual classes belong to $K_0(R)$. Assume their fibers $P_x,Q_x$ both have dimension $n>0$. Let $a,b$ be module endomorphisms whose fiber maps $A,B$ are normal for chosen Hermitian products, with eigenvalues $\lambda_j,\mu_j$. For every unitary identification $U:Q_x\to P_x$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This is the determinant comparison on actual projective representatives. The virtual class $[P]-[Q]$ has signed rank and its determinant line is $\det P\otimes(\det Q)^*$. For a pair of invertible realized endomorphisms its scalar is a ratio, not a positive-dimensional permutation product.

## 224 Algebraic K1

Let $R$ be a unital ring with a unital homomorphism $x:R\to\mathbb C$. Let $a,b\in GL_n(R)$ be automorphisms representing classes in $K_1(R)$, and let their complex images $A=x(a),B=x(b)$ be normal. With eigenvalues $\lambda_j,\mu_j$, for every $U\in U(n)$ such that $C=A+UBU^*$ is invertible,

$$\det(C)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The determinant is the scalar image of the class $[C]$ in $K_1(\mathbb C)\simeq\mathbb C^\times$. The statement concerns fixed finite representatives; addition of matrices is not the group operation on $K_1$. Singular sums remain in the ordinary matrix conjecture but have no invertible $K_1$ class.

## 225 Whitehead torsion

Let $G$ be a group and $\rho:G\to U(d)$ a finite-dimensional unitary representation, extended linearly to $\mathbb Z[G]$. Let $a,b\in GL_r(\mathbb Z[G])$ be two chosen automorphism matrices representing Whitehead torsion data. Assume their block realizations $A=\rho(a),B=\rho(b)$ are normal and invertible on $\mathbb C^{n}$ with $n=rd$. Let $\lambda_j,\mu_j$ be their eigenvalues. For every unitary $U$ with $A+UBU^*$ invertible,

$$\det_{\mathbb C}(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The representation determinant of a fixed torsion matrix is a scalar; its modulus removes the ambiguity from the units $\pm g$ in the Whitehead quotient under a unitary representation. The sum need not represent a Whitehead class over the group ring. No addition on abstract Whitehead classes is assumed.

## 226 Topological K-theory

Let $E,F$ be complex Hermitian vector bundles over a compact space $X$, representing actual classes of topological $K^0(X)$, with the same positive rank $n$. Fix a point $x$ and bundle endomorphisms $a,b$ with normal fiber maps $A=a_x,B=b_x$. For their eigenvalues $\lambda_j,\mu_j$ and every unitary identification $U:F_x\to E_x$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

This is the fiberwise determinant-line scalar. Virtual bundle differences use tensor products of determinant lines with inverses, while the Chern character is additive; neither supplies a positive spectral list without actual representatives.

## 227 Fusion categories

Let $\mathcal C$ be a fusion category with $n>0$ simple objects $X_i$. On the complexified Grothendieck ring with orthonormal simple basis let $N_a,N_b$ be fusion matrices for two objects: $(N_a)_{ij}$ is the multiplicity of $X_i$ in $a\otimes X_j$. Assume $N_a,N_b$ are normal, for example in a commutative fusion ring with the usual duality involution. Let $\lambda_j,\mu_j$ be their complex eigenvalues. For every unitary $U$ of the simple-object coordinate space,

$$\det(N_a+UN_bU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

Frobenius-Perron dimensions describe distinguished positive eigenvalues, not all spectral values. The permutation length is the number of simple objects, not their total categorical dimension.

## 228 Modular tensor categories

Let two modular tensor categories have the same number $n>0$ of simple objects, and choose their normalized modular representations on the complex simple-object coordinate spaces. Let $A,B$ be any two normal modular operators of size $n$, for example their diagonal twist matrices $T$ (or unitary modular $S$ matrices in unitary categories). With complex eigenvalues $\lambda_j,\mu_j$ and every unitary identification $U$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The determinant uses the modular representation matrices. Individual and total quantum dimensions are separate invariants and do not determine the full spectrum of $S$ or $T$.

## 229 Quantum groups

Let two finite-dimensional type-one representations of a quantum group have the same complex dimension $n>0$ and a fixed complex deformation parameter $q$ for which the weight decompositions exist. Fix a Cartan weight operator $K_h$ acting by $q^{\langle h,a_j\rangle}$ and $q^{\langle h,b_j\rangle}$ on orthogonal weight spaces of the two representations (use integral weights and a specified torus character). Let $A,B$ denote these normal realized actions. For each unitary identification $U$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^n(q^{\langle h,a_j\rangle}+q^{\langle h,b_{\pi(j)}\rangle}):\pi\in S_n\right\}.$$

The determinant is the ordinary determinant of the representation; it is not the noncommutative quantum determinant in an RTT algebra. A quantum trace or dimension with noninteger weights cannot be substituted for the ordinary spectral multiplicities.

## 230 Hopf algebras

Let $H,K$ be finite-dimensional complex Hopf algebras of equal dimension $n>0$. Choose normal realized endomorphisms $A,B$, for example their antipodes if the antipodes are normal in specified Hermitian products. Let $\lambda_j,\mu_j$ be the linear eigenvalues with multiplicity. For every unitary identification $U:K\to H$,

$$\det(A+UBU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

The left side is the ordinary determinant of the combined linear action. The sum need not be a Hopf morphism. Group-like determinant coefficients in a coalgebra are not used as complex numbers without realization.

## 231 Coalgebras and comodules

Let $C$ be a complex coalgebra and $V,W$ finite-dimensional right comodules of common dimension $n>0$. Let $f:V\to V$, $g:W\to W$ be comodule endomorphisms normal for specified Hermitian products, with eigenvalues $\lambda_j,\mu_j$. For every unitary identification $U:W\to V$,

$$\det(f+UgU^*)\in\operatorname{conv}\left\{\prod_{j=1}^{n}(\lambda_j+\mu_{\pi(j)}):\pi\in S_{n}\right\}.$$

If $U$ intertwines the comodule structures the sum is a comodule endomorphism. The scalar determinant is its action on the top exterior space of the underlying vector space, whether or not a comodule exterior construction exists.

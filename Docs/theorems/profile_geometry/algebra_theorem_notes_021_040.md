## Round 021 — Recover actual finite spectra, including zero matching coordinates

### Proposed obligation

The real PSD test previously recovered a singular point of the cubic. Show that this point is represented by actual finite spectra, rather than only by a limiting spectral configuration.

### Derivation

Let 0≠x lie in the affine cone over Sing C=M8. The projective GIT quotient map is surjective, so its projective class is represented by a semistable ordered configuration of eight points on P¹. Choose nonzero lifts v_1,…,v_8.

There is a common projective coordinate change A whose pole avoids all eight points. Thus every second coordinate γ_i of Av_i is nonzero. Normalize the lifts to

\[
w_i=\frac{Av_i}{\gamma_i}=(t_i,1).
\]

For every perfect matching μ, its four-bracket invariant transforms by the same factor:

\[
\prod_{\{i,j\}\in\mu}[w_i,w_j]
=\frac{(\det A)^4}{\prod_{i=1}^8\gamma_i}
\prod_{\{i,j\}\in\mu}[v_i,v_j].
\]

The factor is independent of μ. For the bipartite matching coordinates set a_i=t_i and b_j=−t_{4+j}. Their brackets are a_i+b_j. Consequently there is a single ρ∈C* such that

\[
\boxed{x=\rho\,z(a,b)}
\]

with every a_i and b_j finite. Repeated points and zero individual brackets cause no difficulty: no bracket was divided out.

If the cubic polarization test gives x=(c+id)/2, then

\[
c=x+\bar x=\operatorname{Re}(2\rho z(a,b)).
\]

### Result and remaining issue

The singular-cubic recovery is an exact finite-spectrum recovery on every nonzero point of the cone. The remaining issue is positivity against actual unitary moments, not a hidden closure or reconstruction gap.

## Round 022 — A coordinate-free PSD lift, with the cubic equation automatic

### Proposed mechanism

Remove the denominators and choices involved in a kernel basis N.

Define the linear map Γ:Sym₁₄(R)→R¹⁴ by

\[
\Gamma(X)_j=\frac12\operatorname{tr}(H(e_j)X).
\]

Consider

\[
\boxed{X\succeq0,\qquad H(c)X=0,\qquad \Gamma(X)=G(c).}
\tag{22.1}
\]

### Derivation

The equation H(c)X=0 places the image of X in ker H(c). On the rank-twelve stratum, X=NTNᵀ for a symmetric PSD 2×2 matrix T, and (22.1) becomes exactly L(T)=G(c).

There is also an automatic equation:

\[
3C(c)=c\cdot G(c)
=c\cdot\Gamma(X)
=\frac12\operatorname{tr}(H(c)X)=0.
\]

Thus (22.1), together with rank H(c)=12, places c on C=0 and its Hessian hypersurface. The established reduced-support theorem places c on the secant variety. The proved conormal rank bound then gives rank L≤2, and the PSD rank reduction gives a rank-one feasible lift ddᵀ.

It follows that, for an arbitrary real c with rank H(c)=12,

\[
\boxed{\text{(22.1) is feasible}
\iff c=\operatorname{Re}(\eta z(a,b))
\text{ for finite spectra}.}
\]

### Limitation

For larger Hessian kernels, a feasible higher-rank X need not reduce to rank one by this argument. The coordinate-free test is exact on the rank-twelve stratum. Round 039 supplies an all-strata formulation using a vector d instead.

## Round 023 — Repair the homogeneity of the coupled PSD certificate

### Proposed mechanism

Prove full support positivity by combining the spectral PSD lift with genuine unitary Gram matrices.

### Obstruction and corrected template

Under positive scaling,

\[
g\mapsto rg,\quad c\mapsto rc,\quad X\mapsto r^2X.
\]

The support deficit F_U(g) has degree one in the cost. A term

\[
\operatorname{tr}(W[X\otimes G_U])
\]

with a cost-independent W has degree two. Therefore an unnormalized identity equating these quantities cannot be a universal certificate. This rules out a naive version of the previous coupled-PSD proposal.

For Rg≥0 use the nonnegative homogeneous gauge

\[
\rho(g)=\sum_{\pi\in S_4}(Rg)_\pi.
\]

If ρ=0, every full cost coordinate is zero, so F_U(g)=0. Otherwise a degree-compatible sufficient certificate is

\[
\begin{aligned}
\rho(g)F_U(g)
={}&\sum_{\pi,\sigma}a_{\pi\sigma}(U)
(Rg)_\pi(Rg)_\sigma\\
&+\sum_k\operatorname{tr}
\left(W_k[X\otimes G_{U,k}]\right)
+\text{terms vanishing on the defining equations},
\end{aligned}
\tag{23.1}
\]

where a_{\pi\sigma}(U)≥0 on the unitary group, W_k≥0, and G_{U,k} are Gram matrices of actual rows, columns, or compound vectors.

Every displayed nonvanishing term is nonnegative. Hence such an identity would prove MOC on the regular sector, and then everywhere in dimension four by the density argument already established.

### Status

The homogeneity repair is proved. An identity of the form (23.1) has not been constructed. The Gram matrices must come from the same actual unitary; independent p/q coordinates do not impose that compatibility.

## Round 024 — Determine exactly what external-vertices positivity controls

### Obligation

Can Drury’s theorem already imply the full convex hull after a geometric reinterpretation?

### Derivation

Let H=conv{z_π} and suppose 0∉H. The halfspaces tested by external-vertices positivity are

\[
\ell(z_\pi)\ge1\quad\forall\pi
\quad\Longrightarrow\quad \ell(d)\ge1.
\]

Intersecting these halfspaces gives the outward radial convex hull

\[
\boxed{\{r y:r\ge1,\ y\in H\}.}
\tag{24.1}
\]

Indeed every r y satisfies each such lower bound. Conversely a point outside that closed convex radial set is separated by a linear functional whose positive minimum on H can be normalized to one.

The set in (24.1) permits outward overshooting. For example take the real triangle

\[
H=\operatorname{conv}\{1+i,1-i,2\}.
\]

The point d=3 belongs to its outward radial hull and satisfies every external halfspace, while d∉H.

### Result

EVC is a lower bound on how far a determinant can lie from the origin along an allowed ray. It does not provide the outer support bound. In particular it does not imply membership in conv({0}∪H). The example is a convex-geometric obstruction to that deduction, not an actual spectral/unitary counterexample.

## Round 025 — EVC removes one sign of the affine center

### Proposed mechanism

Use the exact affine center h, rather than attempt an unsupported translation of the spectral products.

### Derivation

Suppose g=h e+c has nonnegative permutation coordinates, where c is an actual real spectral cost.

If h<0, then

\[
c_\pi\ge-h>0.
\]

Drury’s theorem applied after positive scaling gives

\[
F_U(c)\ge-h,
\]

and hence F_U(g)=h+F_U(c)≥0. This directly handles h<0. If a strict violation had h=0, replacing h by a sufficiently small positive ε would retain every vertex inequality and the negative deficit.

Therefore any counterexample would imply one satisfying

\[
\boxed{h>0.}
\tag{25.1}
\]

On the regular affine chart, h=C(g)/Q(g). It is therefore enough to search for, or exclude, violating costs with C(g)/Q(g)>0. This does not claim a separate proof at h=0 from an unjustified translation of spectral vertices.

Positive homogeneity permits h=1 in the remaining region. The missing assertion becomes

\[
c_\pi\ge-1\quad\forall\pi
\quad\Longrightarrow\quad F_U(c)\ge-1.
\]

### Status

This cleanly separates the solved external part from the unresolved internal threshold. Changing the sign of c changes lower bounds into upper bounds and does not turn this last assertion into EVC.

## Round 026 — Compute the fermionic compression exactly on every weight sector

### Proposed mechanism

Make the all-n qubit operator concrete enough to use representation theory.

Let

\[
K_U=J^*\Lambda^n(U\otimes I_2)J,
\]

where J sends a product of n qubits to the wedge with one particle in each spatial mode.

### Derivation

Index the computational basis of weight k by subsets S,T⊂{1,…,n} of size k. Since U does not change the qubit label, the corresponding amplitude factors into the two color sectors:

\[
(K_U)_{S,T}
=\varepsilon(S,T)\det U[S,T]\det U[S^c,T^c].
\]

Jacobi’s complementary-minor identity for a unitary matrix states

\[
\det U[S^c,T^c]
=\varepsilon(S,T)\det U\,
\overline{\det U[S,T]}.
\]

The signs cancel. Thus

\[
\boxed{\left(K_U/\det U\right)_{S,T}
=|\det U[S,T]|^2.}
\tag{26.1}
\]

Different weights do not couple. Every weight block is the entrywise squared modulus of a unitary compound matrix, hence is doubly stochastic.

### Result and obstruction

All-n MOC is a product-state matrix-coefficient assertion for this exact block operator. Applying Birkhoff separately to the blocks permits arbitrary bijections of k-subsets. Those bijections need not be induced by one permutation of the original n sites. The known failure of common-minor laws is exactly an obstruction to synchronizing these block decompositions.


## Round 028 — Prove that direct-sum ancillas cannot activate the failure

### Proposed mechanism

Attach an auxiliary block carrying an additional spectral factor.

### Proof

Let U=U_1⊕U_2 and partition the spectra accordingly. The actual determinant factors:

\[
d=d_1d_2.
\]

If each block obeys MOC, write

\[
d_1=\sum_\pi\lambda_\pi z_\pi^{(1)},\qquad
d_2=\sum_\sigma\mu_\sigma z_\sigma^{(2)}
\]

with nonnegative weights of total mass one. Then

\[
d=\sum_{\pi,\sigma}\lambda_\pi\mu_\sigma
z_\pi^{(1)}z_\sigma^{(2)}.
\]

Each product is a full-size permutation product for the block-preserving permutation π⊕σ. These are included among all full-size vertices.

### Result

A block-diagonal unitary cannot turn blocks satisfying MOC into a counterexample, regardless of the spectra chosen in the different blocks. Repetition, independent copies, and scalar direct-sum ancillas all obey this no-activation result.


## Round 030 — Rank-two additive zeros have a rigid graph structure

### Proposed mechanism

Use zeros to route permutations through selected ancilla channels.

### Derivation

For an additive representative M_ij=a_i+b_j,

\[
M_{ij}=0\iff a_i=-b_j.
\]

Thus the zero set is a union of complete bipartite graphs between row and column classes with matching spectral values.

Two immediate consequences are

\[
M_{ij}=M_{ik}=0\ \Longrightarrow\ b_j=b_k,
\]

so the entire columns j and k agree; and

\[
M_{ij}=M_{\ell j}=0\ \Longrightarrow\ a_i=a_\ell,
\]

so the entire rows i and ℓ agree. Nonzero row-column gauges preserve the zero graph.

### Result

Arbitrary selector graphs cannot be embedded into a generic rank-two matching matrix by choosing spectral zeros. Requiring two zero edges incident at a vertex already creates a whole equality class. Any coherent-routing construction must respect this algebraic restriction.

## Round 031 — A cross-spectrum exchange changes compact unitarity into indefinite unitarity

### Proposed mechanism

The eight-point spectral variety has S8 symmetry. Exchange one point from the A spectrum with one from the negative B spectrum, and track the actual scattering matrix.

Write

\[
U=\begin{pmatrix}u&r\\c&D\end{pmatrix},\qquad u\ne0.
\]

If y=Ux, exchange the input coordinate x_1 with the output coordinate y_1. The new input and output are

\[
\widetilde x=(y_1,x'),\qquad
\widetilde y=(x_1,y').
\]

Solving the first equation for x_1 gives

\[
\boxed{
V=
\begin{pmatrix}
1/u&-r/u\\
c/u&D-cr/u
\end{pmatrix}.}
\tag{31.1}
\]

### Exact signature calculation

Original unitarity says |y_1|²+||y'||²=|x_1|²+||x'||². After the exchange this becomes

\[
\widetilde y^*J\widetilde y
=\widetilde x^*J\widetilde x,\qquad
J=\operatorname{diag}(-1,1,\ldots,1).
\]

Hence V*JV=J. Generically V is not compact unitary: |V_{11}|=1/|u|>1 when |u|<1.

### Result

The natural scattering realization of this extra S8 symmetry lands in U(n−1,1). Full bracket symmetry cannot be applied while retaining the original positive moment cone without an additional argument.

## Round 032 — Exact determinant covariance under the signature-changing swap

### Obligation

Determine whether the exchange merely resembles a symmetry or gives a precise determinant identity.

Set

\[
a'_1=-b_1,\quad b'_1=-a_1,
\]

and leave all other a_i,b_j unchanged. Let M_ij=a_i+b_j and M'_ij=a'_i+b'_j.

### Proof

Define

\[
L=\begin{pmatrix}-1/u&0\\-c/u&I\end{pmatrix},
\qquad
R_0=\begin{pmatrix}1/u&-r/u\\0&I\end{pmatrix}.
\]

A block multiplication gives

\[
\boxed{V\circ M'=L(U\circ M)R_0.}
\tag{32.1}
\]

For example, the lower-right correction is
−c_i r_j(a_i+b_j)/u, exactly the correction in V_ijM'_ij. Therefore

\[
\det(V\circ M')=-\frac{\det(U\circ M)}{u^2}.
\]

The pivot has determinant det V=det D/u. For unitary U, the cofactor identity gives det D=det U\,\bar u. Consequently

\[
\boxed{
\frac{\det(V\circ M')}{\det V}
=-\frac1{|u|^2}
\frac{\det(U\circ M)}{\det U}.}
\tag{32.2}
\]

### Result

This is a genuine, exact spectral/scattering duality. It includes both a sign reversal and a positive amplification. The indefinite metric in Round 031 is the substantive cost of the exchange.


## Round 034 — Derive the optimal local 2×2 Gram repair

### Proposed mechanism

Pair the spectral PSD matrix with a genuine two-vector unitary Gram matrix.

Let

\[
T=\begin{pmatrix}a&b\\b&c\end{pmatrix}\succeq0,\qquad
G_0=\begin{pmatrix}r&z\\\bar z&s\end{pmatrix}\succeq0.
\]

Then

\[
\begin{aligned}
ar+cs-2b\operatorname{Re}z
&\ge ar+cs-2|b||z|\\
&\ge ar+cs-2\sqrt{acrs}\\
&=(\sqrt{ar}-\sqrt{cs})^2\ge0.
\end{aligned}
\tag{34.1}
\]

Equivalently, this is the quadratic form of T⊗G_0 at the vector (1,0,0,−1).

### Optimality

For a coefficient matrix

\[
B=\begin{pmatrix}\lambda&\nu\\\bar\nu&\mu\end{pmatrix},
\]

the pairing tr(BG_0) is nonnegative for every PSD G_0 if and only if

\[
\lambda\ge0,\qquad \mu\ge0,\qquad
\lambda\mu\ge|\nu|^2.
\]

Necessity follows by taking rank-one G_0 from a negative eigenvector whenever B is not PSD. Thus the determinant bound on the cross coefficient cannot be weakened.

### Status

This is an exact local dual primitive for (23.1). The unresolved task is an identity matching the actual signed-law deficit to a sum of these primitives with coefficients controlled by spectral PSD. Pairing separately feasible spectra and separately feasible linear p/q moments does not supply that identity.

## Round 037 — The value–curvature identity exposes the remaining sign problem

### Proposed mechanism

Exclude negative support minima by studying a fixed-gradient fiber.

Assume the fiber through c is smooth with tangent ker H(c), let N be a basis of this kernel, and let ℓ be stationary on the fiber:

\[
\ell N=0.
\]

Choose the symmetric Hessian pseudoinverse H† on im H(c), and define

\[
B=L^*(H^\dagger\ell).
\]

### Exact identities

If a fiber curve has tangent n=Nt, differentiating G(x)=G(c) twice gives

\[
H(c)x''=-2G(n).
\]

Since ℓ annihilates the kernel, its fiber Hessian is

\[
\boxed{\operatorname{Hess}_{\rm fiber}\ell=-2B.}
\]

If T is a spectral PSD recovery matrix, then L(T)=G(c). Euler polarization gives H(c)c=2G(c), and therefore

\[
\boxed{\ell\cdot c=2\operatorname{tr}(BT).}
\tag{37.1}
\]

A local minimum requires −B≥0 in unconstrained fiber directions. Together with T≥0 this implies ℓc≤0, which is compatible with a negative violation. It does not prove the desired opposite sign.

In a recovered basis whose first vector is d with G(d)=G(c), take T=diag(1,0). Then B₁₁=ℓc/2. The exact phase circle

\[
c_\theta=c\cos\theta+d\sin\theta,\qquad
G(c_\theta)=G(c)
\]

has second derivative −ℓc. A negative value is automatically positively curved in this direction.

### Sharp remaining obligation

An escape argument must control the other, quadric-pencil direction. At an unconstrained stationary negative point, det B<0 would make the fiber Hessian indefinite and exclude a local minimum. There is no proof that actual unitary moments force this determinant sign.

With active inequalities Rg≥0, only the feasible critical tangent cone is relevant; an indefinite ambient Hessian is insufficient unless its descending direction is feasible. Boundary support minima and nongeneric fibers remain additional obligations.

## Round 038 — Higher fiber jets give a further exact obstruction to flat minima

### Proposed mechanism

If the quadratic curvature is only semidefinite, test the next nonzero term instead of declaring the argument exhausted.

Write an actual smooth fixed-gradient curve as

\[
x(t)=c+tn+t^2v+t^3w+O(t^4).
\]

Quadratic polarization of G yields the successive identities

\[
H(c)n=0,
\]

\[
H(c)v=-G(n),
\]

\[
H(c)w=-H(n)v.
\tag{38.1}
\]

At a stationary ℓN=0,

\[
\ell v=-\ell H^\dagger G(n),\qquad
\ell w=-\ell H^\dagger H(n)v.
\]

If ℓv=0 but ℓw≠0, the first nonzero change is odd in t. Such a two-sided feasible curve cannot pass through a local minimum.

### Result and limit

This produces a concrete higher-order test on the null direction of the 2×2 curvature matrix. It does not assume the polar fiber is a linear plane.

The equations are conditions on actual smooth fiber curves. Solving only the displayed truncated linear equations does not guarantee that a formal jet extends, and an active support inequality can remove one side of the curve. No universal nonvanishing theorem for the cubic term has been proved.

## Round 039 — An exact compact polynomial formulation covers every exceptional stratum

### Proposed mechanism

Eliminate the regular-chart denominators and the higher-corank PSD gap without returning to unbounded spectral parameters.

Use real variables h,c,d and real and imaginary entries of U. Impose

\[
U^*U=I,
\]

\[
H(c)d=0,\qquad G(d)=G(c),
\]

\[
R(h e+c)\ge0,
\]

\[
\boxed{h^2+\|c\|^2+\|d\|^2=1.}
\tag{39.1}
\]

### Equivalence proof

The two cubic-polarization equations are equivalent to

\[
G((c+id)/2)=0.
\]

Round 021 therefore recovers actual finite spectra up to a common complex scalar whenever (c,d)≠(0,0). If both vanish, the remaining constant cost is harmless.

Conversely every actual spectral cost admits a d with these equations. A positive common scaling of h,c,d preserves all sign conditions and the sign of F_U(h e+c), and enforces the normalization unless the entire cost representation is zero.

Thus MOC in dimension four is equivalent to nonnegativity of the polynomial objective F_U(h e+c) on the compact real algebraic set (39.1) with the displayed inequalities. Compactness follows from the normalization and unitary constraints. The moment functional can be expressed polynomially through squared minors of U.

### Result

This formulation includes Q=0, higher Hessian corank, repeated spectral points, and vanishing matching coordinates. Unlike the unrestricted matrix lift X≥0, it retains rank one through the vector d and introduces no false real branch.

It is an exact global target for a polynomial certificate, not itself such a certificate.


## Round 001 — Elliptic lines of the cubic polar map

### Proposed mechanism

Replace the insufficient conditions C(c)=0 and det Hess C(c)=0 by a geometric condition distinguishing conjugate secants from secants joining two real singular points.

Let C be any real homogeneous cubic, G=∇C, and H=Hess C. Suppose

\[
G(c)=G(d),\qquad H(c)d=0.
\tag{1.1}
\]

The previous campaign identified (1.1) as the exact condition that x=(c+id)/2 is singular. The additional observation here is an entire polar pencil:

\[
\boxed{G(sc+td)=(s^2+t^2)G(c).}
\tag{1.2}
\]

This follows by quadratic polarization of G. If G(c)≠0, c and d are linearly independent.

Moreover C vanishes on their entire real plane. Indeed

\[
c\cdot G(d)=\tfrac12 d^TH(c)d=0,
\quad c\cdot G(c)=0,
\quad d\cdot G(c)=\tfrac12c^TH(c)d=0.
\]

Euler's identity gives C(sc+td)=0. Thus the projective line spanned by c,d lies on the cubic, its projective gradient is constant at every real point, and its singular points occur at t/s=±i. They form a conjugate pair, with no real singular point.

In contrast, if x,y are real singular points and c=x+y, d=x−y, then

\[
H(c)d=0,\qquad G(d)=-G(c),
\quad G(sc+td)=(s^2-t^2)G(c).
\tag{1.3}
\]

That line has two real singular points t/s=±1.

### Actual result

Equations (1.2)–(1.3) prove a geometric distinction between the two real branches. A nondegenerate actual real spectral cost with G(c)≠0 lies on an **elliptic contracted line** of the polar map. A sum of two real spectral points lies on a hyperbolic contracted line. Algebraic equations without inequalities can merge these branches.

## Round 002 — An exact rank-two matching model, in every dimension

### Proposed mechanism

Avoid recovering spectra from the cubic altogether. Work directly with perfect-matching monomials of a rank-two matrix.

For a matrix M, set z_π(M)=∏ᵢMᵢ,π(i). The additive spectral matrix M_ij=a_i+b_j has rank at most two. Conversely, every generic rank-two matrix is row-column equivalent to an additive one:

\[
M=uv^T+st^T,\qquad
M_{ij}=u_it_j\left(\frac{s_i}{u_i}+\frac{v_j}{t_j}\right).
\tag{2.1}
\]

A generic change of basis in the two-dimensional factorization makes every u_i and t_j nonzero. All matching products are multiplied by the same factor ∏u_i∏t_j under this row-column gauge.

The direct matrix identity, also independently supplied by the root investigator, is

\[
(D_a+UD_bU^*)U=D_aU+UD_b=U\circ M,
\]
so
\[
\boxed{\det(D_a+UD_bU^*)=\frac{\det(U\circ M)}{\det U}.}
\tag{2.2}
\]

Consequently MOC in dimension n is equivalent, by the generic gauge and continuity, to

\[
\frac{\det(U\circ M)}{\det U}
\in\operatorname{conv}_{\mathbb R}\{z_\pi(M)\}
\quad\text{for every rank-at-most-two }M.
\tag{2.3}
\]

### Exact reconstruction from matching coordinates

There is a spectrum-free description of the regular matching variety.

Let E have as its columns the n-by-n permutation incidence matrices, flattened. For every integer relation Eℓ=0, impose the toric relation

\[
\prod_{\ell_\pi>0}z_\pi^{\ell_\pi}
=
\prod_{\ell_\pi<0}z_\pi^{-\ell_\pi}.
\tag{2.4}
\]

If all z_π are nonzero, these equations imply z_π=∏M_iπ(i) for a matrix with all entries nonzero. Proof: assigning z_π to the incidence generators defines a character of their integer lattice precisely when (2.4) holds. A character into C* extends to the ambient integer lattice because complex roots exist; equivalently use Smith normal form. Its values on the edge generators give M_ij.

Now impose, for every three rows I, three columns J, and every matching ρ between their complements,

\[
\sum_{\sigma:I\to J}\operatorname{sgn}(\sigma)
z_{\sigma\cup\rho}=0.
\tag{2.5}
\]

For the reconstructed M, the left side is

\[
\det M[I,J]\prod_{i\notin I}M_{i,\rho(i)}.
\]

The second factor is nonzero, so all three-by-three minors vanish. Hence rank M≤2. The converse is immediate.

Thus toric matching equations plus six-term determinant relations characterize regular spectral products exactly. Their real and imaginary parts retain the real branch information.

For an affine real cost g=h e+Re(ηz), introduce c=g−he and a real d, and apply (2.4)–(2.5) to x_π=(c_π+id_π)/2. A quadratic toric relation x_πx_σ=x_τx_ρ becomes

\[
c_\pi c_\sigma-d_\pi d_\sigma
=c_\tau c_\rho-d_\tau d_\rho,
\]
\[
c_\pi d_\sigma+d_\pi c_\sigma
=c_\tau d_\rho+d_\tau c_\rho.
\tag{2.6}
\]

### Actual result and remaining gap

This is an exact regular-sector parametrization for every n, not merely a necessary cubic equation in n=4. Degenerate spectral products are limits of generic ones.

The positivity statement (2.3) remains unproved.


## Round 004 — Fermionic compression and a universal norm bound

### Proposed mechanism

Interpret rank-two matching products as matrix coefficients of permutations acting on qubits, and the Hadamard determinant as a fermionic scattering amplitude.

### Complete construction

Define an isometry

\[
J:(\mathbb C^2)^{\otimes n}
\longrightarrow \Lambda^n(\mathbb C^n\otimes\mathbb C^2)
\]
by
\[
J(v_1\otimes\cdots\otimes v_n)
=(e_1\otimes v_1)\wedge\cdots\wedge(e_n\otimes v_n).
\]

Since Λⁿ(U⊗I₂) is unitary,

\[
K_U=J^*\Lambda^n(U\otimes I_2)J
\]

is a contraction. Its product matrix coefficients are

\[
\langle x_1\otimes\cdots\otimes x_n,
K_U(y_1\otimes\cdots\otimes y_n)\rangle
=\det[U_{ij}\langle x_i,y_j\rangle].
\tag{4.1}
\]

Every complex rank-two matrix has a factorization M_ij=⟨x_i,y_j⟩. Therefore

\[
\boxed{
|\det(U\circ M)|\le\prod_i\|x_i\|\prod_j\|y_j\|.
}
\tag{4.2}
\]

Taking the infimum over rank-two factorizations gives a factorization-capacity bound. Dividing K_U by det U preserves its contraction norm.

Expanding (4.1) gives

\[
K_U=\sum_\pi\operatorname{sgn}(\pi)
\left(\prod_iU_{i,\pi(i)}\right)P_\pi,
\tag{4.3}
\]

with a consistent convention for the permutation operators. Only the permutation representations visible on tensor powers of C² matter. In n=4 this is the fourteen-dimensional quotient behind the common feature identities: its blocks have dimensions 1,3,2 and squared dimensions sum to 14.

### What remains

The exact missing statement is product-matrix-coefficient domination:

\[
\operatorname{Re}\langle X,\eta K_UY/\det U\rangle
\le
\max_\pi\operatorname{Re}\langle X,\eta P_\pi Y\rangle
\]

for all decomposable X,Y. An operator norm inequality does not imply this polygon inequality.

The construction makes the interference mechanism concrete: intermediate fermionic states can have two distinct internal states occupying one spatial mode, whereas classical permutation composition excludes those paths.


## Round 006 — Plücker interaction coordinates

### Proposed mechanism

Separate the four-dimensional spectral interaction into decomposable bivectors rather than treating all determinant support coefficients as independent.

Write M=XYᵀ with two-column matrices X,Y. Then

\[
\det M[I,J]=x_Iy_J,\quad
x_I=\det X[I,:],\quad y_J=\det Y[J,:].
\tag{6.1}
\]

In dimension four,

\[
x_{12}x_{34}-x_{13}x_{24}+x_{14}x_{23}=0,
\]
\[
y_{12}y_{34}-y_{13}y_{24}+y_{14}y_{23}=0.
\tag{6.2}
\]

The double-transposition interaction is exactly

\[
z_{\rm id}-z_{(12)}-z_{(34)}+z_{(12)(34)}
=\det M[12,12]\det M[34,34].
\tag{6.3}
\]

Its right side is (x₁₂x₃₄)(y₁₂y₃₄).

The three pairing coordinates

\[
X=(x_{12}x_{34},x_{13}x_{24},x_{14}x_{23})
\]

lie on X₁−X₂+X₃=0; likewise Y. Thus the pairing-interaction table is XYᵀ, complex rank one on two-dimensional factors. Its real support has real rank at most two.

### Actual result

The quartic interactions obey explicit quadratic equations and a factorization on two Plücker planes. They do not span the arbitrary coefficient cone permitted by permutation inequalities alone.

### Obstruction and remaining step

Complex Plücker products are not nonnegative squared norms. Choose

\[
X_1=Y_1=1,\quad X_3=Y_3=i,
\quad X_2=Y_2=1+i.
\]

Then Re(X₁Y₁)=1, Re(X₃Y₃)=−1, and Re(X₂Y₂)=0. Decomposability holds while the two diagonal contributions cancel.

A proof must connect these bilinear spectral factors with conjugate unitary Plücker factors. Replacing them by absolute values discards the cancellation determining the support direction.

## Round 007 — Recovering the affine center before solving the real branch

### Proposed mechanism

Remove the arbitrary support constant h by a rational operation before attacking conjugate-secant recovery.

For the particular fourteen-coordinate cubic, the prior exact identities are

\[
C(x+he)=C(x)+hQ(x),\qquad Q(x+he)=Q(x),
\]

where e is all ones and Q=DₑC.

If g=h e+c is an actual affine spectral cost, C(c)=0. On Q(g)≠0,

\[
\boxed{
h=\frac{C(g)}{Q(g)},\quad
c=g-\frac{C(g)}{Q(g)}e.
}
\tag{7.1}
\]

The center is unique. A wrong real branch cannot be repaired by another constant on this sector.

### Actual consequence

Regular affine membership requires the following concrete sequence:

1. Form c by (7.1).
2. Compute a real kernel basis N for H(c).
3. Solve
   \[
   \nabla C(Nt)=\nabla C(c).
   \tag{7.2}
   \]
4. If actual spectral recovery is needed, impose the matching equations from Round 002.

This avoids the degree-42 determinant and its extraneous factor Q¹¹. It treats Q=0 as a distinct chart instead of dividing through it.

### What remains

For a putative negative MOC cost, one must show (7.2) infeasible or prove the eventual unitary pairing nonnegative. The regular sector becomes a small real quadratic feasibility problem once the Hessian kernel is known. The Q=0 sector needs another chart or a valid closure argument.

## Round 008 — A two-by-two PSD formulation of real recovery

### Proposed mechanism

Lift real recovery to a positive-semidefinite matrix and exploit the small Hessian kernel.

Let N span ker H(c), and set

\[
A_j=\tfrac12N^TH(e_j)N,\qquad
L(T)_j=\operatorname{tr}(A_jT).
\]

Then (∇C(Nt))_j=tᵀA_jt, so real recovery is equivalent to

\[
\boxed{
L(T)=\nabla C(c),\quad T\succeq0,\quad
\operatorname{rank}T\le1.
}
\tag{8.1}
\]

A dual obstruction follows immediately: if real α satisfy

\[
\sum_j\alpha_jA_j\succeq0,\qquad
\alpha\cdot\nabla C(c)<0,
\tag{8.2}
\]

there is no recovery.

### Complete rank-reduction lemma

**Lemma.** If dim ker H(c)=2 and rank L≤2, the rank-one condition in (8.1) is redundant.

**Proof.** If feasible T has rank at most one, it already works. Otherwise T is positive definite. Choose nonzero symmetric Z∈ker L, which exists because Sym₂ has dimension three. Move along T+sZ. Near s=0 these matrices are positive definite. In at least one direction the feasible interval has a finite endpoint because T⁻¹ᐟ²ZT⁻¹ᐟ² has a nonzero eigenvalue. At that endpoint the matrix is positive semidefinite and singular, hence has rank at most one, with the same L-image. ∎

### Necessary qualification

The rank bound is **unproved for every corank-two point of the spectral cubic**, and it is false for general cubics.

For example let

\[
C=x_1^2(x_4+x_6)
+\tfrac12x_1(x_4-x_6)^2+\tfrac12x_1x_5^2
+x_2^2x_4+2x_2x_3x_5+x_3^2x_6.
\]

At c=e₁, ker H(c)=span(e₂,e₃), while

\[
\nabla C(c)=e_4+e_6,
\]
\[
\nabla C(se_2+te_3)=s^2e_4+2st\,e_5+t^2e_6.
\]

The PSD lift has the unique solution T=I₂. But real recovery requires s²=t²=1 and st=0, which is impossible. Thus rank L=3 cannot be ignored.

## Round 009 — Gluing spectrum-dependent laws

### Proposed mechanism

Formulate a meta-proof over restricted cases as gluing feasible permutation laws, and determine precisely when local extension is legitimate.

Let s denote parameters, A(s) the real matrix of augmented columns (1,v_π(s)), and b(s)=(1,d(s)). A law satisfies

\[
A(s)\lambda(s)=b(s),\qquad \lambda(s)\ge0.
\]

Suppose A(s₀) has full row rank and a strictly positive feasible λ₀ exists. Put

\[
R(s)=A(s)^T[A(s)A(s)^T]^{-1}.
\]

Near s₀,

\[
\boxed{
\lambda(s)=\lambda_0+
R(s)(b(s)-A(s)\lambda_0)
}
\tag{9.1}
\]

is exactly feasible, since A(s)R(s)=I. Continuity preserves positivity in a neighborhood.

If a region has local feasible laws, a partition of unity gives a global continuous law:

\[
\lambda(s)=\sum_\alpha\phi_\alpha(s)\lambda_\alpha(s).
\]

This works because the feasible laws at each fixed s form a convex fiber.

### Actual result

Existing local laws have no monodromy obstruction to gluing. A strict law supplies an open neighborhood theorem. The law here may depend on the spectral parameters; no spectrum-independent law is asserted.

### Boundary obstruction

At a law with zero weights, positivity in (9.1) is not automatic. A forward derivative δλ must satisfy

\[
A_0\delta\lambda=b'_0-A'_0\lambda_0,
\qquad
\delta\lambda_j\ge0
\quad\text{if }\lambda_{0j}=0.

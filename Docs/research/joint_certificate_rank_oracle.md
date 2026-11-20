## 1. The joint certificate cone really does admit rank reduction

For fixed supported actual \(z\), retain the entire certificate, not merely \(Y\):

\[
\mathcal K=
\left\{
(Y,\mu,\nu,\xi):
\begin{array}{l}
Y\succeq0,\quad \mu,\nu,\xi\ge0,\\
\langle Y,G_j\rangle=0\quad(j=1,\ldots,8),\\
(\langle Y,A_e\rangle)_e=\mu-\nu-C^T\xi
\end{array}
\right\}.
\]

Its objective is

\[
\ell_z(Y,\mu,\nu,\xi)
=\langle Y,F(z)\rangle+\mu\cdot w+\xi\cdot r.
\]

A negative value excludes **every** legal allocation and every cubic completion, exactly as required in `organized/research/ACTUAL_FIBER_ALLOCATION.md:139–163`.

### Compact normalization

Use

\[
\operatorname{tr}Y+\mathbf1^T\mu+\mathbf1^T\nu+\mathbf1^T\xi=1.
\]

This normalized slice is compact: PSD entries are bounded by the trace, and every scalar variable is bounded by one. Consequently, if a negative certificate exists, the normalized objective attains a negative minimum at an extreme point.

There are eight gauge equations, six \(b\)-equations, and one normalization equation: **fifteen affine equations**.

At a point with \(\operatorname{rank}Y=r\) and \(s\) positive scalar coordinates, the relevant product-cone face has dimension

\[
\frac{r(r+1)}2+s.
\]

If this exceeds fifteen, there is a nonzero two-sided feasible perturbation inside the face, contradicting extremality. Hence

\[
\boxed{\frac{r(r+1)}2+s\le15,\qquad r\le5.}
\]

This is a bound on the **joint linear certificate cone**. It does not assert that rank-one \(Y\) suffice, and it does not separate allocation choices between rank-one summands.

The proof and constructive reduction algorithm are given in this section.

### Alternative parity-block budget

The coefficient matrices respect the established \(9+10\) parity decomposition. Averaging preserves all certificate equations and the objective. Taking an extreme certificate in that block-diagonal cone gives

\[
\boxed{
\frac{r_+(r_++1)}2+
\frac{r_-(r_-+1)}2+s\le15.
}
\]

In particular,

\[
r_++r_-\le6.
\]

These are **alternative guarantees**:

- an unaveraged certificate of rank at most five; or
- a parity-block certificate satisfying the displayed block-rank budget.

I have not proved that one can impose both guarantees simultaneously. For instance, the block budget permits \((r_+,r_-)=(3,3)\), with at most three positive scalar multipliers.

Modulo the orthogonal freedom in full-column-rank factors
\[
Y_\pm=L_\pm L_\pm^T,
\]
the permitted parity patterns require at most **51 essential real factor coordinates**, rather than the 100 entries of arbitrary symmetric \(9+10\) blocks. This is a concrete reduction for a targeted negative-certificate search.

### Scalar supports are also bounded

At a negative certificate, \(Y\ne0\). Indeed, if \(Y=0\), then for any legal \(\alpha\),

\[
\begin{aligned}
\mu\cdot w+\xi\cdot r
&=\mu\cdot(w-\alpha)+\nu\cdot\alpha
+\xi\cdot(r+C\alpha)\\
&\ge0.
\end{aligned}
\]

At an extreme negative certificate, the positive scalar columns of

\[
[\,I_6,\,-I_6,\,-C^T\,]
\]

must be linearly independent. A dependence produces a supported scalar perturbation preserving the six \(b\)-equations; subtracting its normalization times the original certificate produces a nonzero normalized two-sided perturbation. Thus

\[
\boxed{s\le6.}
\]

In particular, \(\mu_e\) and \(\nu_e\) cannot both be positive at such an extreme certificate.

Exact enumeration gives the following numbers of independent supports:

| Support size | Number |
|---:|---:|
| 0 | 1 |
| 1 | 15 |
| 2 | 99 |
| 3 | 377 |
| 4 | 900 |
| 5 | 1,344 |
| 6 | 1,088 |
| **Total** | **3,824** |

The enumeration uses the actual signed residual matrix C, not an unsigned surrogate. The retained verifier `../../code/research/verify_joint_certificate_rank.py`, function `joint_structure`, checks independence of the fourteen directions and their parity structure.

### Constructive reduction algorithm

Starting from any negative certificate:

1. Restrict matrix perturbations to the current PSD range and scalar perturbations to the current positive support.
2. Solve the fifteen homogeneous perturbation equations.
3. If a nonzero direction exists, choose the sign that does not increase the objective.
4. Move until a PSD eigenvalue or a scalar coordinate vanishes.
5. Repeat on the smaller face.

Compact normalization makes the boundary step legitimate. Each step decreases face dimension. The scalar-dependence perturbation similarly removes dependent scalar supports.

This gives an actual rank/support reduction procedure—not merely an existence citation.

The related unconditional upper bound is Chua–Plaumann–Sinn–Vinzant, *Gram spectrahedra*, [arXiv:1608.00234v3](https://arxiv.org/abs/1608.00234v3), Proposition 3.1, including its face-dimension proof. Only its unconditional upper bound is used; the generic lower bound is not imported.

---

## 2. Exact HMSV-to-allocation coordinates are now explicit

The audited HMSV coordinates are

\[
f=(c,\operatorname{vec}A,\operatorname{vec}B),
\]

where \(A\) is \(3\times3\), \(B\) is \(2\times2\), and the normalization is the audit’s Fourier normalization.

Fourier inversion on the fourteen-dimensional incidence span is

\[
\boxed{
s_\pi=
\frac{
c+3\operatorname{tr}(A\rho_{31}(\pi))
+2\operatorname{tr}(B\rho_{22}(\pi))
}{24}.
}
\]

Thus there is an explicit rational \(24\times14\) matrix \(E\) with \(s=Ef\). Put

\[
D=\mathbf1E_{\mathrm{id}}-E.
\]

Then

\[
Df=(s_{\mathrm{id}}-s_\pi)_\pi
\]

is the complete vector of original contact gaps.

Construct \(Z\) from:

- six transposition rows of \(D\), divided by four;
- three double-transposition rows;
- four oriented three-cycle gap differences.

This gives precisely the project profile order

\[
z=(w_{12},w_{13},w_{14},w_{23},w_{24},w_{34},
d_1,d_2,d_3,J_{012},J_{013},J_{023},J_{123}),
\]

with

\[
\boxed{z=Zf,\qquad \operatorname{rank}Z=13,\qquad Z_{\bullet,0}=0.}
\]

The residual map is

\[
r=Rf,\qquad
R=\frac12
\begin{pmatrix}
1&1&-1\\
1&-1&1\\
-1&1&1
\end{pmatrix}
Z_{6:9,\bullet}.
\]

Using the exact project arrays,

\[
F(z)=\sum_{j=1}^{13}z_jF_j,
\]

we therefore obtain all fourteen Fourier-coordinate Gram coefficients:

\[
\boxed{
F(Zf)=\sum_{k=1}^{14}f_k
\left(\sum_{j=1}^{13}Z_{jk}F_j\right).
}
\]

The constant-coordinate coefficient is zero, as it must be.

This closes the **coordinate-bridge obligation**, not the positivity obligation. The project’s existing exact arrays already supply \(z\mapsto F\); see `organized/research/actual_fiber_allocation/build_criterion.py:5–29`. The new script supplies and checks \(f\mapsto z\).

Checks performed:

- inversion on all fourteen coordinate directions;
- rank thirteen and disappearance of the constant coordinate;
- agreement with the actual strict seed;
- export of every Fourier-to-Gram coefficient.

See the retained verifier `../../code/research/verify_joint_certificate_rank.py`, function `bridge`, for exact reconstruction of the rational coordinate maps.

An immediate useful consequence is that, for a fixed joint certificate, the entire objective is an explicit linear functional of \(f\):

\[
\ell(f)=
\langle Y,F(Zf)\rangle+
\mu\cdot(Zf)_{0:6}+\xi\cdot Rf.
\]

There is no remaining normalization ambiguity between the HMSV profile and the canonical allocation pencil.

---

## 3. A real-lift reduction that does not discard the coupled equations

The essential actual constraint remains

\[
H_\Phi(f)y=0,\qquad
\nabla\Phi(y)=\nabla\Phi(f),
\qquad y\in\mathbb R^{14}.
\]

I retained both equations. The cubic equation and singular-Hessian equation were not substituted for them.

Suppose the Hessian has corank two, and choose a real kernel basis \(K\in\mathbb R^{14\times2}\). Write

\[
y=K\binom uv.
\]

Because the gradient is quadratic, there is an explicitly computable \(14\times3\) matrix \(B_f\) such that

\[
\nabla\Phi\!\left(K\binom uv\right)
=B_f
\begin{pmatrix}u^2\\uv\\v^2\end{pmatrix}.
\]

Introduce

\[
M=\begin{pmatrix}m_{00}&m_{01}\\m_{01}&m_{11}\end{pmatrix}.
\]

Real lifting is exactly equivalent to

\[
B_f(m_{00},m_{01},m_{11})^T=\nabla\Phi(f),
\qquad M\succeq0,\qquad \operatorname{rank}M\le1.
\]

So far this is a reformulation. The useful additional fact is:

> **If \(\operatorname{rank}B_f=2\) and the affine system is consistent, its PSD relaxation is exact.**

The affine solution set is a line in \(\operatorname{Sym}_2\). If it contains a positive-definite matrix, moving along a nonconstant line must reach a finite singular PSD endpoint in at least one direction. If it already contains a singular PSD matrix, there is nothing to prove. In either case it contains a PSD matrix of rank at most one.

Therefore, under these **checkable hypotheses**,

\[
\boxed{
\exists y\text{ satisfying the coupled lift}
\iff
\exists M\succeq0\text{ satisfying the linear moment equations}.
}
\]

Computationally, parameterize the line, solve its determinant quadratic, and test the diagonal signs at its singular endpoints. An identically singular line instead reduces to linear diagonal inequalities.

This is not an unrestricted “positive map on \(M_2\)” argument. Exactness follows from the dimension of this particular affine slice.

### Exact actual example

For

\[
a=(-1-2i,\ 2+2i,\ -1+2i,\ 0),\qquad
b=(-2-i,\ -2+i,\ 1,\ 2+2i),
\]

the exact computation gives Hessian rank twelve and \(\operatorname{rank}B_f=2\). Its moment-line determinant is

\[
\det M(t)=
\frac{1906901768}{10680189025}
(t-576)(23t+193442).
\]

At \(t=576\),

\[
M=
\begin{pmatrix}
80656&6816\\6816&576
\end{pmatrix}
=
\binom{284}{24}(284,\ 24).
\]

This is PSD rank one and reconstructs a real lift through \(K\). The other singular endpoint is negative semidefinite.


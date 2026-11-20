# Full-unitary MOC4: an exact quartic and one certificate scalar

**Status:** proved reformulation, not a proof of MOC. This calculation keeps the actual spectral products and covers every unitary direction; it is not a rank-two restriction. The universal PSD certificate in Section 4 is unproved. No novelty relative to the entire literature is asserted.

## 1. Clearing the Cayley denominator in every dimension

Let
\[
z_\pi=\prod_{i=1}^n(a_i+b_{\pi(i)}),\qquad
h=\max_\pi\operatorname{Re}(\eta z_\pi).
\]
Relabel the b-spectrum so the identity attains h, and put
\[
\delta_\pi=h-\operatorname{Re}(\eta z_\pi)\ge0,
\qquad \delta_{\mathrm{id}}=0.
\]
The relabeling is harmless for the unrestricted unitary problem. It would not be harmless for a prescribed restricted family of Cayley generators.

For an arbitrary Hermitian H, let
\[
U_t=(I+itH)(I-itH)^{-1},\quad
 d_H(t)=\det(I+t^2H^2)>0,\quad D=D_a+D_b.
\]
Multiplying the matrix inside the determinant on the left by I-itH and on the right by I+itH gives
\[
\boxed{
 d_H(t)\det(D_a+U_tD_bU_t^*)
 =\det\{D+it[D_a-D_b,H]+t^2HDH\}.
}
\tag{1}
\]
Consequently the support numerator is the real polynomial
\[
N_H(t)=h\,d_H(t)
 -\operatorname{Re}\!\left[\eta\det\{D+it[D_a-D_b,H]+t^2HDH\}\right].
\tag{2}
\]

**Degree cancellation.** Its constant coefficient is zero. Its linear coefficient is also zero: the first orbit variation at a diagonal pair is a commutator with zero diagonal, and hence its determinant derivative vanishes. This argument first applies when D is invertible and then extends polynomially to every spectrum.

For invertible H, U_t tends to -I as t tends to infinity. The limiting determinant is z_id and its first variation again vanishes. Thus the coefficients of degrees 2n and 2n-1 in (2) vanish. Invertible Hermitian matrices are dense, so the same cancellations hold for singular H. For n>=2,
\[
\boxed{N_H(t)=t^2Q_H(t),\qquad\deg Q_H\le2n-4.}
\tag{3}
\]
This is an identity, not a positivity claim.

## 2. Exact equivalence, without realification

Every unitary with no eigenvalue -1 is U_1 for a Hermitian H. That Cayley chart is dense in U(n). Therefore MOC in dimension n is equivalent to
\[
Q_H(t)\ge0\quad\text{for every real }t
\tag{4}
\]
for every spectral pair, support multiplier, maximizing-permutation relabeling, and Hermitian H.

Every nonnegative real univariate polynomial of degree at most 2m is a sum of squares of real polynomials of degree at most m. For completeness: each real root has even multiplicity; collect one root from each nonreal conjugate pair into a complex polynomial f, and write the nonnegative polynomial as f times its conjugate, hence (Re f)^2+(Im f)^2, absorbing its positive leading constant. The zero polynomial is immediate.

Applying this with m=n-2 gives the equivalent finite certificate
\[
Q_H(t)=(1,t,\ldots,t^{n-2})G_H(1,t,\ldots,t^{n-2})^T,
\qquad G_H\succeq0.
\tag{5}
\]
The certificate may and generally must depend on both spectra as well as H. The identity does not construct it.

There are n(n-1)/2 symmetric Gram entries and 2n-3 independent coefficient constraints. Surjectivity follows because each monomial degree from 0 to 2n-4 occurs on a Gram antidiagonal. Thus the unconstrained Gram fiber has dimension (n-2)(n-3)/2: for n=3,4,5,6,7 these dimensions are 0,1,3,6,10. This is the triangular-number sequence [OEIS A000217](https://oeis.org/A000217), here derived by coefficient counting rather than inferred from a numerical pattern. It explains the single scalar at n=4; it does not establish PSD feasibility.

## 3. Explicit endpoint and cubic coefficients for full U(4)

Write
\[
Q_H(t)=A+Bt+Ct^2+Dt^3+Et^4.
\]
Using cycles as mappings i->j->k->i, one has
\[
\boxed{A=4\sum_{i<j}\delta_{(ij)}|H_{ij}|^2,}
\tag{6}
\]
\[
\boxed{B=8\sum_{i<j<k}
 \operatorname{Im}(H_{ij}H_{jk}H_{ki})
 (\delta_{(ijk)}-\delta_{(ikj)}).}
\tag{7}
\]
In particular A>=0.

Here is a derivation that also addresses the apparently complex permutation coefficients. Since
\[
\det(D_a+UD_bU^*)=\overline{\det U}
 \sum_\pi\operatorname{sgn}(\pi)\prod_iU_{i,\pi(i)}z_\pi,
\]
expand U_t=I+2itH-2t^2H^2-2it^3H^3+O(t^4). Transpositions contribute the second-order coefficient. At cubic order, for each triple set w=H_ij H_jk H_ki. The real contribution to the determinant is
\[
8\operatorname{Im}(w)(z_{(ijk)}-z_{(ikj)}).
\]
The remaining imaginary contribution is proportional to
\[
z_{(ij)}+z_{(ik)}+z_{(jk)}-z_{\mathrm{id}}-z_{(ijk)}-z_{(ikj)}=0.
\tag{8}
\]
Identity (8) is the vanishing determinant of the rank-at-most-two 3-by-3 matrix (a_i+b_j), multiplied by the factors outside the triple. Thus it is a polynomial identity for the actual spectra, not an assumption about arbitrary permutation costs. Subtracting the determinant from its support maximum gives (7).

There is also a reciprocal identity. For invertible H,
\[
U(-H^{-1})=-U(H),\qquad
N_H(t)=\det(H)^2t^8N_{-H^{-1}}(1/t).
\tag{9}
\]
It follows that
\[
\boxed{E=4\sum_{i<j}\delta_{(ij)}
 |\operatorname{adj}(H)_{ij}|^2\ge0.}
\tag{10}
\]
This formula is polynomial and remains valid when H is singular. For invertible H the remaining odd coefficient is
\[
D=-\det(H)^2 B(H^{-1}).
\tag{11}
\]
For all H, both D and C are defined without any division by coefficient extraction from (2). Explicitly,
\[
C=[t^4]N_H(t),\qquad D=[t^5]N_H(t).
\]
Thus no orthogonal completion or hidden optimization is contained in these coefficients.

## 4. The single scalar that remains unproved

Coefficient matching in (5) for n=4 leaves precisely one free real scalar u:
\[
\boxed{
G(u)=\begin{pmatrix}
 A&B/2&u\\
 B/2&C-2u&D/2\\
 u&D/2&E
\end{pmatrix}\succeq0.
}
\tag{12}
\]
Indeed Q_H(t)=(1,t,t^2)G(u)(1,t,t^2)^T. Consequently the assertion

> For every actual spectral input and every Hermitian H, there exists a real u satisfying (12)

is **equivalent to unrestricted MOC4**. Equations (6) and (10) establish the two endpoint inequalities but do not establish (12).

For A,E>0, the scalar feasibility condition is equivalently
\[
\boxed{
C\ge \inf_{|u|<\sqrt{AE}}
\left\{2u+\frac{EB^2-2uBD+AD^2}{4(AE-u^2)}\right\}.
}
\tag{13}
\]
Endpoint limits are permitted. This follows by taking the Schur complement of the A,E corner of G. Formula (12), not division in (13), handles all degeneracies.

The obstacle is now explicit: the nonnegative permutation gaps and their common spectral-product structure must imply (12). Assuming arbitrary nonnegative gap arrays in their place is not justified. Choosing u=0 or requiring C>=0 is also not justified.

### 4.1 An exact failure of an endpoint-compatible scalar prescription

Let J=adj(H) and
\[
T=4\sum_{i<j}\delta_{(ij)}\operatorname{Re}(\overline{H_{ij}}J_{ij}).
\]
The choice u=-T automatically makes the A,E corner PSD: it is the real Gram matrix of the vectors with components 2 sqrt(delta_(ij)) H_ij and -2 sqrt(delta_(ij)) J_ij. However, the full matrix G(-T) need not be PSD.

An exact counterexample to that prescription is
\[
a=(13,17,-10,3),\quad b=(6,9,10,-3),\quad \eta=1,
\]
\[
H=\begin{pmatrix}
8&-1&1&0\\
-1&10&-1&-1-i\\
1&-1&12&-1+i\\
0&-1+i&-1-i&9
\end{pmatrix}.
\]
The identity attains the support maximum h=0. Direct exact expansion gives
\[
(A,B,C,D,E)=(667888,1225120,112096784,60478496,4201015520),
\qquad T=-52763152.
\]
Consequently
\[
\det G(-T)=-88754623743488049152<0.
\]
This is **not a counterexample to MOC**. In fact G(0) is positive definite, with leading principal minors
\[
667888,\quad74492867118592,\quad312334966012763591692288.
\]
It disproves the proposed universal scalar selection, despite its automatic endpoint Cauchy–Schwarz bound. The failure was detected numerically and then recomputed with exact integers; it is not a tolerance-level observation.

### 4.2 Eliminating the Gram scalar: a sharp algebraic threshold

For A,E>0 set
\[
\beta=\frac{B}{A^{3/4}E^{1/4}},\quad
\gamma=\frac{C}{\sqrt{AE}},\quad
\delta=\frac{D}{A^{1/4}E^{3/4}},\quad
s=\frac{|\beta+\delta|}{2},\quad q=\frac{|\beta-\delta|}{2}.
\]
Define
\[
\Psi(s,q)=\max_{r\ge2}\{2-r^2+sr+q\sqrt{r^2-4}\}.
\tag{13a}
\]
Then the exact scalar-free criterion is
\[
\boxed{Q_H(t)\ge0\ \forall t\in\mathbb R
\iff C\ge\sqrt{AE}\,\Psi(s,q).}
\tag{13b}
\]
This is a theorem about quartics, **not a proof that every MOC spectral input satisfies the criterion**.

To prove it, put t=(A/E)^(1/4)x. The normalized quartic is
1+beta x+gamma x²+delta x³+x⁴. For x nonzero write
\[
y=x+x^{-1},\quad z=x-x^{-1},\quad y^2-z^2=4.
\]
Dividing the quartic by x² gives
\[
\gamma+y^2-2+(\beta+\delta)y/2+(\delta-\beta)z/2.
\]
For each r=|y|>=2 the signs of y and z can be chosen independently.
Its minimum is therefore gamma-Psi(s,q), proving (13b). The value at x=0 is 1.

The maximization in (13a) is explicit. If q=0,
\[
\Psi(s,0)=\begin{cases}2s-2,&s\le4,\\2+s^2/4,&s\ge4.\end{cases}
\]
If q>0, there is exactly one maximizing r_*>2, characterized by
\[
2r_*=s+\frac{qr_*}{\sqrt{r_*^2-4}},\qquad
(2r_*-s)^2(r_*^2-4)=q^2r_*^2,\quad2r_*>s.
\]
Indeed the derivative of the objective decreases strictly from +infinity to
-infinity, since its second derivative is
-2-4q/(r²-4)^(3/2). Substitution of r_* in (13a) determines the threshold.

There is also a constructive SOS. At gamma_*=Psi(s,q), choose the real
nonzero minimizing x_0. The boundary quartic has a root of multiplicity at
least two at x_0 and
factors as
\[
(x-x_0)^2\{x^2+\alpha x+x_0^{-2}\},\qquad
\alpha=\delta+2x_0.
\]
The quadratic factor is nonnegative, so kappa=x_0^(-2)-alpha²/4>=0.
For every gamma>=gamma_* the normalized quartic equals
\[
[(x-x_0)(x+\alpha/2)]^2+
\kappa(x-x_0)^2+(\gamma-\gamma_*)x^2.
\tag{13c}
\]
In the original basis (1,t,t²), the SOS gives the explicit Gram scalar
\[
u=-\frac{\sqrt{AE}}2\,x_0(\delta+2x_0).
\tag{13d}
\]
Only the middle diagonal changes when gamma increases above gamma_*, so this
same scalar works throughout that interval. This constructs a certificate if
the spectral inequality (13b) is established; it does not assume the refuted
prescription u=-T.

For completeness, the scalar-free criterion at the endpoint degeneracies is
\[
\begin{array}{ll}
A=0,\ E>0:&B=0,\quad C\ge D^2/(4E),\\
E=0,\ A>0:&D=0,\quad C\ge B^2/(4A),\\
A=E=0:&B=D=0,\quad C\ge0.
\end{array}
\tag{13e}
\]
These are necessary and sufficient for the corresponding quartic to be
nonnegative: a zero constant term forces a zero linear term; a zero leading
quartic term forces a zero cubic term; what remains is the elementary
quadratic discriminant criterion. This completes the generic quartic test,
not the proof that the MOC coefficients satisfy it. Formula (12) also handles
all these cases without division.

An exact implementation check is beta=19/5, delta=1/5: r_*=5/2,
gamma_*=69/20, x_0=-1/2, alpha=-4/5 and kappa=96/25. Expanding (13c)
reproduces all five coefficients exactly. No literature-priority claim is made
for this univariate calculation.

### 4.3 Proved pruning of the unrestricted target

[analysis_moc4_quartic_pruning.md](analysis_moc4_quartic_pruning.md) develops the proof architecture without restricting to real unitaries:

- The support problem reduces to four exhaustive generic edge types: a transposition, a double transposition, a three-cycle, or a four-cycle.
- For an all-real-t quartic proof, it suffices to use zero-diagonal Hermitian generators with Frobenius norm one. These retain all complex directions; invertible generators suffice by density.
- The established reflection-average theorem proves the universal bound C>=-2 sqrt(AE). Its edge-sensitive strengthening closes the equality boundary by forcing a block-reducing configuration, where B=D=0. The remaining generic edge target has A,E>0 and C>-2 sqrt(AE).
- The global Gram test needs at most three scalar candidates. With I=C²-3BD+12AE and J=72ACE+9BCD-27AD²-27EB²-2C³, the sole interior candidate is u=(C-sqrt(I))/6; its determinant is (J+2 I^(3/2))/108. The two endpoint candidates need their compatibility conditions.
- An alternative complete route uses the full canonical domain and a four-parameter interval SOS on [-1,1], rather than insisting on global positivity of each individual quartic.

These are proved reductions, not a proof of the remaining spectral odd-coupling inequalities. The new note also gives an exact counterexample to u=-T **inside the full canonical zero-diagonal domain**, so that gauge cannot rescue the prescription refuted in Section 4.1.

## 5. Full real SO(4) specialization and a negative-middle example

Take H=-iK with real skew K. Then U_t=(I+tK)(I-tK)^(-1). Put
\[
s=\sum_{i<j}K_{ij}^2,\quad p=\operatorname{pf}K,
\quad d(t)=\det(I-tK)=1+st^2+p^2t^4.
\]
The denominator d_H(t) is d(t)^2. Define
\[
\mathcal A(X)=4\sum_{i<j}\delta_{(ij)}X_{ij}^2,
\quad
\mathcal B(X)=8\sum_{i<j<k}X_{ij}X_{jk}X_{ki}
 (\delta_{(ijk)}-\delta_{(ikj)}).
\]
With Hodge-dual convention (*K)_12=K_34, (*K)_13=-K_24, (*K)_14=K_23,
\[
A=\mathcal A(K),\quad B=\mathcal B(K),\quad
D=-p\mathcal B(*K),\quad E=p^2\mathcal A(*K).
\tag{14}
\]
These follow from K^(-1)=-*K/p and the reciprocal identity; polynomial continuation includes p=0.

For a reproducible exact example take
\[
a=(-2-i,-3-3i,2+i,3+2i),\quad
b=(-3+3i,-2,3,-2i),\quad\eta=1,
\]
\[
K=\begin{pmatrix}
0&-1&-2&-2\\1&0&-2&3\\2&2&0&1\\2&-3&-1&0
\end{pmatrix}.
\]
The identity is uniquely maximizing, h=450, p=9, and d(t)=1+23t^2+81t^4. Exact expansion gives
\[
Q(t)=52280-11312t-246404t^2+60048t^3+4017600t^4.
\tag{15}
\]
Its middle coefficient is negative. Nevertheless u=-157341 gives
\[
G=\begin{pmatrix}
52280&-5656&-157341\\
-5656&68278&30024\\
-157341&30024&4017600
\end{pmatrix}\succ0.
\]
The leading principal minors are 52280, 3537583504, and 12528602970304410. This certifies this entire curve and demonstrates why coupling the endpoint terms is essential. It is not offered as another case in lieu of the universal assertion (12).

## 6. Numerical scope and remaining target

The direct-attack data in `build/direct_attack/` are evidence only. The fixed-spectrum, optimized-frame search performed 3,536 local optimizations in dimensions 3 through 6, including 2,160 real-orthogonal-frame runs in dimension four. Those runs were not full-U(4) searches. No normalized gap exceeded 1e-8. These are local searches, not certified global optimizations.

The joint-spectrum search also optimizes the actual support gap, not arbitrary compound-matrix costs. Its first 120 trials frequently made all 24 projected products tie despite separated spectral entries. To exclude that degeneracy, a second pass required variance at least 1e-5 among the 24 projected products. Of 60 trials in that pass, 23 satisfied the constraints and 21 optimizers reported success. The maximum normalized gap among feasible trials was approximately -7.94e-6. The other 37 trials were not valid evidence for feasibility or for MOC.

The stronger prescription u=-T survived 87 initial random tests, but the stress test found a failure and led to the exact refutation in Section 4.1. This is a concrete warning against converting a clean numerical run into a universal certificate. The all-input one-scalar feasibility problem (12) remains intact.

The required next mathematical step is a proof or counterexample of (12) for all actual spectral inputs. The all-n target is the analogous construction in (5). Neither follows merely from univariate sums-of-squares theory, which establishes the equivalence but not the required nonnegativity.

The later audit in `docs/research/moc_oeis_convergence.md` distinguishes endpoint data from iteration traces, identifies converged suboptimal saddles, and proves a uniform covering-error bound. Its nine new dimension-four traces use complex Givens parameters, not the earlier real-orthogonal restriction. Neither experiment constructs a certified global cover.

Related notes: `analysis_moc4_quartic_pruning.md` (unrestricted proof architecture and exact pruning), `analysis_rank_two_cayley_reduction.md` (the p=0 boundary and a sufficient budget), `algebra_quaternionic_realification.md` (a separate dimension-four reduction). The full-unitary derivation above does not rely on either theorem.

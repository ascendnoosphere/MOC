## 1. Exact original theorems

### Singular-locus theorem

Howard–Millson–Snowden–Vakil, *The ring of projective invariants of eight points on the line via representation theory*, **arXiv:0809.1233v1, Theorem 1.1**:

> Over \(\mathbb Q\), there is a unique, up to scaling, nonzero skew-invariant cubic \(s\in\operatorname{Sym}^3(R_8^{(1)})\). It vanishes on \(M_8\), and \(M_8\) is its singular locus. More precisely, the fourteen partial derivatives generate \(I_8\), so the singular scheme of the affine cubic cone is precisely the affine cone over \(M_8\).

The theorem also identifies \(s\) as the skew-average of the cube of any matching.

- Original: https://arxiv.org/src/0809.1233v1
- Source: arXiv:0809.1233v1, Theorem 1.1.

### Hessian/secant theorem

HMSV, *The geometry of eight points in projective space: representation theory, Lie theory, dualities*, **arXiv:1103.5255v1**, submitted 27 March 2011:

- **Corollary 3.12:** \(\deg\operatorname{Sec}(M_8)=21\).
- **Proposition 3.13:** the secant divisor on the cubic is the zero divisor of a section of \(\mathcal O_{\mathcal C}(7)\).
- **Proposition 3.19, p. 18:**
  > “The Hessian \(\mathcal H_{\mathcal C}\) vanishes to order \(2\) along \(\operatorname{Sec}(M_8)\).”

The following paragraph states that the Hessian is a perfect square modulo the cubic, using a lift of that invariant septic section. Together with the surrounding argument, the reduced intersection is exactly the complex secant variety—not an additional unidentified component.

- Original: https://arxiv.org/src/1103.5255v1
- Secant/septic construction: arXiv:1103.5255v1, Corollary 3.12 and Proposition 3.13.
- Hessian theorem and square statement: arXiv:1103.5255v1, Proposition 3.19 and its following paragraph, p. 18.

**Arithmetic caution:** retain a nonzero scalar:
\[
\det H_\Phi\equiv \kappa S^2\pmod{\Phi},\qquad \kappa\ne0.
\]
Do not interpret “square” as a real nonnegativity assertion under the current normalization.


## 2. Public invariant audit

Found:

https://github.com/djma/marcus-de-oliveira/blob/573e649cc8810cfb707fb1441bdeaa78b6665471/research/full_moc_n4/n4_m8_invariant_audit.md

Its accompanying verifier is:

https://github.com/djma/marcus-de-oliveira/blob/573e649cc8810cfb707fb1441bdeaa78b6665471/research/full_moc_n4/verify_n4_m8_invariant_certificate.py

The audit and verifier are pinned by the commit-specific public URLs above.

I independently checked:

- incidence/Fourier span rank \(14\);
- skew covariance under all seven adjacent \(S_8\) transpositions;
- all fourteen gradient identities on **generic symbolic product arrays**;
- the abstract cubic/secant identities;
- the audit’s real-score example with nonzero gradient and Hessian rank \(12\);
- its projected-line factorization and irreducible degree-nine factor.

The global nonic conclusion requires HMSV and denominator clearing, not merely the line computation.

## 3. Exact hypothesis match and a reconstructible cubic

For eight vectors, take
\[
u_i=(a_i,1),\qquad v_j=(-b_j,1).
\]
Then
\[
[u_i,v_j]=a_i+b_j,\qquad
\delta_\pi=\prod_i[u_i,v_{\pi(i)}].
\]

These are precisely bipartite perfect-matching invariants, with **each of the eight labels occurring once**, matching HMSV’s equal linearization \(\mathcal O(1,\ldots,1)\). The 24 bipartite matching polynomials span the fourteen-dimensional degree-one invariant space. This span and the natural \(S_8\) action were checked exactly.

Consequently the product-coordinate vector lies in the affine cone over \(M_8\). Multiplication by \(\eta\) preserves that cone. Repeated spectra and zero evaluations introduce no division issue.

### Fourier coordinates directly from the 24 scores

For a score array \(f_\pi\), use the verifier’s normalization:
\[
c=\sum_\pi f_\pi,\qquad
A=\sum_\pi f_\pi\rho_{31}(\pi^{-1}),\qquad
B=\sum_\pi f_\pi\rho_{22}(\pi^{-1}).
\]

Here:

- \(\rho_{31}\) acts on \(e_0-e_3,e_1-e_3,e_2-e_3\);
- \(\rho_{22}\) acts on \(q_0-q_2,q_1-q_2\), where
  \[
  q_0=01|23,\quad q_1=02|13,\quad q_2=03|12.
  \]

Write \(B=\begin{pmatrix}p&q\\r&s\end{pmatrix}\). An explicit integral skew cubic is
\[
\boxed{\Phi(c,A,B)=162\det A+72c\det B-27T(A,B)+8K(B)}
\]
with
\[
T=\sum_{\alpha,\beta=0}^1
B_{\alpha\beta}\operatorname{tr}(A^TR_\alpha A L_\beta),
\]
\[
R_0=\begin{pmatrix}1&-1&2\\-1&-2&-1\\2&-1&1\end{pmatrix},
\quad
R_1=\begin{pmatrix}-1&-2&1\\-2&-1&1\\1&1&2\end{pmatrix},
\]
\[
L_0=\begin{pmatrix}0&0&1\\0&0&-1\\1&-1&0\end{pmatrix},
\quad
L_1=\begin{pmatrix}0&-1&0\\-1&0&1\\0&1&0\end{pmatrix},
\]
and
\[
\begin{aligned}
K=3(&2p^2q+p^2s-2pq^2+2pqr-2pqs-2prs+ps^2\\
&-q^2r-qr^2+2qrs-2r^2s+2rs^2).
\end{aligned}
\]

Exact implementations:

```python
fourier_blocks(values: Sequence[sp.Expr])
    -> tuple[sp.Expr, sp.Matrix, sp.Matrix]

phi(scalar: sp.Expr, block31: sp.Matrix, block22: sp.Matrix)
    -> sp.Expr
```

See the [pinned public verifier](https://github.com/djma/marcus-de-oliveira/blob/573e649cc8810cfb707fb1441bdeaa78b6665471/research/full_moc_n4/verify_n4_m8_invariant_certificate.py), lines 109–183 and 323–386.

**This supplies the missing coordinate bridge:** it is not just an abstract isomorphism of fourteen-dimensional representations.

## 4. Direct proof of the two necessary equations

Let \(H_\Phi\) denote the Hessian **matrix**. For every homogeneous cubic,
\[
\Phi(p+q)=\Phi(p)+\Phi(q)
+\nabla\Phi(p)\cdot q+\nabla\Phi(q)\cdot p,
\]
\[
H_\Phi(p+q)(p-q)=2\bigl(\nabla\Phi(p)-\nabla\Phi(q)\bigr).
\]

Take \(w=\eta\delta\), \(f=\Re w\). Because \(\Phi\) has real coefficients,
\[
\nabla\Phi(w)=\nabla\Phi(\bar w)=0.
\]
Euler’s identity gives \(\Phi(w)=\Phi(\bar w)=0\). Applying the first identity to \(w,\bar w\), then homogeneity, yields
\[
\boxed{\Phi(f)=0.}
\]

Writing \(w=f+iy\), the second identity gives
\[
H_\Phi(f)y=0.
\]
If \(y\ne0\), this is a nonzero kernel vector. If \(y=0\), then \(f\) itself is singular and
\[
H_\Phi(f)f=2\nabla\Phi(f)=0.
\]
For \(f=0\), the Hessian matrix is zero. Thus in every case
\[
\boxed{\det H_\Phi(f)=0.}
\]

These necessity arguments are elementary; they do not require the deeper Hessian-divisor theorem.


## 6. Global projection to the thirteen gap coordinates

Put
\[
D=\det B,\qquad \Phi=72cD+\Phi_0(A,B).
\]
On \(D\ne0\),
\[
c_*=-\frac{\Phi_0}{72D},
\]
and an explicit reconstructible projection equation is
\[
\boxed{
J(A,B)=D^2\det H_\Phi(c_*,A,B)=0.
}
\]

### Why \(J\) is genuinely polynomial

The Hessian has block form
\[
\begin{pmatrix}
0&0&v^T\\
0&M&N\\
v&N^T&Q+cK
\end{pmatrix},
\qquad
v=72\nabla D,\quad K=72H_D.
\]
Its determinant has degree at most three in \(c\). Its leading coefficient is, up to sign,
\[
\det(M)\,v^T\operatorname{adj}(K)v.
\]
Since \(D\) is quadratic,
\[
\nabla D=H_D\,\operatorname{vec}B,\qquad
(\nabla D)^T\operatorname{adj}(H_D)\nabla D
=2\det(H_D)D.
\]
Hence the cubic coefficient is divisible by \(D\), and \(D^2\) clears all denominators.

Therefore \(J\) is homogeneous of degree eighteen. HMSV’s double-divisor theorem then yields
\[
\boxed{J=\kappa N_9^2}
\]
for a homogeneous polynomial \(N_9\) of degree nine and nonzero scalar \(\kappa\). Polynomiality plus unique factorization supplies the polynomial square root up to scalar. This is a global argument, unlike checking one line.

The verified line specialization is
\[
J(t)=-2^{20}3^{42}q_9(t)^2,
\]
with \(q_9\) irreducible and coprime to the specialized \(D\). This also illustrates why “square” supplies **no real positivity conclusion**.

### Mapping scores to gaps

For \(\Delta_\pi=f_{\rm id}-f_\pi\),
\[
A(f)=-A(\Delta),\qquad B(f)=-B(\Delta),
\]
because both nontrivial representation sums vanish. Adding a constant changes only \(c\), by \(24\) times that constant. Thus \(J=0\), equivalently \(N_9=0\), descends to the current thirteen-dimensional gap model.

**Boundary caution:** on \(D=0\), reconstructing a score requires
\[
\Phi_0(A,B)=0
\]
and a direct Hessian/lifting check in \(c\). A denominator-cleared projected equation alone does not certify a real lift.


## 1. Original-source audit: the correct active results support the argument

### Singular locus and hypotheses

The imported singular-locus statement is accurately represented in `organized/research/HMSV_COMPATIBILITY.md:12–14`.

The original theorem says, **over \(\mathbb Q\)**:

- the nonzero \(S_8\)-skew cubic is unique up to scaling;
- its fourteen derivatives generate \(I_8\);
- consequently its affine singular scheme is precisely the affine \(M_8\) cone.

This is stronger than merely saying the cubic vanishes on product evaluations. It justifies identifying the complex singular cone after base change.

**Sources:** `organized/research/external/m8_hmsv/0809.1233v1/8pts-090708.tex:242–255`; compiled statement at `organized/research/external/m8_hmsv/0809.1233v1.txt:72–80`.

The actual coordinate input satisfies the required equal linearization: each matching uses all eight labels exactly once. There is no hidden distinctness hypothesis or division by pair sums.

### Secant divisor, septic section, and Hessian multiplicity

The active source supports the chain used in `organized/research/HMSV_COMPATIBILITY.md:16–20`:

1. the secant variety has degree \(21\);
2. it is the divisor of a section of \(\mathcal O_{\mathcal C}(7)\);
3. the Hessian vanishes precisely along the exceptional/secant divisor, with multiplicity two;
4. the following paragraph explicitly states the square-modulo-cubic conclusion.

**Sources:** `organized/research/external/m8_hmsv/1103.5255v1/8pts-032711.tex:1267–1323,1570–1596`.

The compiled text confirms **Corollary 3.12 and Proposition 3.13** at `organized/research/external/m8_hmsv/1103.5255v1.txt:831–859`, and **Proposition 3.19**, on printed page 18, at `organized/research/external/m8_hmsv/1103.5255v1.txt:956–962`.

Thus the correct imported conclusion is

\[
\det H_\Phi\equiv \kappa S_7^2\pmod{\Phi},\qquad \kappa\ne0.
\]

Retaining the normalization scalar is essential.

### API exclusion is correct

The warning in `organized/research/HMSV_COMPATIBILITY.md:24–26` is justified. The active compiled Hessian proposition is **3.19**, not the API’s 3.21. The subsequent septic subsection starts inside a suppressed `\cut{...}` block, and the authors’ serious-error warning occurs at `organized/research/external/m8_hmsv/1103.5255v1/8pts-032711.tex:1609`.

I did **not** use the API’s suppressed “Proposition 3.22.”

**Source-hygiene correction:** the active proof itself contains editorial slips: “dimension at most 3” in its Lefschetz parenthetical, and \(\mathbb P^{14}\) where fourteen homogeneous coordinates give \(\mathbb P^{13}\). These should not be reproduced as general auxiliary claims. They do not invalidate the cited result or the present application. See `organized/research/external/m8_hmsv/1103.5255v1/8pts-032711.tex:1304,1317–1319`.

## 2. The Fourier bridge matches actual products, not just representation dimensions

The construction in `organized/research/HMSV_COMPATIBILITY.md:30–53` is sound.

For
\[
u_i=(a_i,1),\qquad v_j=(-b_j,1),
\]
one has
\[
[u_i,v_j]=a_i+b_j.
\]
Hence the permutation products are actual bipartite matching invariants in HMSV’s degree-one invariant space.

Independently of the bridge verifier, I reconstructed their \(70\times24\) coefficient matrix by selecting one variable from each factor. Its rank is \(14\), and its selected basis and evaluation-extension matrix agree with the previously audited product record.

I then constructed the Fourier representations by restricting genuine permutation matrices to the zero-sum bases, rather than calling the verifier’s `rho31` or `rho22`. This reproduced the saved bridge matrix and established exactly:

\[
\det K_{\mathrm{bridge}}=7247757312,
\]
\[
\Phi_F(K_{\mathrm{bridge}}v)=-20736\,\Phi_{\mathrm{primitive}}(v).
\]

The second identity was checked coefficientwise as a polynomial identity. Combined with the previously audited \(S_8\)-skew covariance, this identifies the **actual unique HMSV cubic**, not merely an abstract cubic in fourteen variables.

I also independently recovered

\[
K_{\mathrm{bridge}}\mathbf1=(24,0,\ldots,0)^T,
\qquad
Q_2(\gamma)=-\frac{D(\gamma)}{12}.
\]

Thus the constant quotient and exceptional chart agree in both coordinate systems. These results substantiate `organized/research/HMSV_COMPATIBILITY.md:50–59`.

**Normalization clarification:** transporting the Hessian uses congruence, not just substitution. With \(\alpha=-20736\),

\[
K_{\mathrm{bridge}}^T H_{\Phi_F}(K_{\mathrm{bridge}}v)
K_{\mathrm{bridge}}
=\alpha H_{\Phi_{\mathrm{primitive}}}(v),
\]
so
\[
\det H_{\Phi_F}(K_{\mathrm{bridge}}v)
=\frac{\alpha^{14}}{(\det K_{\mathrm{bridge}})^2}
\det H_{\Phi_{\mathrm{primitive}}}(v).
\]

This preserves the scalar-square-modulo-cubic conclusion. I checked this determinant transport exactly at the strict fake witness.

## 3. Polynomiality and degree: the denominator argument is valid

The proof in `organized/research/HMSV_COMPATIBILITY.md:63–87` works globally.

In the order \(c,A,B\), the Hessian is

\[
H(c)=
\begin{pmatrix}
0&0&v^T\\
0&M&N\\
v&N^T&Q+cK
\end{pmatrix},
\qquad
v=72\nabla D,\quad K=72H_D.
\]

Only the \(B\)-block depends on \(c\). A determinant term must use a \(B\)-column for the \(c\)-row and a \(B\)-row for the \(c\)-column. At most three remaining factors can therefore contribute \(c\):

\[
\deg_c\det H(c)\le3.
\]

The cubic coefficient is

\[
[c^3]\det H(c)=-\det(M)\,v^T\operatorname{adj}(K)v.
\]

For \(D=pt-qr\), in row-major coordinates, \(\det H_D=1\), and the exact identity is

\[
v^T\operatorname{adj}(K)v=2\cdot72^5D.
\]

Therefore

\[
[c^3]\det H(c)=-2\cdot72^5D\det M.
\]

I independently checked the symbolic block identities and adjugate identity. An additional exact interpolation at an independently chosen point with \(D=17\) confirmed degree three and the stated leading coefficient; that interpolation is a cross-check, not the proof of the global bound.

To make denominator clearing completely explicit, write

\[
\det H(c)=a_0+a_1c+a_2c^2+Db_3c^3,
\qquad b_3=-2\cdot72^5\det M.
\]

Then substitution of \(c_*=-\Phi_0/(72D)\) gives

\[
J
=D^2a_0-\frac{Da_1\Phi_0}{72}
+\frac{a_2\Phi_0^2}{72^2}
-\frac{b_3\Phi_0^3}{72^3}.
\]

This is visibly polynomial over \(\mathbb Q\); no residual denominator remains.

Every term has degree \(18\). The transported strict fake witness has

\[
D=\frac{262540407}{2500}\ne0,\qquad
\Phi_F=0,\qquad
\det H_{\Phi_F}\ne0.
\]

I independently checked these facts, including the exact determinant congruence. Thus \(J\ne0\), making its degree genuinely \(18\), as claimed at `organized/research/HMSV_COMPATIBILITY.md:97`.

## 4. Square-root deduction: valid, but name the field explicitly

This is the principal exposition correction needed at `organized/research/HMSV_COMPATIBILITY.md:89–97`.

On the chart \(D\ne0\), substituting \(c_*\) into the imported congruence gives an equality in the rational function field:

\[
J=\kappa\bigl[D\,S_7(c_*,A,B)\bigr]^2.
\]

Let
\[
R=\mathbb C[A_{00},\ldots,A_{22},B_{00},\ldots,B_{11}].
\]
This is a UFD. For
\[
r=D\,S_7(c_*,A,B)\in\operatorname{Frac}(R),
\]
every irreducible-factor valuation satisfies

\[
2\nu(r)=\nu(J)\ge0.
\]

Since \(\kappa\) is a nonzero constant, it contributes no polynomial-factor valuation. Hence \(r\in R\). Homogeneity gives degree nine, and nonzero \(J\) ensures a nonzero root.

**Important distinction:** this UFD argument occurs in the ordinary thirteen-variable polynomial ring, not in the cubic’s coordinate ring. It does not require importing factoriality of that quotient for this step.

### Recommended field wording

State initially:

> There are \(N_9\in\mathbb C[A,B]\setminus\{0\}\) and \(\kappa\in\mathbb C^\times\) such that \(J=\kappa N_9^2\).

Then explain descent. Because \(J\in\mathbb Q[A,B]\), its geometric square property implies even multiplicities of its irreducible factors over \(\mathbb Q\), in characteristic zero. Consequently one can normalize

\[
J=\kappa_{\mathbb Q}N_{9,\mathbb Q}^{\,2},
\quad
N_{9,\mathbb Q}\in\mathbb Q[A,B],
\quad
\kappa_{\mathbb Q}\in\mathbb Q^\times.
\]

In particular, a real-coefficient root up to a nonzero real scalar exists. The scalar may change when the root is renormalized.

Do **not** infer \(\kappa>0\), or that \(J\) itself has a real polynomial square root without a scalar. Indeed, my strict-fake evaluation gives \(J<0\). In any real scalar-square normalization, that witness forces the scalar to be negative.

No expanded nonic or irreducibility claim is needed. The restraint in `organized/research/HMSV_COMPATIBILITY.md:97` is correct.

## 5. Extension through \(D=0\): valid on actual parameters

The density argument at `organized/research/HMSV_COMPATIBILITY.md:99–101` is legitimate.

On \(D\ne0\), an actual real profile satisfies the cubic and singular-Hessian equations, so its constant coordinate is \(c_*\), and \(J=0\).

The pullback of \(J\) to the real and imaginary parts of \(a,b,\eta\) is polynomial. Independently evaluating the displayed actual witness gave

\[
D=-86400\ne0.
\]

Thus the pullback of \(D\) is not the zero polynomial. Its nonvanishing set is dense in the full real parameter space, and the polynomial pullback of \(J\), vanishing there, vanishes identically.

**Clarification:** this is density in the unrestricted actual parameter space—not an assertion that every fixed support/contact stratum has a dense \(D\ne0\) subset. The universal polynomial identity can subsequently be restricted to supported data. No supporting permutation needs to remain fixed.

At \(D=0\), \(J=0\) remains only necessary. Recovering a score requires \(\Phi_0=0\) and further height/lifting conditions. The document correctly refuses division or sufficiency there.


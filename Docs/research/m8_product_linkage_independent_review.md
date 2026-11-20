## 2. Product span, basis, and full gap map — VALID

The 24 products have a **70×24 coefficient matrix of rank 14**, and lexicographic pivot selection gives exactly

```text
0123, 0132, 0213, 0231, 0312, 1023, 1032,
1203, 1230, 1302, 2013, 2031, 2301, 3012.
```

This confirms `organized/research/M8_PRODUCT_LINKAGE.md:14-17` and the construction at `organized/research/verify_m8_product_linkage.py:26-40`.

I independently confirmed that all 24 products have **integer** coordinates in this basis, and that each coordinate column sums to one. Thus, writing \(f_\pi=\sum_j a_{j\pi}v_j\),

\[
r_0-\sum_j a_{j\pi}r_j
=\sum_{j=1}^{13}a_{j\pi}(r_0-r_j).
\]

Consequently the sign and orientation of the saved map are correct:

\[
\Delta=L\gamma,\qquad L=(a_{j\pi})_{\pi,\ j=1,\ldots,13}.
\]

The saved **24×13** matrix equals the independently reconstructed matrix and has rank 13. This validates `organized/research/M8_PRODUCT_LINKAGE.md:19-23` and `organized/research/verify_m8_product_linkage.py:88-93`.

An important terminology distinction is already present later in the document: these are coordinates on the complete **linear gap space**. They do not mean that every point of that 13-dimensional space is actual spectral data. The actual real image has generic dimension 12.

## 3. Quadratic kernel and unique integrable cubic — VALID

Independent coefficient reconstruction gives:

| Object | Exact result |
|---|---:|
| Pair-product coefficient matrix | 1107×105 |
| Pair-product rank | 91 |
| Quadratic relation-space dimension | 14 |
| Closed-gradient/integrability matrix | 1081×196 |
| Integrability rank | 195 |
| Integrability kernel dimension | 1 |
| Final cubic monomials | 49 |
| Rank of final gradient coefficient vectors | 14 |

These confirm `organized/research/M8_PRODUCT_LINKAGE.md:25-27` and `organized/research/verify_m8_product_linkage.py:41-85`.

The uniqueness assertion has the appropriate meaning: **up to scalar, there is exactly one homogeneous cubic whose fourteen partial derivatives lie in this quadratic relation space**. It is not a claim that there is only one cubic vanishing on the product image.

The integrability procedure is mathematically sound. It parameterizes fourteen quadratic components and imposes equality of mixed partial derivatives. A closed homogeneous quadratic vector field integrates to a homogeneous cubic; Euler’s formula reconstructs it by summing coordinate times component, with an immaterial overall factor of three. Primitive normalization then fixes the displayed polynomial.

I also parsed the literal expression at `organized/research/M8_PRODUCT_LINKAGE.md:30-40`: it agrees exactly with the saved 49-term cubic.

Most importantly, I independently composed each derivative with the original eight-variable product map and obtained the **zero polynomial**, not merely zero at sampled spectra. The all-eight-symbol assertion at `organized/research/M8_PRODUCT_LINKAGE.md:43-47` is justified.

## 4. \(S_8\) covariance and the evaluation transpose — VALID

The transpose in the verifier is correct and essential.

Let \(m(x)\) be the column of squarefree degree-four monomials and let \(B\) contain the basis-product coefficient columns. Then

\[
v(x)=B^Tm(x).
\]

If variable permutation gives the coefficient identity \(B_\tau=BS\), then

\[
v(\tau x)=B_\tau^Tm(x)=S^Tv(x).
\]

Therefore the matrix acting on **evaluation-coordinate columns** is \(A=S^T\), exactly as implemented at `organized/research/verify_m8_product_linkage.py:105-110`.

For all seven saved matrices I independently checked:

- each transformed coordinate agrees with the corresponding product polynomial after swapping the actual \(x\)-variables;
- \(\Phi(A_\tau z)=-\Phi(z)\) as a polynomial in fourteen independent coordinates;
- \(A_\tau^2=I\);
- the commuting and braid relations for adjacent transpositions.

Thus `organized/research/M8_PRODUCT_LINKAGE.md:47` establishes actual skew covariance, not a representation guessed from its dimension. Because adjacent transpositions generate \(S_8\), the full covariance follows.

## 5. Universal cubic and singular-Hessian necessity — VALID, including degeneracies

The proof at `organized/research/M8_PRODUCT_LINKAGE.md:51-66` is correct independently of any singular-locus theorem.

Since \(\nabla\Phi\) is homogeneous quadratic,

\[
\nabla\Phi(\eta v(x))=\eta^2\nabla\Phi(v(x))=0,
\]

including \(\eta=0\). For \(w=r+is\), real coefficients and cubic degree give

\[
\nabla\Phi(r+is)
=\nabla\Phi(r)-\nabla\Phi(s)+iH_\Phi(r)s.
\]

Hence

\[
\nabla\Phi(r)=\nabla\Phi(s),\qquad H_\Phi(r)s=0.
\]

Symmetry of the cubic polarization gives

\[
r^T\nabla\Phi(s)=\tfrac12s^TH_\Phi(r)s.
\]

Combining this with Euler’s identity proves \(\Phi(r)=0\). I checked both abstract polarization identities symbolically in independent real vectors \(r,s\).

The singular-Hessian case split is complete:

- **\(s\ne0\):** \(s\) is a nonzero kernel vector.
- **\(s=0,\ r\ne0\):** \(\nabla\Phi(r)=0\), so \(H_\Phi(r)r=2\nabla\Phi(r)=0\).
- **\(r=s=0\):** the Hessian vanishes because its entries are linear.
- **\(r=0,\ s\ne0\):** again \(H_\Phi(0)=0\).

No division or nonvanishing pair-sum assumption enters. I additionally checked explicit real, purely imaginary, zero-\(\eta\), and zero-pair-sum examples.

The scope warning at `organized/research/M8_PRODUCT_LINKAGE.md:68` is necessary: these equations are **necessary only**. This audit does not establish that passing both equations produces actual spectra or even a real conjugate-secant representation.

## 6. Constant projection and exceptional chart — VALID

I independently confirmed

\[
\nabla\Phi(\mathbf1)=0,\qquad \operatorname{rank}H_\Phi(\mathbf1)=4,
\]

and the complete polynomial identity

\[
\Phi(c\mathbf1-(0,\gamma))
=cQ_2(\gamma)+C_3(\gamma),
\]

with **39 quadratic terms** and **35 cubic terms**. This validates `organized/research/M8_PRODUCT_LINKAGE.md:72-81` and the saved expressions at `organized/research/m8_product_linkage_verification.json:4107-4108`.

The chart distinction is correct:

- If \(Q_2\ne0\), there is exactly one cubic-compatible height, \(c=-C_3/Q_2\).
- If \(Q_2=0,\ C_3\ne0\), no height passes the cubic.
- If \(Q_2=C_3=0\), the cubic leaves the height undetermined; the Hessian condition must still be imposed with \(c\) retained.

There is no universal division by \(Q_2\).

Denominator clearing must preserve this distinction. A cleared polynomial evaluated on \(Q_2=0\) cannot automatically replace the retained-height problem. The present text does not make that mistake.

The projected nonic remains **unverified here**, exactly as stated at `organized/research/M8_PRODUCT_LINKAGE.md:83`.


## 8. Generic dimension — VALID, with the upper-bound argument made explicit

The three displayed generators are correct global **infinitesimal polynomial kernel identities**:

\[
(1,-1,0),\quad
(a,b,-4\eta),\quad
(a^2,-b^2,-\eta(\sum a-\sum b)).
\]

I independently differentiated the thirteen selected complex gap products and verified \(JK=0\) symbolically in all nine complex parameters. This confirms `organized/research/M8_PRODUCT_LINKAGE.md:114-120` and `organized/research/verify_m8_product_linkage.py:164-179`.

The generic-rank proof is sound:

- \(K\) has rank 3 at the witness, hence generically.
- Thus \(J\) has rank at most 6 on a dense open set.
- Every 7×7 minor of polynomial \(J\) consequently vanishes identically.
- Therefore exceptional parameter points cannot secretly have complex rank greater than 6.
- Exact rank 6 at the witness establishes generic complex rank 6.

For the actual real map \(h=\Re F\), the relevant differential is

\[
D_{\mathbb R}h=[\Re J\mid-\Im J],
\]

up to parameter-column ordering. It is **not enough** merely to realify the full complex-output map and observe rank 12. The verifier correctly checks the **13×18 real-output Jacobian** at `organized/research/verify_m8_product_linkage.py:180-182`.

My independent reconstruction also gave rank 12. In the ordering \([\Re\text{ parameters}\mid\Im\text{ parameters}]\), one 12×12 minor has determinant

```text
38854139786035200
```

The global complex bound gives real rank at most 12, and this minor gives the matching lower bound. Thus the actual real gap image has generic dimension **12 inside 13**, as claimed at `organized/research/M8_PRODUCT_LINKAGE.md:125`.

The local normal also checks exactly. It is not a global support inequality: using the displayed normal, I found strict actual identity-contact profiles with normal-dot-gap values **10,311,264** and **−69,299,664**, respectively, with positive minimum gaps 56 and 20.

Finally, the witness Hessian rank 12 does **not** establish a universal rank-12 statement. The document explicitly avoids that inference at `organized/research/M8_PRODUCT_LINKAGE.md:130`. The universal argument used here establishes singularity, hence rank at most 13—not a stronger uniform bound.


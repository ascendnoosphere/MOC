## 1. Exact determinant reduction

The proof in `organized/research/RECTANGULAR_COMPRESSION_REDUCTION.md:26–51` is sound.

With \(E:\mathbb C^{n-1}\to\mathbb C^n\) the coordinate inclusion, set
\[
D=\operatorname{diag}(a_i-a_n)_{i<n},\qquad
C=U\operatorname{diag}(a_n+b_j)U^*.
\]
Then, exactly,
\[
D_a+UD_bU^*=C+EDE^*.
\]

Under the displayed nonzero assumptions, both \(C\) and \(D\) are invertible. Sylvester’s identity gives
\[
\begin{aligned}
\det(C+EDE^*)
&=\det C\,\det(I_n+C^{-1}EDE^*)\\
&=\det C\,\det(I_{n-1}+DE^*C^{-1}E)\\
&=\det C\,\det D\,
  \det(D^{-1}+E^*C^{-1}E).
\end{aligned}
\]
The last step factors \(D\) **on the left**; it does not commute \(D\) through another matrix.

Because \(W=E^*U\),
\[
E^*C^{-1}E
=W\operatorname{diag}\bigl((a_n+b_j)^{-1}\bigr)W^*.
\]
Also \(\det C=\prod_j(a_n+b_j)\), since unitary conjugation contributes no determinant phase. Thus the multiplier is exactly
\[
L=\prod_{i<n}(a_i-a_n)\prod_j(a_n+b_j).
\]

There is no missing conjugation, sign, modulus, or unitary-determinant factor. In particular, this is an ordinary inverse \(C^{-1}\), not an adjoint inverse or entrywise conjugate reciprocal.

## 2. Comparison products and complex support directions

The product identity and permutation–injection correspondence in `organized/research/RECTANGULAR_COMPRESSION_REDUCTION.md:53–60` are also correct.

For an injection \(\iota:\{1,\ldots,n-1\}\to\{1,\ldots,n\}\),
\[
L\prod_{i<n}(x_i+y_{\iota(i)})
=
\left(\prod_{j\notin\operatorname{im}\iota}c_j\right)
\prod_{i<n}(d_i+c_{\iota(i)}).
\]
There is exactly one unused index. Assigning it to \(\pi(n)\) uniquely completes \(\iota\) to a permutation, producing precisely the square comparison product.

Consequently:

- There are exactly \(n!\) indexed products on each side.
- No comparison products are added or discarded.
- Coincident products in degenerate cases cause no problem.
- Every product receives the **same** scalar \(L\).

Complex multiplication by nonzero \(L\) preserves convex hulls with real, nonnegative coefficients. To make the support-direction statement completely explicit, under
\[
h_S(\eta)=\max_{z\in S}\operatorname{Re}(\overline\eta z),
\]
one has
\[
h_{LS}(\eta)=h_S(\overline L\,\eta).
\]
For unit \(\eta=e^{i\theta}\), this is
\[
h_{LS}(e^{i\theta})
=|L|\,h_S(e^{i(\theta-\arg L)}).
\]

Thus the phase is transferred to the original support direction, not optimized independently. No extra phase or budget appears.

**Presentation suggestion:** at `organized/research/RECTANGULAR_COMPRESSION_REDUCTION.md:60`, “preserves convex combinations in the complex plane” would be less ambiguous than “preserves complex convex combinations.” The coefficients remain real and nonnegative.

## 3. Both implications and all degenerate cases

The two directions in `organized/research/RECTANGULAR_COMPRESSION_REDUCTION.md:64–72` are valid.

**Rectangular to square:** for fixed \(U\), the conditions
\[
a_i-a_n\ne0,\qquad a_n+b_j\ne0
\]
exclude finitely many proper complex hyperplanes. Their complement is dense. Apply the identity there, then pass to the limit in the **original square determinant and square vertex list**.

**Square to rectangular:** every coisometry \(WW^*=I_{n-1}\) has orthonormal rows and can be completed to a unitary \(U\) with exactly those first rows. For nonzero \(x_i,y_j\), the choices
\[
a_n=0,\qquad a_i=x_i^{-1},\qquad b_j=y_j^{-1}
\]
satisfy all required invertibility assumptions. Division by the common nonzero \(L\) proves the rectangular membership.

For zeros, keeping \(W\) fixed while perturbing \(x,y\) to nonzero entries is sufficient. The limiting objects are
\[
\det(D_x+WD_yW^*)
\quad\text{and}\quad
\prod_{i<n}(x_i+y_{\iota(i)}),
\]
which remain finite and continuous. The reciprocal square spectra may diverge; the proof never needs their convergence.

The finite-hull closure argument is rigorous: coefficient vectors belong to
\[
\{\lambda\in\mathbb R^{n!}:\lambda_\pi\ge0,\ \sum_\pi\lambda_\pi=1\},
\]
a compact simplex. A convergent subsequence gives a limiting convex representation. This handles repeated entries, coincident vertices, and vanishing factors without evaluating a reciprocal at zero.


## 5. Möbius reduction cross-check

The ordered matrix identity and scalar \(K\) in `organized/research/MOBIUS_REDUCTION.md:9–35` are correct. The \(AY\) terms cancel in the stated order; commutativity of \(A,Y\) is unnecessary. Normality of \(f(A)\) and \(-f(-B)\) follows from diagonal functional calculus whenever their denominators are invertible.

The density and limiting argument in `organized/research/MOBIUS_REDUCTION.md:48–59` is likewise adequate. It transfers membership back to finite original data before taking exceptional limits; transformed spectra need not remain bounded.

**Minor notation caveat:** in `organized/research/MOBIUS_REDUCTION.md:41–44`, \(r(a_3)\) is undefined, so \(f(a_3)=1\) uses the rationally simplified Möbius map, not literal sequential finite evaluation. Explicitly,
\[
f(t)=
\frac{(t-a_1)(a_2-a_3)}
{(t-a_1)(a_2-a_3)+(t-a_3)(a_2-a_1)}.
\]
Its denominator at \(a_3\) is nonzero for the stipulated distinct triple. Stating this cancellation would remove a superficial pole ambiguity; it does not change the validity of the reduction.

The all-\(b\) obligation remains correctly stated in `organized/research/MOBIUS_REDUCTION.md:63–72`.


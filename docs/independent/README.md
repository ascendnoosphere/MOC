# Marcus–de Oliveira: independent restricted families and exact reductions

16 October 2026

**Scope:** The results below are proved special cases and exact equivalent reductions, with independent checks. They do not prove the unrestricted conjecture. No novelty claim is made for the special cases.

## Reading guide

- This page gives explicit convex certificates and the one-variable elimination argument.
- [Rank-two notes](rank_two_notes.md) develop the corresponding restricted family.
- [Referee notes](referee_notes.md) record the independent checks and their hypotheses.
- [Exact checkers](../../code/independent/exact/) accompany the certificates below. Run commands from the repository root.
- [Broader families](../broader/README.md) collect later Fourier and neighborhood results.

The target is

\[
\det(A+UBU^*)\in\operatorname{conv}
\left\{\prod_{j=1}^n(a_{\pi(j)}+b_j):\pi\in S_n\right\},
\]

with arbitrary complex diagonal matrices A,B and unitary U.

## 1. An exact family with four explicit convex weights

Let

\[
M=\begin{pmatrix}
1&-2&-2&-2\\2&1&-2&2\\2&2&1&-2\\2&-2&2&1
\end{pmatrix},\qquad U=M/\sqrt{13},
\]

\[
A(t)=\operatorname{diag}(0,1,2,t),\qquad
B(s)=\operatorname{diag}(0,1,is,2+is).
\]

Here t is any complex number. Define four permutation vertices using one-based tuples (pi(1),...,pi(4)):

| Permutation | Vertex |
|---|---|
| (1,3,4,2) | z1 = 0 |
| (3,4,1,2) | z2 = (-2s²+6is)(1+t) |
| (3,4,2,1) | z3 = (4-2s²+6is)(1+t) |
| (4,1,3,2) | z4 = (6-s²+5is)t |

Then the polynomial identity

\[
\boxed{\det(A(t)+UB(s)U^*)
=\frac{29z_1+(52-3s^2)z_2+(36+3s^2)z_3+52z_4}{169}}
\]

holds for all complex s,t. For real s satisfying 3s²≤52, its weights are real, nonnegative, and sum to one. Thus it proves the conjecture for this entire family.

Verification is elementary and exact. MMᵀ=13I and det M=169. Consequently

\[
\det(A+UBU^*)=\frac{\det((a_i+b_j)M_{ij})}{169}.
\]

Expanding the numerator gives

\[
144-164s^2+528is+(456-216s^2+788is)t.
\]

The displayed weighted sum has precisely these coefficients; its degree-three and degree-four terms in s cancel. The verifier uses integer pairs for Gaussian integers and dictionaries for polynomial coefficients. It does not use floating-point arithmetic.

For s≠0, B(s) has simple, noncocircular spectrum: the circle through 0,1,is is x²+y²−x−sy=0, while 2+is gives 2 in that equation. For Im(t)≠0, A(t) also has simple spectrum not contained in a circle or line. This does not establish the result for arbitrary spectra at this U, let alone for arbitrary U.

Run:

```bash
python code/run.py independent/exact/verify_two_parameter_family.py
python code/run.py independent/exact/verify_finite_family.py
```

## 2. Eliminating one complex spectral variable exactly

Suppose, with all other data fixed,

\[
d(t)=D_0+tD_1,\qquad z_\pi(t)=Z_{\pi,0}+tZ_{\pi,1}.
\]

Then

\[
d(t)\in\operatorname{conv}\{z_\pi(t)\}\quad\text{for every }t\in\mathbb C
\]

is equivalent to

\[
(D_0,D_1)\in\operatorname{conv}\{(Z_{\pi,0},Z_{\pi,1})\}\subset\mathbb C^2.
\]

One direction follows by applying the affine evaluation map. For the converse, a strictly separating real functional on C² has the form Re(c0 x+c1 y). If c0≠0, evaluate at t=c1/c0 to contradict the assumed inclusion. If c0=0, perturb c0 slightly: strict separation survives because the vertex set is finite. This proves the equivalence without invoking MOC.

For n=4, use homogeneous spectral coordinates a_i=alpha_i/gamma_i and b_j=beta_j/delta_j. Define S_ij=alpha_i delta_j+gamma_i beta_j. The quantities

\[
d=\det(S\circ U)/\det U,\qquad z_\pi=\prod_j S_{\pi(j),j}
\]

are the ordinary determinant and pairing vertices multiplied by the same nonzero scalar whenever denominators are nonzero. Taking A projectively as (0,1,infinity,t), S has rows beta, beta+delta, delta, beta+t delta. The determinant and every vertex are affine in t, so the preceding four-dimensional hull test applies.

Infinite coordinates do not create spurious examples. For a scalar c avoiding finitely many zeros, set

\[
a_i'=\frac{\alpha_i}{\alpha_i+c\gamma_i},\qquad
b_j'=\frac{\beta_j}{c\delta_j-\beta_j}.
\]

All new determinants and vertices are the homogeneous ones multiplied by

\[
\frac{c^n}{\prod_i(\alpha_i+c\gamma_i)\prod_j(c\delta_j-\beta_j)}.
\]

The new spectra are finite, so the hull test has its usual normal-matrix interpretation.

## 3. An explicit cyclic-shift certificate

The cyclic-shift family has an explicit MOC certificate. Let Q be the cyclic shift and omega=exp(2pi i/n). For arbitrary diagonal A,

\[
\det(A+tQ)=\prod_i a_i+(-1)^{n-1}t^n
=\frac1n\sum_{k=0}^{n-1}\prod_{i=0}^{n-1}(a_i+t\omega^{i+k}).
\]

Only the diagonal and full-cycle permutations contribute to the determinant. Averaging the vertices kills every mixed term by the roots-of-unity filter. For the primitive odd-dimensional clock–shift block I−2P+2Q, the determinant is 1, itself a pairing vertex obtained by cancellation. These are explicit positive certificates for the stated cyclic-shift families.

Source: https://arxiv.org/html/2609.15567v1

## 4. A full arbitrary-spectrum certificate at the Fourier eigenbasis F5

Let F_ij=omega^(ij)/sqrt(5), with indices in F5. Give the twenty affine permutations pi_(r,s)(j)=rj+s the weights

\[
p_{r,s}=\frac2{25}\sin^2(\pi r/5),\qquad r=1,2,3,4,\ s\in\mathbb F_5.
\]

The weights sum to one. Each singleton image event has probability 1/5. For two-element input and output sets with differences c,d, exactly two affine maps work, with slopes ±d/c. Their probability sum is

\[
\frac4{25}\sin^2(\pi(d/c)/5)
=\frac4{25}\sin^2(\pi dc/5)
=|\det F_{I,J}|^2.
\]

Here c²=±1 in F5. Complementation gives the remaining minor sizes. Therefore these weights reproduce all squared minors for this particular U, and the determinant expansion proves MOC for arbitrary spectra at F5. The construction was independently refereed.


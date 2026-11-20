# Exact pair rotations for determinant support optimization

For complex spectra $a,b$ and a unitary $U$, put

$$
B=U\operatorname{diag}(b)U^*,\qquad
F(U)=\operatorname{Re}\{\eta\det(\operatorname{diag}(a)+B)\},\qquad |\eta|=1.
$$

A rotation of two rows of $U$ can be optimized exactly with four determinant evaluations. This statement holds in every dimension and does not assume that the spectra are real. It gives an implementable coordinate ascent method. It does not establish MOC or identify a global maximum.

## Lemma and proof

Fix rows $i,j$ and let $R(t,\phi)$ be the identity outside them, with block

$$
R(t,\phi)=
\begin{pmatrix}
\cos t&\sin t\,e^{i\phi}\\
-\sin t\,e^{-i\phi}&\cos t
\end{pmatrix}.
$$

There are real numbers $c,A,B_x,B_y$ such that

$$
F(R(t,\phi)U)
=c+A\cos(2t)+(B_x\cos\phi+B_y\sin\phi)\sin(2t).
\tag{1}
$$

Indeed, conjugating the matrix in the determinant gives

$$
\det(D_a+RBR^*)=\det(R^*D_aR+B).
$$

Only a $2\times2$ block $X$ of $R^*D_aR$ varies. Expand the determinant using its entries. Terms that use no entry of $X$ are constant. Terms that use one are linear in $X$. The terms that use two equal $\det(X)$ times the complementary principal minor. Since $\det(X)=a_i a_j$ is fixed, the restricted determinant is affine in the four entries of $X$. Explicitly,

$$
X=\frac{a_i+a_j}{2}I+
\frac{a_i-a_j}{2}
\begin{pmatrix}
\cos(2t)&\sin(2t)e^{i\phi}\\
\sin(2t)e^{-i\phi}&-\cos(2t)
\end{pmatrix}.
$$

Taking the real part after multiplication by $\eta$ proves (1). The argument uses no inverse and therefore also holds at singular matrices. If $a_i=a_j$, all three variable coefficients vanish.

Write $f_{t,\phi}=F(R(t,\phi)U)$. Recover the coefficients by

$$
\begin{aligned}
c&=(f_{0,0}+f_{\pi/2,0})/2,&
A&=(f_{0,0}-f_{\pi/2,0})/2,\\
B_x&=f_{\pi/4,0}-c,&
B_y&=f_{\pi/4,\pi/2}-c.
\end{aligned}
$$

The vector $(\cos2t,\sin2t\cos\phi,\sin2t\sin\phi)$ ranges over the unit sphere. Therefore the exact pair maximum is

$$
\max_{t,\phi}F(R(t,\phi)U)=c+\sqrt{A^2+B_x^2+B_y^2}.
\tag{2}
$$

One maximizing choice is

$$
\phi=\operatorname{atan2}(B_y,B_x),\qquad
 t=\tfrac12\operatorname{atan2}(\sqrt{B_x^2+B_y^2},A).
$$

If $B_x=B_y=0$, choose $t=0$ for $A\ge0$ and $t=\pi/2$ for $A<0$. If all coefficients vanish, every choice has the same support. For real orthogonal mixing, set $\phi=0$; three evaluations give the maximum $c+\sqrt{A^2+B_x^2}$ and $t=\frac12\operatorname{atan2}(B_x,A)$.

At the current matrix, pair stationarity requires $B_x=B_y=0$ and pair maximality additionally requires $A\ge0$. These conditions address one pair at a time. They do not control coupled directions or compare different permutations.

## Algorithm and limits

Cycle through row pairs and replace each pair by the maximizer (2). Each accepted step increases or preserves the support. The implementation also evaluates the proposed update and rejects decreases caused by floating point error. It stops when a complete sweep improves the normalized support by less than $3\times10^{-15}$ or after 80 sweeps. Near repeated eigenvalues, recovering tiny coefficients still suffers subtraction error; exact coordinate optimization does not remove floating point limitations.

A coordinate maximum need not be globally optimal. The present sample includes three outputs near suboptimal permutation matrices: one at $n=5$ and two at $n=6$. Their normalized support deficits are approximately $2.55\times10^{-5}$, $3.64\times10^{-4}$, and $5.74\times10^{-4}$. Reaching a permutation is compatible with MOC even when that permutation does not maximize the selected support.

The repository also has an exact four-dimensional obstruction in `docs/research/session_variational.txt`: for $\eta=1$, $a=(2+5i,2-3i,-2+i,5+4i)$ and $b=(1+i,-2+2i,3+3i,1-5i)$, the identity permutation has support 129, and every transposition decreases it, by respectively $472,96,42,1104,1218,126$. The permutation $(2,1,4,3)$ has support 1099. The identity is a strict local maximum on the unitary orbit, because its tangent Hessian has these strictly negative pair curvatures and no mixed terms. Thus even strict local maximality does not imply global maximality at $n=4$. Both determinants are permutation products, so this is fully consistent with MOC.

At a permutation, rotation of a row pair traces the segment between its determinant product and the product for the corresponding transposition. Thus pair maximality becomes the finite condition that no transposition improves the permutation. This is weaker than maximization over all permutations.

## The 2026-10-31 numerical campaign

The adversarial search ran 3,189 BFGS optimizations over 532 spectral instances. Each comparison enumerated the complete permutation hull. The spectra came from Gaussian, unit-circle, near-real, near-pair-cancellation, and clustered families. The $n=4$ searches used both real orthogonal and complex unitary frames; $n=5,6$ used complex unitary frames. This is a finite sample of unrestricted complex-spectrum instances, not exhaustive coverage.

| Dimension | Optimizations | Spectral instances | Maximum normalized support excess |
|---|---:|---:|---:|
| 4 | 1,596 | 266 | $7.91\times10^{-16}$ |
| 5 | 798 | 133 | $1.17\times10^{-15}$ |
| 6 | 795 | 133 | $1.15\times10^{-15}$ |

The normalization is

$$
\frac{\operatorname{Re}(\eta d)-\max_\pi\operatorname{Re}(\eta z_\pi)}{\max_\pi|z_\pi|},
\quad d=\det(D_a+UD_bU^*),\quad z_\pi=\prod_i(a_i+b_{\pi(i)}).
$$

No optimized point lay outside its complete hull at tolerance $10^{-8}$. The largest complete-hull excess was $1.33\times10^{-15}$. Unit-circle inputs have collinear permutation products; the code checks their segment bounds and perpendicular residual instead of treating a failed two-dimensional hull construction as evidence of a violation.

The search retained 45 nonmonomial candidates for which a random support direction had intrinsic gradient norm below $2\times10^{-6}$. All 45 came from clustered spectra. Their count by dimension was 23, 10, and 12. Exact pair polishing moved all 45 to matrices with

$$
n-\sum_{ij}|U_{ij}|^4<10^{-4};
$$

the largest final score was $5.40\times10^{-5}$. All 23 four-dimensional examples reached the global permutation support to within $1.56\times10^{-15}$. Thirty-nine of the 45 improved support by more than $10^{-10}$.

Thirty-five candidates had a positive eigenvalue above $10^{-10}$ in the analytic intrinsic tangent Hessian. These are numerical saddle findings, not exact certificates; a small gradient alone does not certify stationarity or local maximality. The observed candidates therefore give no evidence that nonmonomial local maxima govern this sample. Clustered spectra make some mixing directions nearly flat and can satisfy a gradient stopping criterion prematurely.

The pair formula agreed with direct determinant evaluation within $7.78\times10^{-16}$. Analytic Givens gradients agreed with finite differences within $1.38\times10^{-10}$. Three independent 70-digit directional derivative checks verified the intrinsic Hessian to $1.62\times10^{-15}$. An 80-digit determinant/support check agreed with its double-precision value to $1.1\times10^{-16}$.

## Reproduction and records

Run from the repository root with one BLAS thread:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 python code/research/moc_campaign_adversarial.py --seconds 290 --max-trials 5000
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python code/research/moc_campaign_stationarity.py
```

The wall-clock limit makes the last trial depend on machine load. Campaign seed 2026103107 and per-instance seeds preserve the generated cases.

- `code/research/moc_campaign_adversarial.py`: complete-hull search, intrinsic gradient, degenerate-hull handling, and 80-digit recomputation of suspected excesses.
- `code/research/moc_campaign_stationarity.py`: `rotation`, `hessian`, and `polish` implement the pair formula and the stationarity audit.
- `build/moc_campaign_20261031/adversarial.jsonl`: one record per optimization, including support/hull excesses, gradients, optimizer status, and frame mixing.
- `build/moc_campaign_20261031/adversarial.metadata.json`: counts and gradient checks.
- `build/moc_campaign_20261031/adversarial_examples.json`: spectra, matrices, angles, and support directions for all 45 candidates.
- `build/moc_campaign_20261031/adversarial_stationarity.json`: before/after gaps and mixing, Hessian extrema, nearest permutations, and transposition gains.
- `build/moc_campaign_20261031/adversarial_suspects.json`: empty; no apparent excess triggered the high-precision suspect path.
- `build/moc_campaign_20261031/adversarial_precision_check.json` and `adversarial_hessian_check.json`: independent precision checks.

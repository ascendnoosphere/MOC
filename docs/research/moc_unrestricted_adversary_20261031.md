# Joint spectra, unitary, and support adversary for unrestricted MOC

31 October 2026. This experiment searches arbitrary complex spectra in dimensions
4, 5, 6, and 7. It produces no unrestricted proof and no MOC counterexample.
Its main useful finding is methodological: joint optimization commonly leaves
the nonordinary support region or approaches a reducible mixer. A search must
retain those features if it is to test a mechanism intended to handle them.

The immutable output contains 105 optimizer starts, 420 smoothing stages,
17,474 optimizer iterations, and 30,529 distinct cached state evaluations.
Those evaluations calculate 30,288,840 permutation products in total. Repeated
spectral controls, adaptive iterates, and smoothing stages are counted in those
totals; they are not independent random MOC instances. A preceding three-start
smoke run is retained separately as `joint_raw.jsonl` and is excluded throughout.

| Dimension | Fixed spectra | Joint, free | Joint, guarded | Permutations at each state |
| --- | ---: | ---: | ---: | ---: |
| 4 | 15 | 15 | 15 | 24 |
| 5 | 10 | 10 | 10 | 120 |
| 6 | 5 | 5 | 5 | 720 |
| 7 | 5 | 5 | 5 | 5040 |

All permutations are enumerated. There is no sampled inner-hull substitution.
The dimension-four seeds deliberately include the known actual nonordinary
spectra, the exact actual obstruction to the earlier three-budget triangle
rule, and the Walsh cubic saddle. Higher-dimensional seeds include complex
Gaussian, clustered, near-real, and near-cancelling spectra.

![Joint search landscape](../../build/moc_unrestricted_20261031/adversary/joint_adversarial_landscape.png)

For spectra (a,b\in\mathbb C^n), a unitary (U), and (|\eta|=1), write

\[
 z_\pi=\prod_i(a_i+b_{\pi(i)}),\qquad
 d=\det(\operatorname{diag}a+U\operatorname{diag}b\,U^*),\qquad
 s=\left(\frac1{n!}\sum_\pi|z_\pi|^2\right)^{1/2}.
\]

The exact quantity audited at every endpoint is

\[
 E=\frac{\Re(\eta d)-\max_\pi\Re(\eta z_\pi)}s.
\]

A positive (E) would violate the chosen support inequality. The largest
double-precision endpoint value was (1.4706983412\times10^{-16}). Reconstructing
its unitary from the saved Givens angles at 90 decimal digits gives

\[
 E=-3.2746468856891515968590836254\times10^{-17}.
\]

No endpoint has (E>10^{-8}). Eleven selected original endpoints, comprising
the closest free endpoint in each dimension and the seven endpoints accepted
within the guard tolerance, were independently replayed at 90 digits. All
have negative (E). These are pointwise arithmetic replays, not interval
certificates for surrounding neighborhoods.

The source normalization removes exactly the shift symmetry

\[
 a_i\mapsto a_i-c,\qquad b_j\mapsto b_j+c,
 \qquad c=(\operatorname{mean}a-\operatorname{mean}b)/2,
\]

and then uses a positive common scale to set

\[
 \sum_i|a_i|^2+\sum_j|b_j|^2=2n.
\]

The shift preserves every sum (a_i+b_j) and the matrix in the determinant.
Positive scaling multiplies the determinant and every product by the same
positive (n)-th power. Both operations preserve the support comparison.

The mixer is a product of the (n(n-1)/2) complex Givens rotations with pairs
in lexicographic order. Each pair has an angle and a phase. A right diagonal
unitary commutes with (operatorname{diag}b), so it need not be represented.
The support angle is an additional variable. Joint runs also vary all (4n)
real source coordinates before the gauge projection and normalization.

Analytic derivatives use

\[
 \partial_{a_i}d=\operatorname{adj}(C)_{ii},\qquad
 \partial_{b_j}d=(U^*\operatorname{adj}(C)U)_{jj},\qquad
 \dot d=\operatorname{tr}(\operatorname{adj}(C)\dot C),
\]

where (C=\operatorname{diag}a+U\operatorname{diag}b\,U^*). The permutation-product
derivatives use prefix and suffix products and never divide by a spectral sum.
They therefore remain defined when a factor vanishes. Near a singular (C),
the code evaluates polynomial cofactors directly. Gradients are pulled back
through the source normalization. Centered-difference checks cover all 12
dimension/mode combinations. The largest objective error is

\[
 7.87\times10^{-8},
\]

and the largest constraint-Jacobian error is (1.43\times10^{-7}).

Optimization uses a smooth maximum, followed by the separate exact finite
maximum audit. With (v_\pi=\Re(\eta z_\pi)/s), the minimized function is

\[
 L_\tau=\tau\log\sum_\pi e^{v_\pi/\tau}-\Re(\eta d)/s,
 \qquad
 \tau\in\{0.015,0.0015,0.00015,0.000015\}.
\]

The explicit regularization error satisfies

\[
 0\le L_\tau+E\le\tau\log(n!).
\]

At the final temperature this upper bound reaches approximately

\[
 1.28\times10^{-4}\quad(n=7).
\]

Consequently a small positive endpoint deficit is not evidence that a
positive uniform gap exists, even after imposing the guards. Local optimization
can also stop above the infimum. Every numerical conclusion here concerns the
displayed endpoints and search behavior.

To prevent the simplest limiting escapes, guarded runs impose

\[
 \gamma=1-\sigma_2(|U|^2)\ge0.08,
 \qquad\min_{i<j}|a_i-a_j|,\ \min_{i<j}|b_i-b_j|\ge0.12,
\]

and require the ratio of minor to major RMS axes of the complex product cloud
to be at least (0.035). The singular value concerns the real doubly stochastic
matrix (|U|^2). A block-reducible probability matrix has a second singular
value of one, so (gamma=0). The connectivity guard excludes that exact
limiting mechanism.

For the two hostile dimension-four source families, guarded runs additionally
require

\[
 \min_{w\in\mathcal W}w\cdot
 \frac{\max_\pi\Re(\eta z_\pi)-\Re(\eta z)}s\le-0.025,
\]

where (mathcal W) is the exact relabeling orbit of the archived ordinary-cone
dual. The implementation verifies that every such dual is nonnegative on the
34 ordinary rays. A negative value detects a support cost outside that cone.

Of 35 guarded starts, seven meet all constraints within the recorded

\[
 2\times10^{-6}
\]

optimization feasibility tolerance. The other 28 are retained in the raw data
and excluded from guarded endpoint conclusions. High-precision replay shows
that six of the seven tolerance-accepted points have (gamma) slightly below
the exact (0.08) threshold, by (3.4\times10^{-8}) to (9.5\times10^{-7}).
Only the original dimension-seven trial 62 strictly meets all decimal
thresholds at 90 digits.

This shortfall was repaired without another broad search. For each of the
seven saved endpoints, the audit applies one minimum-norm correction using
the Jacobian of its active guards and then recomputes every constraint. The
parameter displacements are between (1.04\times10^{-5}) and

\[
 5.10\times10^{-5}.
\]

All seven corrected points have positive guard slack of approximately

\[
 5\times10^{-6},
\]

and all seven retain negative support excess at 90 digits. The original raw
endpoints remain unchanged. These repairs are separate artifacts, not seven
additional optimizer starts.

![Repaired nonordinary endpoint](../../build/moc_unrestricted_20261031/adversary/retained_nonordinary_endpoint.png)

For the corrected dimension-four trial 14, the numerical values are

\[
\begin{aligned}
 -E&=0.00024840979998926160516774719698547\ldots,\\
 \gamma&=0.08000500011427003919080134528768\ldots,\\
 \text{cloud aspect}&=0.33316653887352225804318106308264\ldots,\\
 \text{minimum spectral separation}&=0.12257362104355642134145585384368\ldots.
\end{aligned}
\]

Its ordinary-cone dual minimum remains below (-0.025). It is a useful
fully retained hostile input for future global mechanisms. Its validity does
not establish a lower bound over the whole guarded parameter space.

The main observed structural pattern is more robust than the fitted gap sizes.
Of 35 joint-free endpoints, 31 have (gamma<10^{-8}), and 30 have support
deficit below (10^{-8}). The remaining cases approach spectral collisions,+a thin product hull, or a visibly suboptimal value. All 15 dimension-four
joint-free endpoints have ordinary support costs at the end, although five
started with nonordinary costs. Thus an unconstrained joint counterexample
search can repeatedly optimize away the very source geometry that a proposed
full proof still needs to control. A productive next test should preserve the
actual complex source, nonordinary support, and mixer connectivity together.
These observations do not prove equality rigidity or convergence to commuting
global maximizers.

The Walsh control is deliberately retained as a negative control for a
variational proof rule. With

\[
 a=(1,-1,-3i,3i),\quad b=(-3,3,-i,i),\quad\eta=i,
\]

the archived dense Walsh mixer has support 24 and a negative semidefinite
nongauge Hessian with eigenvalues (-96) six times and zero six times. Its
coupled path has support

\[
 24+384\cos(\sqrt3t)
 \left(\frac{\sin(\sqrt3t)}{\sqrt3}\right)^3.
\]

The first and second derivatives vanish, while the third derivative is
positive. It reaches permutation support 48. The new experiment replays that
formula on 301 path points with residual below (5\times10^{-12}); its exact
algebraic proof remains the earlier archived checker. A pair-coordinate or
Hessian-only stopping rule would therefore be an unsuitable proof certificate.

Reproduction:

```sh
python code/research/moc_unrestricted_adversary_joint.py --starts 105 --seconds 420 --maxiter 75 --label campaign
python code/research/moc_unrestricted_adversary_audit.py
python code/research/moc_unrestricted_adversary_visualize.py
```

The search appends its raw file. Use a new label or an empty output directory
for an additional independent run. The saved campaign used seed 2026103193
and one BLAS thread; its wall time was approximately 222 seconds. Runtime
limits can change the completed schedule on another machine.

Artifacts are under

[`build/moc_unrestricted_20261031/adversary/`](../../build/moc_unrestricted_20261031/adversary/):

- `campaign_raw.jsonl`: all original inputs, endpoints, products, unitary angles,
  stage statuses, and iterative traces.
- `campaign_summary.json`: gradient checks, mode/dimension totals, the exact
  control replay, and the first selected high-precision replays.
- `endpoint_precision_and_guard_audit.json`: 11 original 90-digit replays,
  feasibility accounting, seven deterministic repairs, and their 90-digit
  replays.
- `joint_adversarial_landscape.png/.pdf` and
  `retained_nonordinary_endpoint.png/.pdf`: static shareable figures.

The remaining mathematical obligation is unchanged: prove that every actual
complex source and unitary satisfy every support inequality, or provide an
independently verified actual violation. This finite search does neither.

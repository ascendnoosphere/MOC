# Full91 quartic laws and nonlinear first-moment repairs

31 October 2026 — unrestricted complex spectra, four-by-four physical mixer.

No positive law uniform in the physical mixer is proved here. Neither the
full91 nor mixed77 quartic Born-law model is refuted by this work. The exact
negative results below concern four explicitly defined nonlinear formulas.

## An explicit uniform chirality56 positive kernel

There is a concrete positive source kernel beyond Gaussian35. For every
partition of eight labels into two unordered triples and one pair, put

```
h_[ijk],[lmn],[rs] = [ij][jk][ki] [lm][mn][nl] [rs]^2.
```

There are 280 such amplitudes. Every spinor occurs twice, so these are
degree-two sections of the **full** fourteen-generator source ring.
They give the manifest positive kernel

```
K56(x,t) = sum_partition h_partition(x) conjugate(h_partition(t)).
```

In the spin-one Veronese coordinates `q(t)=(1,t,t^2)`, with
`G=[[0,0,1],[0,-2,0],[1,0,0]]`, the identities

```
q(a)^T G q(b) = (a-b)^2,
det(q(a),q(b),q(c)) = (a-b)(b-c)(c-a)
```

express each amplitude as two epsilon contractions and one metric
contraction. Both identities are checked symbolically.

These 280 amplitudes vanish at every four-plus-four two-value collision
node. The 35 node-evaluation functionals have exact rank35, and the
amplitudes have exact evaluation rank56 over GF(1009). Since `dim R2=91`,
the upper and lower bounds agree: they span the entire degree-two ideal
of the 35 nodes. This proves an exact kernel construction, not only a
dimension proposal.

Fifty-six selected amplitudes have been exported in the original fourteen
source coordinates:

```
h56 = C^T q91,
q91_j = x_i*x_k,
C in Mat(91,56; Z),   max |C_ij| = 4.
```

The verification expands all 6561 possible affine-spinor monomials of
multidegree at most two and compares their integer coefficients. The
coefficient denominator is exactly one. This supplies explicit positive
square factors, including quadratic polynomial source information beyond
the physical Cartan8 projection. It does not exclude expressing sources
rationally through a suitable invertible physical-amplitude chart.

At both Q59 and the independent physical mixer R3701, the 35-by35 matrix
of Gaussian35 values on the collision nodes has exact rank35 over
GF(1009). Consequently

```
R2(full91) = physical Gaussian35  direct_sum  universal chirality56
```

at both mixers. More generally, for any mixer where this node matrix `N`
is invertible, a quadratic source section `q` has Gaussian interpolant
`g(x)^T N^(-1) (q(e_nu))_nu`; its remainder belongs to chirality56. The
invertibility condition is stated explicitly; no global nonvanishing
claim for `det(N)` is made.

The missing step remains the positive24 first-moment coupling. The
Gaussian35-only no-go does not address the full block matrix of effects
on `Gaussian35 + chirality56`, including its cross terms. A complete
56-state-only cone test after 1200 iterations is unresolved, with
coefficient residual `5.91e-5`; its positive kernel alone is not a MOC law.

Reproduce the kernel and its explicit source coordinates with

```
python code/research/moc_unrestricted_fierz_chirality56.py --coordinates
```

The generated certificates are `chirality56_exact.json` and
`chirality56_source_coordinates.json` in the Fierz build directory.

Four collision-node evaluations also align numerically with the four
small success directions of the full91 and mixed77 searches. This led to
deliberately postselecting the four nodes `(0123),(0257),(0367),(0156)`
away. The resulting 87-feature and 73-feature branches retain all source
variables. The best 87-state coefficient residual is `8.84e-7`, still
unresolved. The zeros have not been proved necessary or uniform in the
mixer. In particular, at Q59 the last three nodes have product values
`{0,1}` and physical determinants `81/3481,324/3481,324/3481`, respectively;
they are interior hull points, not outside-hull witnesses.

## A complete coefficient problem that retains all fourteen sources

Write the 24 permutation products as `z=F x` in the fourteen noncrossing
link coordinates, and the physical determinant as `d=y^T x`. Set
`delta_pi=z_pi-d`. Let `b(x)` be any basis for the full degree-two source
ring, and `c(x)` a basis for its degree-three ring. Their dimensions are
91 and 364. Multiplication by each linear `delta_pi` has a matrix
`M_pi: R2 -> R3`, characterized by

```
delta_pi(x) b(x)^T = c(x)^T M_pi.
```

The all-source quartic measurement problem is therefore

```
E_pi >= 0,  E_pi = E_pi^T,
sum_pi M_pi E_pi = 0,
sum_pi trace(E_pi) = 1.                                      (1)
```

These are 24 independently variable effects on the entire 91-dimensional
ring. The positive factors include the six external source coordinates;
they are not compressed to the physical eight amplitudes or Gaussian35.
The analogous mixed77 test uses the span of the 112 products `a_i*x_j`
modulo the same full source ideal.

If (1) holds, the nonnegative numbers

```
w_pi(x) = b(x)^* E_pi b(x)
```

have the exact **complex** first moment

```
sum_pi (z_pi(x)-d(x)) w_pi(x) = 0.
```

Where their sum is nonzero they give a positive permutation law. A
nonzero PSD success effect cannot vanish on every actual source because
the degree-two coordinates are independent. Its nonvanishing set is dense,
so continuity would cover the remaining sources for that fixed mixer.
Uniformity in all physical mixers is a further required step.

Conversely, a complex-source identity with constant Hermitian effects
polarizes in the holomorphic and antiholomorphic variables. Independence
of the antiholomorphic degree-two coordinates gives the matrix identity
in (1). For real `F,y`, conjugating the identity and averaging the effects
reduces Hermitian effects to real symmetric effects without losing PSD.
Thus this test includes every constant-effect quartic Born law on full91.

The source ring is the invariant ring of eight ordered points on the
projective line. The ideal generated by the fourteen partials of the
skew cubic is proved in [Howard–Millson–Snowden–Vakil,
arXiv:0809.1233](https://arxiv.org/abs/0809.1233).
The authors' [original computational supplement](https://math.stanford.edu/~vakil/files/hmsv1code/)
also gives the degree-three ideal rank 196 and quotient dimension 364.
The exact companion here constructs reductions of sizes 105-by91 and
560-by364 directly from the repository's rational source quadrics.

## A practical projection for the complete cone

The code uses orthonormal polynomial coordinates and the linear map

```
A(X) = sum_pi M_pi X_pi.
```

It allows nonsymmetric matrices in this linear subspace. Symmetry is
imposed by the separate PSD-cone projection. This makes

```
AA*(Y) = B Y,     B = sum_pi M_pi M_pi^T,
Pker(X)_pi = X_pi - M_pi^T B^+ A(X).
```

Only one 364-by364 pseudoinverse is needed. In contrast, explicitly
eliminating symmetry before projection would require a normal operator
on up to 33,124 cubic-by-quadratic coefficients.

Let `I` denote the 24-block identity and `p=Pker(I)`. Projection onto the
linear identity plus trace normalization is

```
Paff(X) = Pker(X) + (1 - <I,Pker(X)>) p / ||p||^2.
```

Douglas–Rachford alternates this affine projection and 24 eigenvalue
clippings. A second implementation minimizes the smooth dual objective

```
1/2 ||ProjPSD(C - A*Y - lambda I)||_F^2 + lambda,
```

after whitening the equality map. Neither implementation fits weights to
a finite list of spectral support costs: its residual is the entire
cubic-ring coefficient identity.

Files:

* `code/research/moc_unrestricted_fierz_full91.py`
* `code/research/moc_unrestricted_fierz_dual_lbfgs.py`
* `code/research/moc_unrestricted_fierz_dual_exact.py`

Generated operators, effects, logs, and audit reports are in
`build/moc_unrestricted_20261031/fierz/`.

A uniform-target calibration, replacing `d` by the average of the 24
products, recovers `E_pi=I/(24*91)` in one iteration: coefficient residual
`1.47e-17`, complex first-moment error `6.14e-17`. An independent actual
source audit checks the ideal equations and the multiplication diagram
to about `5e-15`. These checks verify the numerical operator; they do not
make the physical solve exact.

The 6,000-step physical Q59 runs have the following results. The moment
errors are measured only on a small diagnostic sample.

| Complete effects | Coefficient residual | Maximum diagnostic normalized complex-moment error |
|---|---:|---:|
| full91 | `1.174e-6` | `6.55e-6` |
| mixed77 | `3.131e-6` | `1.68e-5` |

Both remain unresolved. Slow convergence is not a no-go. Neither dual
has a strict separating PSD-shift margin. The independent smooth-dual
and Newton runs are recorded in their generated JSON files; no successful
law is asserted here.

## Exact obstructions to four nonlinear repairs

A separate experiment drops the fixed-effect restriction and enforces
the first moment through source-dependent real least squares. Put

```
D = [ 1 ; Re(z-d) ; Im(z-d) ],
w = diag(r) D^T (D diag(r) D^T)^(-1) (1,0,0)^T.              (2)
```

For positive prior `r`, (2) automatically has sum one and the exact
complex first moment whenever the three-by-three Gram matrix is
invertible. Positivity of the individual outcomes remains unproved.

At the exact physical mixer

```
O = (1/59) [ -25  46  16  22
             -46 -31  20  -2
             -16  20 -11 -52
              22   2  52 -17 ],
```

the following four choices all fail. Here
`L_pi=product_i (59 O_i,pi(i))` and `delta_pi=z_pi-d`.

| Prior | Negative-weight samples out of 400 | Exact fixture minimum, decimal |
|---|---:|---:|
| `r_pi=1` | 280 | -0.111606 |
| `r_pi=L_pi^2` | 226 | -0.053656 |
| `r_pi=1/abs(delta_pi)^2` | 288 | -0.067773 |
| `r_pi=L_pi^2/abs(delta_pi)^2` | 328 | -0.762428 |

The sample counts are exploratory. Each displayed failure is separately
replayed with exact Gaussian-integer spectra and rational weights; the
exact checks establish the obstruction to the proposed universal formula.
The phrase “physical prior” in the JSON names means the squared Leibniz
amplitude `L_pi^2`, not the full general class of positive instruments.

For the first row, take

```
a = (4-3i, 3-i, -2-3i, 3+3i),
b = (2+4i, 1+i, -2+i, -1-4i).
```

Outcome 11 in lexicographic zero-based permutation order has exactly

```
w_11 = -79531281766069 / 712606854207772 < 0.
```

The same fixture is constructively repaired by the positive law on
outcomes `(0,1,13)`:

```
(77169,733506,114976)/925651,
```

with the remaining 21 probabilities zero. Both its normalization and
its complex first moment are checked rationally. Each of the other three
formula failures also has an independently checked positive triangle law
in the saved report. These finite repairs demonstrate that the failures
are not MOC violations. They do not supply a uniform triangle choice or
a proof that such a triangle exists for every spectral source.

Reproduce with

```
python code/research/moc_unrestricted_fierz_nonlinear.py
```

The exact fixtures are in
`build/moc_unrestricted_20261031/fierz/nonlinear_minimum_variance_failures.json`.
The accompanying PNG/PDF shows the actual product polygon, determinant,
and negative weights of (2).

## Exact dual repair remains conditional

For rational degree-two and degree-three bases, a strict dual would have

```
Z_pi = sym(M_pi^T Y) + lambda G > 0,
lambda < 0, G > 0.
```

Pairing with (1) would give
`sum tr(Z_pi E_pi)=lambda tr(G sum E_pi)<0`, a contradiction. The exact
repair tool rounds a discovered multiplier in rational polynomial
coordinates, constructs all matrices using exact integer products, and
checks strict diagonal dominance after rational congruences. It refuses
to certify when the numerical dual lacks a strict PSD-shift margin.
No such strict full91 dual is obtained by the runs reported here.

The live proof problem remains the same: construct positive 24-outcome
effects or genuinely nonlinear weights, retain all fourteen source
coordinates, prove their exact complex first moment, and establish the
construction uniformly in the physical mixer.

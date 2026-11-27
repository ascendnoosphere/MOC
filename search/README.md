# Emergent-dimension counterexample search

This directory contains a dependency-free Node.js research engine for the
Marcus–de Oliveira conjecture. It searches one population of variable-size
spectral/unitary graphs. **There is no dimension input, dimension sweep, or
dimension-specific worker.** Dimension is the number of live spectral
labels in a graph, not a parameter that the user selects.

The program is a heuristic discovery engine with an exact arithmetic
separation verifier. A finite search that finds nothing does not prove MOC.

## Run

From the repository root, with Node.js 18 or later:

```sh
node search/emergent.js selftest
node search/emergent.js search --steps 100000 --workers 4 --seed 2026
node search/emergent.js verify moc-counterexample.json --work 2000000
```

The last command requires a certificate from a successful search. Each
worker maintains an independent population with variable order and a
different random seed. Workers stop when one produces an exact witness
or when all proposal budgets are exhausted. No worker is assigned an
order.

| Option | Default | Meaning |
| --- | ---: | --- |
| `--steps` | 1000 | Proposals per worker, including rejected proposals |
| `--workers` | 1 | Number of parallel populations |
| `--seed` | 1 | Pseudorandom seed |
| `--population` | 24 | Archive size per worker |
| `--samples` | 40 | Random matching permutations per new spectral pair, plus deterministic and locally optimized samples |
| `--work` | 80000 | Main floating subset-hull work limit per new spectral pair |
| `--exact-work` | 1000000 | Work limit for each exact support oracle |
| `--report-every` | 100 | Progress interval in proposals (0 disables) |
| `--out` | moc-counterexample.json | Destination of a certified witness |

The limits count operations in the support oracles, not CPU seconds.
They do not bound all matrix operations, BigInt arithmetic, or the
additional contact-proposal oracles. A rough cubic matrix-operation
guard derives its limit from `--work`; this is a resource guard,
not an independently chosen dimension cutoff. Raise the work and
population budgets for broader exploration. More workers also require
more memory.

The JSON progress records include the histogram of realized dimensions,
not a schedule of dimensions. `complete` counts candidates evaluated
against a full **floating-point** matching hull. `best.gap` is the
largest relative floating support gap among them. It is not a
certificate. `oracleWork` counts the main hull work, including capped
attempts, not all computational work.

## 1. Structural genome

A graph contains two complex spectral values for each live label and
an ordered list of two-coordinate unitary gates. A gate acts on rows
\(i,j\) using

\[
G_{ij}(q)=\begin{pmatrix}c&-\bar s\\s&c\end{pmatrix},
\qquad c=\frac{1-|q|^2}{1+|q|^2},\quad s=\frac{2q}{1+|q|^2}.
\]

The matrix \(U\) is the product of these gates in application order.
Every gate is unitary. Every finite unitary mixer has a two-row
factorization up to right diagonal phases, which commute with the
second diagonal spectrum.

A restart begins with no labels. Birth operations add labels and
incident gates. The only minimum is the proved MOC theorem in orders
0 through 3. A random continuation after that minimum produces an
unassigned initial order. Subsequent mutations insert or delete
labels, rewire or modify gates, or change spectral values. Mutations
can increase or decrease the order of the same lineage.

Disconnected graphs split into independent normal blocks. A strict
violation of a block-diagonal pair requires a violating block, so
disconnected proposals reduce to a randomly selected eligible component.
The search discards only components below the proved order threshold,
and the exact small-multiplicity/opposite-pair cases listed below.
The archive uses a mixture of gap fitness, continuous structural
novelty and random replacement. The novelty metric includes log label
count, gate density, mixing, nonnormality, and near-contact pressure.
It has no order-indexed buckets.

## 2. Support oracle: avoid factorial enumeration

For spectra \(a,b\), put \(z_{ij}=a_i+b_j\). Positive row scaling
changes the determinant and every matching product by the same positive
factor. The numerical search uses this scaling to reduce underflow.

Let \(H(S)\) be the planar convex hull of the products matching the last
\(|S|\) rows to the available column set \(S\). With zero-based row
indices,

\[
H(\varnothing)=\{1\},\qquad
H(S)=\operatorname{conv}\bigcup_{j\in S}
z_{n-|S|,j} H(S\setminus\{j\}).
\]

Multiplication by a complex scalar is real-linear. Therefore a point
that is not a vertex of a partial hull can be discarded without
changing the final hull. Memoization gives at most \(2^n\) subset
states instead of storing all \(n!\) matching products. Runtime
also depends on the number of generated hull vertices and sorting;
it is not an unconditional \(O(n2^n)\) time bound.

A fast inner hull of actual matching products is computed first.
Two-swap directional ascent improves these samples. A determinant
inside this inner hull cannot be outside the full hull (in exact
arithmetic). The numerical engine spends the full hull budget on
near-boundary candidates and on a random subset of other candidates.
The full spectral hull is cached across mixer mutations. A sampled-only
gap is optimistic and cannot be accepted as a witness.

If the determinant is outside the hull, its projection onto the
polygon gives a candidate separating direction. If it is inside,
the maximum outward support deficit gives its signed distance to
the boundary. Normalize the gap by the hull's maximum modulus.

## 3. Search operators tied to the proof library

- **Checked structural reductions:** exclude orders 0–3, spectral lists
  with at most two distinct values on either side, two lists each
  with at most three values, and the checked opposite-pair cases.
  Use exact equality, not a near-equality tolerance. Use block
  factorization to reduce disconnected gate graphs.
- **Projective charts:** opposite translation equalizes traces and
  common positive scaling fixes spectral energy. Occasional regular
  fractional-linear changes preserve inclusion. A damped complex
  Newton step attempts the equal-first/equal-second spectral
  coefficient chart; if it cannot find a regular pole it falls back.
  This is a numerical proposal, not a theorem-verification routine.
- **Rank-two orbit ascent:** for nonsingular \(M=A+B\), its inverse
  supplies an analytic maximizer of a fixed directional determinant
  on a two-row SU(2) orbit. No finite-difference gradient is needed.
  If \(d=a_j-a_i\), \(K=M^{-1}\), and \(t=|s|^2\), the determinant
  ratio after left multiplying the mixer by \(G\) is
  \(1+tT+\operatorname{Re}(cs)X+\operatorname{Im}(cs)Y\), where
  \(T=d(K_{ii}-K_{jj})-d^2\det K_{\{i,j\},\{i,j\}}\),
  \(X=d(K_{ij}+K_{ji})\), and
  \(Y=id(K_{ij}-K_{ji})\).
  The three real coordinates lie on a sphere. The support maximizer
  aligns them with the linear objective. Appending a gate also permits
  an incremental row/column update of the normal matrix.
- **One-free-entry minimax:** each matching product and the determinant
  are complex affine functions of one spectral entry. A trust-box
  max-min problem is solved by polygon clipping and bisection.
  The initial constraints come from sampled permutations and the
  active hull. A bounded cutting-plane loop adds newly violated
  contacts from the subset oracle.
- **Terminal-contact continuation:** the checked terminal reduction
  requires at least \(2n-1\) maximizing contacts. The engine
  linearizes projected contact equalities for the highest discovered
  matching products, and includes the first-order preservation of
  the complex determinant-minus-pivot difference. A regularized
  least-squares trust step changes both spectra. Approximate contact
  count and nonnormality are fitness signals, **not** hard exclusions
  or claims of exact terminality.
- **Open-family seeds:** near-opposite spectra, near-two-line spectra,
  nearly real spectra, clustered spectra, products of two Householder
  reflections, Fourier mixers, and real orthogonal mixers. Subsequent
  mutations can leave the seed family. No claimed proof of an open
  family is used as a pruning rule.

### Source map

| Repository result | Use |
| --- | --- |
| [Core](../Lean/MOC/Core.lean), [Support](../Lean/MOC/Support.lean) | Objective and strict directional witness |
| [Small](../Lean/MOC/Small.lean), [ExtendedCases](../Lean/MOC/ExtendedCases.lean), [TwoValues](../Lean/MOC/TwoValues.lean), [TwoSpectralCircles](../Lean/MOC/TwoSpectralCircles.lean), [OppositePair](../Lean/MOC/OppositePair.lean), [FourCoincidence](../Lean/MOC/FourCoincidence.lean) | Checked exact-case reductions |
| [ProjectiveTransport](../Lean/MOC/ProjectiveTransport.lean), [EqualSpectralCoefficients](../Lean/MOC/EqualSpectralCoefficients.lean) | Spectral normalization and chart changes |
| [FreeEntryEquivalence](../Lean/MOC/FreeEntryEquivalence.lean), [Free-entry proof map](../Docs/free-eigenvalue-and-exterior-shifts-proof-map.md) | Affine spectral optimization |
| [AffineGapCover](../Lean/MOC/AffineGapCover.lean), [GlobalContactSlice](../Lean/MOC/GlobalContactSlice.lean), [Contact map](../Docs/contact-transfer-proof-map.md) | Contact target and continuation proposals |
| [BalancedContactReduction](../Lean/MOC/BalancedContactReduction.lean), [NormalOrbit](../Lean/MOC/NormalOrbit.lean), [RankTwoPhaseEscape](../Lean/MOC/RankTwoPhaseEscape.lean) | Nonnormality merit and orbit optimization motivation |
| [FourMinorTransport](../Lean/MOC/FourMinorTransport.lean), [Open targets](../README.md#open-all-order-targets) | Real orthogonal and other seed families |
| [GaussianCayley](../Lean/MOC/GaussianCayley.lean) | Exact rational witness strategy |
| [DeterminantModulusBound](../Lean/MOC/DeterminantModulusBound.lean) | Motivation for modulus normalization and assignment disk bound |

The order-specific contact cones, matching-square certificates,
rectangular-frame reductions and other conditional routes in the
repository remain available for future specialized operators.
They are not silently treated as completed global theorems. This
implementation does not import Lean or modify its proof files.

## 4. Exact certificate

Only `CERTIFIED` denotes a counterexample. Floating-point candidates
are rounded at increasing precision to Gaussian integer spectra and
Gaussian rational two-row gates. QR compression reduces redundant
gates before rationalization. The exact verifier:

1. Constructs an integer matrix \(V\) and positive integer \(q\)
   such that \(U=V/q\). Checks \(VV^*=q^2I\) with BigInt arithmetic.
2. Computes the determinant of
   \(q^2\operatorname{diag}(a)+V\operatorname{diag}(b)V^*\)
   by fraction-free Gaussian-integer Bareiss elimination.
   Thus the determinant of the normal sum is \(D_N/q^{2n}\).
3. Computes the exact matching hull using the subset recurrence with
   Gaussian integer products and exact orientation tests. It checks
   the strict integer inequality
   \[
   \langle e,D_N\rangle >
   q^{2n}\max_\sigma\langle e,P_\sigma\rangle.
   \]
   The real dot product with integer pair \(e=(e_x,e_y)\) is the
   repository projection \(\operatorname{Re}((e_x-ie_y)z)\).
   The discovery engine can derive a separating integer normal from
   the exact polygon if the rounded direction is inadequate.
4. If the exact hull exceeds its budget, an exact branch-and-bound
   attempts the same strict inequality. For a partial product it
   bounds the remaining modulus using a scalar maximum-product
   assignment DP when affordable, or independent row maxima.
   The squared modulus bound permits strict integer comparisons
   without square roots. No branch is dropped on a floating tolerance.

The certificate stores integer spectra, rational gate parameters,
an integer direction, and a computed proof summary. Verification
recomputes the result from those inputs and does not trust the stored
summary. It does not require a floating-point search or a network
connection.

Verifier exit codes: 0 = `CERTIFIED`; 1 = `NOT_SEPARATED`
(the supplied direction is not strict); 2 = `INCONCLUSIVE` or input
error. A nonseparating direction is not a proof of full hull inclusion.

## 5. Validation and limits

The core self-test passed 996 assertions in a V8 JavaScript runtime.
It cross-checks exact hull support and disk bounds against direct
permutations through order six, verifies matching paths, compares
Bareiss with direct Leibniz determinants, tests analytic two-row ascent
against random gates, tests QR compression and incremental updates,
checks derivatives and rational unitarity, and runs a mixed-size
search. The CLI search and verify paths were also exercised with
mocked Node I/O; the actual Node worker-thread integration was not
run in that environment.

Two 5,000-proposal runs of this revision, using the default population
and main oracle budget and an exact budget of 300,000:

| Seed | Evaluated | Full numerical hull | Realized orders | Best relative numerical gap | Certified |
| --- | ---: | ---: | --- | ---: | --- |
| 2026 | 4712 | 4153 | 4–13, 16, 17 | -3.4311e-11 | 0 |
| 314159 | 4578 | 3922 | 4–13, 16 | -8.5704e-7 | 0 |

These are smoke/throughput measurements, not a coverage claim.
No exact certificate attempts were triggered by either run.
Near-zero gaps can result from commuting or other proved limits.
The method is stochastic and not exhaustive. Subset hull work and
exact integer sizes can still grow rapidly. Rounding can miss a very
small violation; exact verification may exhaust its budget; a fixed
finite run cannot exclude any general order. The verifier is an
arithmetic implementation, not a Lean kernel certificate.

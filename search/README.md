# Emergent-dimension counterexample search

This directory contains a dependency-free Node.js research engine for the
Marcus–de Oliveira conjecture. It searches shared populations of variable-size
spectral/unitary graphs, including compressed arbitrary-order cyclic graphs. **There is no dimension input, dimension sweep, or
dimension-specific worker.** Dimension is the number of live spectral
labels in a graph, not a parameter that the user selects.

The program is a heuristic discovery engine with an exact arithmetic
separation verifier. A finite search that finds nothing does not prove MOC.

## Run the persistent parallel engine

Use Node.js 18 or later. There are no third-party packages.

```sh
node search/parallel.js selftest
node search/native-smoke.js

node search/parallel.js search \
  --steps 1000000 --workers 8 --batch 250 \
  --population 48 --archive 256 \
  --cache-dir .moc-cache --run-id moc \
  --work 200000 --exact-work 1000000 \
  --cycle-share 0.5 --proof-work 20000 \
  --proof-every 2 --precision 256
```

The step target is cumulative **across all workers**, not per worker.
No worker has a dimension or an order range. The coordinator dispatches
batches dynamically and returns completed migrants to a shared archive.
A batch selects either the general dense gate-graph representation or the
unbounded compressed cyclic representation. This choice is not an order
selection.

To extend the same run after an interruption or after the previous target
is complete, use the same cache directory, run ID and seed with a larger
step target:

```sh
node search/parallel.js search --steps 2000000 --workers 8 \
  --cache-dir .moc-cache --run-id moc --seed 2026
```

The command restores the archive, totals, next batch ID and outstanding
jobs from the checkpoint. Ctrl-C requests a checkpointed stop after
in-flight jobs finish. After a hard crash, remove the stale
`coordinator.lock` only after confirming the old coordinator is no longer
running; the pending jobs will then be replayed. Different run IDs can
share one cache directory without sharing a checkpoint. Separate hosts
can use a shared filesystem if it provides atomic rename semantics;
their coordinators and archives remain independent.

```sh
node search/parallel.js inspect .moc-cache/runs/moc/checkpoint.json
node search/parallel.js verify moc-counterexample.json --exact-work 5000000
```

The last command requires a certificate from a successful search. It
independently recomputes the proof, without a discovery cache. The legacy
`search/emergent.js` CLI is also available for a standalone dense search.

| Parallel option | Default | Meaning |
| --- | ---: | --- |
| `--steps` | 100000 | Cumulative proposal target over all workers |
| `--workers` | up to 8 | Local worker threads, dynamically assigned batches |
| `--batch` | 250 | Proposals per scheduled batch |
| `--seed` | 2026 | Stable run seed; batch seeds derive from batch IDs |
| `--population` | 24 | Population size in each batch |
| `--archive` | 128 | Shared migrant capacity per representation |
| `--cycle-share` | 0.4 | Fraction of batches assigned to compressed cyclic graphs |
| `--samples` | 40 | Dense random matching samples |
| `--cycle-samples` | 12 | Compressed transportation matching samples |
| `--work` | 80000 | Main floating hull work limit; also determines dense allocation guard |
| `--exact-work` | 1000000 | Work limit for dense exact or independent final verification |
| `--proof-work` | 3000 | Transportation-tree visits per compressed proof attempt |
| `--proof-every` | 8 | Eligible compressed proof attempt interval within a batch |
| `--precision` | 192 | Dyadic interval mantissa bits for compressed verification |
| `--cache-dir` | .moc-cache | Persistent content-addressed object and checkpoint directory |
| `--run-id` | default | Independent resumable archive/checkpoint name |
| `--memory-mb` | 32 | Approximate worker-local cache memory target |
| `--cache-max-mb` | 4096 | Approximate shared disk cache write limit, not a strict quota |
| `--out` | moc-counterexample.json | Certified witness file |

Work limits count algorithmic work, not CPU time. Dense allocation still
has a resource guard. The compressed representation has no numerical
dimension cap; the run counts, dimension, transportation capacities,
and scaled arithmetic exponents are BigInts. Its actual runtime depends
on the number of runs, the bit length of counts, distinct spectral
values, precision and proof complexity. Raise budgets when necessary.

### Shared caching and upward reuse

The coordinator exchanges elite and diverse candidates after every batch.
Each worker has a bounded local LRU cache and all workers can read the
same persistent content-addressed store. Cache entries have checksums;
writes are published atomically and incomplete/corrupt entries are not
used. Cache objects are immutable computations, not proof premises.

The cache contains:

- completed numerical candidate evaluations and determinants;
- dense partial convex hulls keyed by their actual remaining factor
  matrix, with local matching labels (not by matrix dimension);
- repeated cyclic transfer-matrix and complex scalar powers;
- budget-specific compressed proof-attempt results.

Dense label births prepend a new label and keep the old spectral
entries where possible. Row scaling depends only on the corresponding
first-spectrum value, so an unchanged suffix retains its factor-matrix
cache key after a birth. Local edits avoid global normalization unless
values drift outside the working scale. A mixer-only mutation also reuses
its parent's spectral hull and incrementally updates the sum matrix.

Cyclic run growth reuses binary powers of the same local transfer
matrix. For example, changing a run count from \(m\) to \(2m\)
requires only the new combinations of cached powers, not a new
dimension-sized calculation. Completed partial states remain reusable
even if their original search exhausted its work budget.

Small objects stay in local memory until reused; expensive objects are
batched to disk. The disk limit is a soft write limit and can overshoot
with concurrent writers. It does not automatically evict old files.
The checkpoint directory is separate from cached computation objects.

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
unassigned initial order in the dense representation. Subsequent mutations insert or delete
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

## 5. Arbitrary-order compressed search and rigorous verification

The dense representation is general but cannot allocate an arbitrary
large matrix. The second representation searches a structured open
family related to [two-layer cyclic gate laws](../Lean/MOC/TwoBiasedCyclicGateLaw.lean)
and [cyclic antipodal spectral cases](../Lean/MOC/CyclicAntipodalSpectra.lean).
It does not treat either restricted result as a proof for arbitrary
cyclic data.

A run stores a pair of first-spectrum values, a pair of second-spectrum
values, two rational two-coordinate gate parameters, and an arbitrary
positive integer multiplicity. The first mixer layer joins the two
coordinates in each cell. The second layer joins one cell to its
neighbor, including the closing edge of the ring. Mutations grow,
shrink, split and alter runs. A nontrivial extra coordinate in a
three-coordinate boundary block is also allowed.

\[
n=2\sum_{j=1}^r m_j+\varepsilon,\qquad
\varepsilon\in\{0,1\}.
\]

Thus both parities are unbounded. These structures are not made large by
appending independent scalar blocks. Repeated run types can still have
additional reducing symmetries; no irreducibility claim is made.

Conjugate the sum by the second layer. The even-order result is cyclic
tridiagonal, since the two normal summands are now made of alternating
two-coordinate blocks. For diagonal entries \(d_i\) and directed edge
entries \(u_i,v_i\), put \(w_i=u_iv_i\). With cyclic indexing,

\[
T_i=\begin{pmatrix}d_i&-w_{i-1}\\1&0\end{pmatrix},
\qquad
D=\operatorname{tr}(T_{n-1}\cdots T_0)
-\prod_i u_i-\prod_i v_i.
\]

The trace enumerates the monomer/dimer terms. The two oriented full
cycles have sign minus in even order. An odd-order defect adds a
triangle at the closing edge. The determinant then has the core-ring
terms, tail monomer/dimer terms, the two triangle orientations, and
the two enlarged-cycle orientations. The implementation expands these
terms using path transfer products, without division by the tail
diagonal entry.

Within a homogeneous run, the same two-node transfer matrix repeats.
Binary exponentiation gives an operation count logarithmic in each run
multiplicity. Explicit boundaries are processed separately. A fixed
number of runs does not require dimension-sized storage. Complex
mantissas have arbitrary integer binary exponents, so determinant
magnitude does not overflow solely because the dimension is large.

### Matching without listing labels

Group equal values in the two spectra. A matching is represented by a
nonnegative integer transportation table \(x_{ij}\) with the prescribed
row and column multiplicities. Its matching product is

\[
P(x)=\prod_{i,j}(a_i+b_j)^{x_{ij}}.
\]

Every labelled permutation induces a feasible table and every feasible
table lifts to a labelled permutation. Greedy feasible transportation
samples provide optimistic inner-hull search scores. These scores can
be very inaccurate: sampling can miss large products, and floating
arithmetic can lose phase accuracy over huge powers. They are never
certificates. The compressed search does not interpret a negative,
zero or positive sampled gap as a rigorous hull decision.

The compressed exact verifier avoids dense expansion. It uses dyadic
complex balls \((r,i,\rho,e)\) with BigInt centers, nonnegative outward
error radii, and arbitrary integer exponents:

\[
|\operatorname{Re}(z2^{-e})-r|
+|\operatorname{Im}(z2^{-e})-i|\le\rho.
\]

Rational gate coefficients are enclosed by directed integer rounding.
Addition aligns exponents with outward rounding; multiplication
propagates the L1 error bound. Binary matrix powers enclose the exact
determinant. The grouped support verifier branches on integer count
intervals, not individual labels. It uses squared-modulus upper bounds
to prune entire intervals. For positive determinant lower projection,
an interval can be eliminated when its upper squared modulus, multiplied
by the squared norm of the direction, is strictly below the square of
the determinant's lower projection.

At a completed transportation table, compare the upper matching
projection with the lower determinant projection. Only when **all**
feasible tables are strictly separated (by certified bounds or leaf
comparisons) can the verifier return `CERTIFIED`. If a matching lower
projection is at least the determinant upper projection, it returns
`NOT_SEPARATED` for that direction. Budget exhaustion or overlapping
intervals return `INCONCLUSIVE`.

A compressed certificate has format `moc-cycle-interval-v1` and includes
the genome, integer direction and precision. The coordinator
independently reverifies it before publishing the certificate.
Unlike an exact dense determinant, it need not store integer numerators
with bit length proportional to the dimension. The worst-case
transportation search can still be prohibitively large. Neither
logarithmic determinant evaluation nor large-order representation
implies logarithmic complete separation or arbitrary dense search.

## 6. Validation and limits

The following were executed in a V8 JavaScript runtime:

| Test | Result |
| --- | --- |
| Dense mathematical core | 998 assertions passed, including reuse of a partial hull across dimensions |
| Compressed cyclic determinant | 58 assertions passed; 50 dense comparisons with maximum relative error about \(1.39\cdot10^{-14}\) |
| Rigorous interval verifier | 31 assertions passed, including enclosure of exact rational determinants in even and odd orders |
| Dimension 1,000,000,000 | Compressed determinant evaluated; one proposed direction rigorously rejected after 67 transportation-tree visits |
| Dimension 1,000,000,001 | Compressed determinant evaluated; one proposed direction rigorously rejected after 88 visits |
| Compressed representation | Evaluated a test fixture of dimension 2,000,000,000,000,000,000,000,000,000,003 |
| Coordinator/cache simulation | Three-worker scheduling, 100-to-160 proposal resume, 1,363 persistent-cache hits, corruption rejection, and recovery of 60 pending proposals |

A final 180-proposal compressed-only run (seed 41, work 2,000, exact
work 3,000, proof work 200, proof interval 2, precision 192) evaluated
180 candidates. It reached dimension 7,685,131,763,883,640,887,311,251,538,516.
Eight compressed verification attempts rejected their proposed
directions; no counterexample was certified. Large unresolved
candidates remain unresolved: these statistics do not prove inclusion
in those dimensions.

The coordinator simulation used the real search kernels and mocked
worker events and filesystem operations. Native Node worker threads and
filesystem concurrency were not executed in this development
environment. Run `node search/native-smoke.js` on the target machine
to test actual parallel dispatch, persistence and resume.

The implementation is stochastic, not exhaustive, and its speedup
has not been benchmarked against an optimized native implementation.
Exact interval verification can fail to resolve a sign; increase
precision and work budgets where justified. A billion-dimensional
compressed cycle is not equivalent to searching a billion-dimensional
general dense unitary. The arithmetic verifier is not a Lean kernel
certificate. No unrestricted conjecture or open family has been proved.

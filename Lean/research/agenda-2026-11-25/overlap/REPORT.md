# Two-frame overlap, unequal-color support and mixed pencils

The analytic proofs and diagnostics are separate. The diagnostics support no general implication.

| Agenda | Result | Exact remaining requirement |
|---|---|---|
| Cycle 02, path 06: three-edge coefficient law | Reproduced the four-term separating inequality: all 24 injections have nonnegative score and the real isometric frame has score −47/1681. The case split in the agenda is the proof of nonnegativity. | The negative direction acts on the entire coefficient vector; it is not a factorized reciprocal spectral objective. It cannot separate a scalar determinant without an additional argument. |
| Cycle 02, path 06: scalar finite-label reduction | Lean theorem `exists_sparse_frame_same_compression` preserves the compression and the isometry while retaining at most $3k^2$ original labels. `exists_sparse_scalar_frame_counterexample` gives the same determinant for a restricted reciprocal frame, with at most 27 labels per side at $k=3$. Restriction can remove, but cannot add, the optional zero vertex. `scalar_frame_law_of_bounded_orders` proves the scalar law of overlap $k$ from MOC through order $6k^2-k$ (51 when $k=3$). | Prove scalar containment for the remaining bounded-size **continuous** family. This is not a finite search over discrete spectra. The argument does not bound the overlap of arbitrary MOC witnesses. |
| Cycle 02, path 10: Hall slack | Rook coefficients reproduce all unordered shared-color rectangle patterns through $n=10$ with Hall condition, balanced-tight equality, and eligible minima. The analytical Hall proof uses only that a row set with two colors has every column as a neighbor. Under strict Hall, every allowed edge extends. Inducting by the degree of a highest-degree vertex proves the stated factorial bound; no enumeration is needed for the proof. | Counts are not linear inequalities on complex projections of matching values. The strict-witness support implication needs the rank-excess theorem separately. Prescribed slack is not automatically closed under limits. General count/equality proofs are not Lean-verified in this pass. |
| Cycle 01 and 02, path 14: pointwise vs simultaneous | 12 trace-zero coefficient vertices suffice, instead of 48 phased Pauli vertices. See the exact construction below and `MixedPencilObstruction.lean`. | No claim these vertices are realized by common additive matching spectra. A same-spectra example or determinant-specific promotion theorem remains open. |
| Cycle 01, path 14: genuine-coefficient diagnostic | Using the exact frame fixture, a numerical LP screened 64 small Gaussian-integer frozen spectra for each of 21 free-label pairs. There were no hits. The sample permits zero frozen labels, repeated labels, leading cancellation and non-Hermitian compressions. | The test has only one real 4-by-3 frame. It cannot establish simultaneous containment, nor eliminate complex frames or larger overlaps. |
| Cycle 01, path 06: terminal-contact rank | The frame compression retains a determinant and restricts its matching vertices. It does not preserve terminal-contact rank or moment constraints. | Need an exact pseudo-witness or certificate under simultaneous terminal rank, moments, normalization and global mixer maximality; no such complete system solved in this branch. |
| Cycle 01, path 10: spinor balance | Parallel/rank-one kernels give exactly the same product on every permutation: the determinant factors into row and column scalars. Balanced non-tight unit frames exist: identical row and column lists consisting of copies of ((1,0),(0,1)) in unequal counts have equal gauges but unequal eigenvalues of the frame operators. Equal-count antipodal axes instead give scalar frame operators. Neither case gives a general local-to-global bridge. | Gauge balance alone is not a tight-frame or commuting condition. Higher-order dense active-contact stationarity at $n=4,5,6$ was not certified here. |

## The 12-vertex obstruction

Write coefficient vectors in order `(1,t,u,tu)`. Take the target
$1+tu$ and the twelve polynomials $3(\pm1\pm i)q$ with $q$ one of
$1-tu,t,u$. Every vertex has constant coefficient plus mixed coefficient
zero. The target does not, so it lies outside the simultaneous coefficient
hull.

Multiply evaluations by any complex direction $w$. Set
$m=\max(|w(1-tu)|,|wt|,|wu|)$. The identity
$(w(1+tu))^2=(w(1-tu))^2+4(wt)(wu)$ gives $|w(1+tu)|^2\le 5m^2$.
For a maximizing $q$, the best sign pair gives real part
$|\Re(wq)|+|\Im(wq)|\ge m$. The directional support over the scaled
vertices is therefore at least $3m$, which bounds the target. Separation
gives pointwise membership for all complex $t,u$, including vanishing
evaluations. The argument uses no numerical tests.

## References and scope

- D'Ariano, Lo Presti and Perinotti, *Classical randomness in quantum
  measurements*, [DOI 10.1088/0305-4470/38/26/010](https://doi.org/10.1088/0305-4470/38/26/010),
  [preprint](https://arxiv.org/abs/quant-ph/0408115). Rank-one effects and
  independence in the real space of Hermitian matrices. The triple-moment
  compression lemma is independent of their extremality theorem.
- Haapasalo, Heinosaari and Pellonpää, *Quantum measurements on finite
  dimensional systems: relabeling and mixing*,
  [DOI 10.1007/s11128-011-0330-2](https://doi.org/10.1007/s11128-011-0330-2),
  [preprint](https://arxiv.org/abs/1104.4886). Mixing and relabeling extremal
  rank-one measurements do not imply a common law for all determinant
  coefficients.
- Kaplansky and Riordan, *The problem of the rooks and its applications*,
  [DOI 10.1215/S0012-7094-46-01324-5](https://doi.org/10.1215/S0012-7094-46-01324-5).
  The inclusion-exclusion diagnostic is the rook-polynomial method, not
  the induction proof of the all-order lower bound.

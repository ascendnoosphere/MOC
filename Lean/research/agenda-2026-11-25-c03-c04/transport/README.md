# Transport, variance, and exact Cayley replay

The pure Python replay constructs Gaussian rational Cayley matrices
and checks the certificates using exact arithmetic. Numerical linear
programs are separate and are not treated as certificates.

From this directory, pass
`--baseline ../../agenda-2026-11-25/transport/experiments.py` to either
script. The flags `--skip-variance` and `--skip-scalar` limit the exact
replay to one of its two tracks.

- `variance_cayley_replay.py`: 384 exact near-commuting rank-one variance
  fixtures in orders 4–6, eight checked independently using the signed
  Leibniz law. There were 236 strict actual-versus-relaxed lower-gap
  separations and 272 strict relaxed-versus-lattice upgrades. No
  adjacent-gap violation in this sample. The Cycle 03 arbitrary-cost
  obstruction and the Cycle 04 conditional/cubic obstructions are
  separately rechecked.
- The same script covers 72 exact scalar cases and 983 support directions
  (axes and every polygon edge); 757 directions tied multiple labels.
  The cases include zero cross sums, repeated labels, near antipodal
  and near-zero spectra, and near commuting mixers. No strict excess.
- `flag_variance_lp.py`: 72 near-commuting all-prefix LPs passed at
  tolerance 1e−8, with worst outward normalized residual 7.3e−17.
  This is numerical, not an exact LP replay.

[ThresholdVariance.lean](../../../MOC/ThresholdVariance.lean) proves the
integer-lattice variance bound for a genuine law and its independent
threshold consequence, conditional on the specified marginal edge
decomposition. [SignedPairMoments.lean](../../../MOC/SignedPairMoments.lean)
proves the exact physical signed singleton and second assignment
moments. [RankOneLattice.lean](../../../MOC/RankOneLattice.lean) supplies the actual
projection-minor marginals for nested integral thresholds and proves
the rank-one lattice bound for every unitary. This is not a positive
joint threshold law or the actual adjacent-score gap bound.

One exact strict relaxation gap is a single real plane rotation in order
four: `x=(1,7,-7,2)`, `y=(19,5,4,-6)`, and sine squared `9/25`.
The mean is 23, the actual variance is 144, and the adjacent true
scores are 14 and 25. The true support lower bound is therefore 18.
The independent relaxed support contains 23 and gives only 0. This
explains a concrete loss in that relaxation without exhibiting a
violation of the actual adjacent-score bound.

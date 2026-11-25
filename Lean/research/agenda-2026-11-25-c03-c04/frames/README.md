# Frame, pencil, and radial replay

Run `python -B frame_pencil_radial_replay.py` with SymPy. It outputs the
record stored in `frame_pencil_radial_replay.json`. Recorded display gaps
are floats only for readability; the assertions about the compressed
matrices, pencil coefficients, and radial inequalities use exact arithmetic.

The three joint frame fixtures include overlap three with a dense
complex frame, overlap four, and a tight frame with one side already
square. The checks track whether optional zero was available before and
after compression. They supplement the [symbolic joint theorem](../../../MOC/FiniteFrameLabels.lean)
and do not prove that compression itself implies the scalar bound.

For the grouped pencil, the supplied conditional centroid is 76/3,
greater than the indicated ordinary upper value 25. The separately
reconstructed affine slope/intercept and alternative feasible tuple are
checked without treating the raw conditional centroid as a probability.
[Two-pivot elimination](../../../MOC/GroupedMomentElimination.lean) is
formal; universal feasibility remains open.

Six radial comparisons include repeated colors and zero-bearing
kernels. Radial control is not control of an arbitrary angled support
line. The [unit-modulus chart result](../../../MOC/UnitModulusRankTwo.lean)
is independent of these radial fixtures.

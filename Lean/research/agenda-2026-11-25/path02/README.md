# Fixed-mass grouped pencil diagnostic

Run `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python stress_fixed_mass.py`
with NumPy 2.3.5 and SciPy 1.17.0. Includes 15 seeded samples at each
(order, family) pair, with seed 20261125. The system uses one variable per
matching product, fixes the total mass at each matched row to the
squared unitary entry, and asks for equality in all four real coefficient
coordinates. Every one of the 270 trials met the reported feasibility
criterion; maximum normalized residual was approximately 5.5e−10.
The near-cancelling directional probes are additional numerical tests,
not a substitute for unrestricted support directions. Data: [result.json](result.json).

The [Lean theorem](../../../MOC/FixedMassGroupedSupport.lean) is an exact
symbolic equivalence and does not assume any result of this script.

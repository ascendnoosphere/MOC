# Real spectral jets and polynomial pencils

For a real rotation or reflection \(R\) and two ordered real spectral lists \(x,c\), use the difference convention. Each permutation gives the polynomial \(z_\pi=\prod_i(x_i-c_{\pi(i)})\). A signed law obtained by dividing the signed Leibniz terms of \(R\) by its determinant reproduces the matrix determinant as a polynomial. This makes it possible to test candidate positive laws by linear programming without inverting the matrix sum at a singular point.

I tested three choices of coefficients for which to seek common weights:

1. The product at real spectra and its five real partial derivatives in \(x_4,c_1,\ldots,c_4\), with the other three entries of \(x\) held fixed.
2. All five coefficients of \(\prod_i[s(x_i-c_{\pi(i)})+t(y_i-d_{\pi(i)})]\). A common positive law gives the inclusion after every complex specialization of \(s,t\).
3. The preceding pencil with a common translation added to every factor, equivalently all coefficients of \(\prod_i[1+s(x_i-c_{\pi(i)})+t(y_i-d_{\pi(i)})]\).

For each family the LP maximizes the smallest of the 24 weights reproducing the selected coefficients and sum one. The experiment used 1,600 inputs with seed 3910, cycling between the regular rational rotation in [the pencil proof](Regular.md), a normalized real Hadamard matrix and a real orthogonal matrix obtained by Gaussian QR. All eight real center coordinates were distinct integers. Each input was tested on all three LPs.

| Coefficients | Negative floor | Within tolerance of zero | Positive floor |
| --- | ---: | ---: | ---: |
| First jet | 0 | 0 | 1,600 |
| Binary quartic | 0 | 1 | 1,599 |
| Translated pencil | 442 | 478 | 680 |

The tolerance is \(10^{-8}\). The counts came from floating-point QR and HiGHS. In particular the negative outcomes concern a common coefficient law for a stronger family and give no scalar counterexample. The first-jet and binary-quartic results leave universal feasibility unresolved. Run `python3 -B Code/probe_spectral_jets.py` with NumPy and SciPy to reproduce the experiment. [Experiment code](../../Code/probe_spectral_jets.py)

## A sufficient local condition at a real center

Here is a way to use a strictly positive first-jet solution. Fix the first three first-spectrum entries at distinct real values using a common fractional linear map on the signed lists, away from its poles. Near a real center the map can be chosen continuously and it only multiplies the determinant and all vertices by a common factor. Write the five remaining complex coordinates as \(x+iy\). For each vertex polynomial \(f\), and for the determinant polynomial with the mixer fixed, use the six real coordinates
\[
 \left(\Re f(x+iy),\quad
     \int_0^1 \Re\,\partial_j f(x+isy)\,ds\quad (1\le j\le5)\right).
\]
All polynomial coefficients are real for a fixed unitary mixer by the squared-minor expansion. The dot product of \(y\) with the last five coordinates gives \(\Im f(x+iy)\) by differentiating along the segment. Hence any law matching all six coordinates proves scalar MOC at that input. At \(y=0\) these are the real product and first jet tested above.

If the 24 real six-vectors affinely span \(\mathbb R^6\) and the target at the center is a convex combination with all weights strictly positive, the inclusion holds on a full neighborhood of that center and mixer. To see this, choose seven independent augmented columns (adjoin a constant one). Keep the other weights fixed and solve the remaining seven equations. Invertibility and strict positivity persist by continuity. The same proof applies to complex unitary perturbations of the mixer. The sampled floors above are numerical. This criterion still requires a proof of the hypotheses at any center where it is invoked and gives only a local conclusion there.

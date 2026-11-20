# Two quaternionic families in order four

Write \(z_\pi=\prod_{i=1}^4(a_i+b_{\pi(i)})\) and let \(H\) be the convex hull of these 24 points. In the ordered quaternion basis use the matrix

\[
 L(t,x,y,z)=
 \begin{pmatrix}
 t&-x&-y&-z\\ x&t&-z&y\\y&z&t&-x\\z&-y&x&t
 \end{pmatrix}.
\]
Its transpose times itself is \((t^2+x^2+y^2+z^2)I\). The normalized matrix represents left multiplication by a unit quaternion and has determinant one by continuity on the unit sphere.

## Arbitrary spectra on an entire one-parameter family

**Theorem.** For every real \(r\), \(U=L(r,1,1,1)/\sqrt{r^2+3}\) satisfies order-four MOC for arbitrary complex spectra. The same holds for its independent monomial row and column translates after relabeling the spectra.

The earlier [isoclinic support calculation](../theorems/finite_and_spin_geometry/dual_isoclinic_support_geometry.md) proves a common permutation law for \(r=0\) or \(|r|\ge\rho\), where \(\rho^3+3\rho-2=0\), \(0<\rho<3/5\). For \(0<r<\rho\) at least one facet of the common-minor hull fails. We give a scalar certificate for that interval. Transposition and interchange of the two spectra handle negative parameters since \(U(-r)=-U(r)^T\).

Permute columns to \((4,2,3,1)\). Use the ordered permutation profiles
\[
1324,1342,1423,1432,2143,2314,2341,2413,3124,3142,3214,3412,4123,4231.
\]
Their signed weights, multiplied by \((r^2+3)^2\), are respectively
\[
 A,B,B,C,B,B,C,A,B,A,C,B,C,h
\]
where \(A=1+2r-r^2,\ B=(1-r)^2,\ C=2r,\ h=r(r^3+3r-2)\).
These are *unnormalized coefficients*, so assertions about their signs and the following linear inequalities are unaffected by the positive common divisor. The verifier checks all 53 subset coordinates of sizes 0, 1 and 2 by polynomial expansion, including the total mass. Complementary minors give sizes 3 and 4.

For \(0<r<\rho\) the first thirteen weights are positive and \(h<0\). A strictly separating real affine cost would have nonnegative costs on all permutation vertices. Its anchor cost at \(4231\) would have to be positive. Scale it to 2. Write the other thirteen costs as \(u_i\ge0\), and their unnormalized positive weights as \(w_i\). Then \(\sum_i w_i u_i<-2h\). If \(R_iw_i+2h\ge0\) for positive radii \(R_i\), necessarily \(\sum_i u_i/R_i<1\).

Use the following radii according to the class of the positive weight. The last column counts zeros among the 497,420 degree-nine Bernstein coefficients.

| Interval checked | Radius for A | Radius for B | Radius for C | Zero coefficients |
|---|---:|---:|---:|---:|
| \([0,1/5]\) | 1/2 | 1 | 2 | 34,194 |
| \([1/5,3/5]\) | 1/2 | 2 | 3/2 | 0 |

For each row the inequalities \(R_i w_i+2h\ge0\) hold on the entire indicated interval. The verifier proves this by exact univariate root counts after scaling to \([0,1]\). It reconstructs the polynomial of actual spectral costs from the [spin certificate](../spin/PROOF.md), and checks all Bernstein coefficients on the simplex with vertices \((0,2)\) and \((R_i e_i,2)\). Both rows have zero negative coefficients and a strictly positive coefficient at \((0,2)\). Thus the polynomial is strictly positive whenever the anchor's barycentric coefficient \(1-\sum_i u_i/R_i\) is positive. Every actual separating cost must instead be a zero of this polynomial, by sections 2 and 3 of the spin proof. This contradiction proves the theorem. The use of that polynomial is independent of whether a particular unitary is a cubic symmetric power.

## Arbitrary quaternion coordinates for matching cross-ratios

**Theorem.** Let \(U=L(t,x,y,z)\) for real unit quaternion coordinates. For a list \(s\) define \(E(s)=(s_1-s_2)(s_3-s_4)\) and \(F(s)=(s_1-s_3)(s_2-s_4)\). If
\[
 E(a)F(b)=F(a)E(b),
\]
then \(\det(D_a+UD_bU^*)\in H\). For distinct entries this is equality of ordered cross-ratios. The polynomial hypothesis includes collisions without division. The conclusion also holds without a spectral hypothesis when any quaternion coordinate vanishes.

Indeed, multiplying the matrix in the determinant on the right by \(U\) gives \(((a_i+b_j)U_{ij})_{ij}\). The Leibniz coefficients of \(z_\pi\) are \(\mathrm{sgn}(\pi)\prod_i U_{i,\pi(i)}\). The sixteen permutations other than three-cycles have nonnegative coefficients, each a fourth power or a product of squares. Their sum is \((t^2+x^2+y^2+z^2)^2=1\). The eight remaining terms sum to
\[
 2txyz\,[E(a)F(b)-F(a)E(b)].
\]
The accompanying verifier expands this identity symbolically for independent spectral variables. Under either hypothesis the sixteen nonnegative terms therefore give the required convex combination.

## Reproduction and scope

Run `python3 -B Code/verify_quaternion_cases.py` from the repository root, with assertions enabled, SymPy, a C++17 compiler, OpenMP and GMP. Grid generation and exact integer interpolation reuse the existing spin verifier.

The equal-three-coordinate theorem allows independent, arbitrary spectra. The general quaternion theorem requires its displayed spectral identity or a zero coordinate. Neither proof establishes scalar MOC for unrestricted real orthogonal mixers or unrestricted order-four normal pairs.

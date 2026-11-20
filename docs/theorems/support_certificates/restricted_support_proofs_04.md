## Investigation 027: five complete complex spectral families

### Accepted statement

For

\[
a=(0,\tfrac12,1,z),\qquad z\in\mathbb C,
\]

complex MOC holds for every \(U\in U(4)\) for each of the following
second spectra:

| Second spectrum | Complete exact coefficient-hull facets |
|---|---:|
| \((-1,i,1,2+i)\) | 35 |
| \((-1,2,1+i,-1+2i)\) | 33 |
| \((-1+i,-2i,2i,2-i)\) | 77 |
| \((1+i,2-i,-1+2i,-2-3i)\) | 81 |
| \((-2-i,-1+i,2+2i,3-i)\) | 80 |

The total is 306 facets. This statement covers every complex value of
the fourth eigenvalue, every support direction, and every unitary. It
does not cover arbitrary second spectra.

### Why a coefficient-hull certificate proves the infinite family

For each permutation, write

\[
\prod_i(a_i+b_{\pi(i)})=Q_\pi+zP_\pi,
\quad
P_\pi=\prod_{i=1}^3(a_i+b_{\pi(i)}),
\quad Q_\pi=b_{\pi(4)}P_\pi.
\]

Both the actual determinant and the 24 comparison values are affine
holomorphic functions of \(z\). Their coefficient pairs lie in
\(\mathbb C^2\cong\mathbb R^4\). A coefficient-hull facet normal
therefore represents a real common-minor cost.

There is a direct elementary way to verify the extension from permutation
values to every complex unitary. The matching product has the expansion

\[
z_\pi=\sum_{|I|=|J|}a_{I^c}b_J\,
1_{\{\pi(I)=J\}}.
\tag{1}
\]

For a unitary \(U\), define the linear Leibniz functional

\[
\Lambda_U(f)=\frac1{\det U}
\sum_\pi\operatorname{sgn}(\pi)
\prod_i U_{i,\pi(i)}\,f_\pi.
\]

Laplace expansion and Jacobi's complementary-minor identity give

\[
\Lambda_U\bigl(1_{\{\pi(I)=J\}}\bigr)
=|\det U[I,J]|^2.
\tag{2}
\]

In particular, \(\Lambda_U\) is real-valued on the real common-minor
span. Equation (1) shows explicitly that both real and imaginary parts
of each product coefficient belong to that span. Consequently applying
\(\Lambda_U\) commutes with taking real parts on the cost functions
used here, even though its individual Leibniz weights can be complex.

Every facet deficit has an exact representation as a nonnegative rational
combination of the 130 known valid generators. Applying \(\Lambda_U\)
therefore proves that facet inequality for the determinant coefficient
pair at every unitary. The complete collection of facets places that
pair inside the coefficient hull. Every complex linear evaluation
\((Q,P)\mapsto\operatorname{Re}(\eta(Q+zP))\) is then bounded by its
permutation maximum. This proves the stated family theorem.

No assertion that arbitrary unitary Leibniz weights are probabilities is
needed or used.

### Independent exact verification

The reviewer reconstructs all 24 Gaussian-rational coefficient points
from the spectral data. It verifies their affine rank four and enumerates
all \(\binom{24}{4}=10626\) candidate supports for each family by the
five-dimensional homogeneous cone method. This differs from the author's
three-by-three affine cofactor construction. The two methods give exactly
the same complete facet sets.

The 130 generators are independently regenerated, including both complete
48-ray orbits. For every facet, every decomposition coefficient is
nonnegative and every one of the 24 reconstructed values equals the
original exact facet gap. There are respectively 241, 213, 724, 747, and
738 nonzero rational coefficients across the five facet lists.

The theorem consequently rests on complete exact polyhedral certificates,
not a numerical absence of counterexamples.

## Investigation 028: a direct optimized-energy proof on every real plane

### Accepted statement

For the actual complex support instance in
`polyhedral_enlarged_counter_exact.json`, with the direction scaled by
512 so that \(h=24\), the optimized energy bound

\[
g\ge\frac14\ell^T\mathcal A^+\ell
\tag{3}
\]

holds on every real rank-two plane. It therefore proves the support bound
on every complex \(U(2)\) action carried by any such plane. Diagonal
phase conjugation extends the conclusion to gauge-real planes. The
identity pairing is a maximizing base in this instance.

This is one fixed complex support direction. The proof does not cover
every genuinely complex plane or every spectral direction.

### Independent geometric and polynomial reconstruction

Let \(p_{ij}\) be the six real Plücker coordinates of a plane, with

\[
p_{12}p_{34}-p_{13}p_{24}+p_{14}p_{23}=0,
\qquad q=\sum_{i<j}p_{ij}^2.
\]

Set \(P_{ij}=\sum_kp_{ik}p_{jk}\). The reviewer independently verifies

\[
P^2=qP
\]

modulo the Plücker relation. Since \(\operatorname{tr}P=2q\), for
\(q=1\) this is precisely the real rank-two orthogonal projection.

The actual products give edge gaps

\[
(\delta_{12},\delta_{13},\delta_{14},\delta_{23},\delta_{24},\delta_{34})
=(39,40,0,9,12,40)
\]

and oriented triple differences \((80,45,72,53)\). Define

\[
\begin{aligned}
B={}&39p_{12}^2+40p_{13}^2+9p_{23}^2+12p_{24}^2+40p_{34}^2,\\
S={}&80p_{12}p_{13}p_{23}+45p_{12}p_{14}p_{24}
+72p_{13}p_{14}p_{34}+53p_{23}p_{24}p_{34},\\
Q={}&44(p_{12}p_{34})^2-10(p_{13}p_{24})^2
-115p_{12}p_{34}p_{13}p_{24},\\
G={}&4\sum_{i<j}\delta_{ij}P_{ij}^2-16Q.
\end{aligned}
\tag{4}
\]

To check the reflection formula without trusting the author's builder,
the reviewer constructs \(R_q=qI-2P\) and verifies both degree-eight
polynomial identities

\[
\det R_q=q^4,
\]

\[
hq^4-\sum_\pi\operatorname{sgn}(\pi)c_\pi
\prod_i(R_q)_{i,\pi(i)}=q^2G,
\tag{5}
\]

modulo the Plücker relation. All \(c_\pi\) are independently recomputed
from the actual complex spectra. Thus at \(q=1\), \(G\) is exactly
the determinant reflection gap \(g\).

For a real frame, the Hessian separates its real-symmetric coordinates
from the imaginary off-diagonal coordinate \(y\). The cubic covector
has only this last component. Directly,

\[
\mathcal A_{yy}=B,\qquad \ell_y=-4S,
\qquad E=\frac{4S^2}{B}\quad(B>0).
\]

The sign of \(\ell_y\) depends on the fixed orientation convention;
its square and the following criterion do not.

### The sextic certificate and the degenerate case

The independent reconstruction verifies

\[
\frac{GB/4-S^2}{4096}
=\sum_{b=1}^{8}m_b(p)^T G_bm_b(p)
\quad\text{modulo the Plücker relation}.
\tag{6}
\]

The eight matrices have sizes \(4,4,4,6,6,4,4,4\). Each is positive
definite, with all 36 exact LDL pivots strictly positive. The monomials
are cubic, and every coefficient in (6) agrees over the rationals.
The eight integer matrices displayed in the author's appendix were also
parsed and checked entry by entry: they equal \(512000G_b\). Thus the
appendix form \(125(GB/4-S^2)=\sum m_b^TM_bm_b\) has exactly the same
normalization as (6).

For \(B>0\), (6) gives \(G\ge4S^2/B=E\). If \(B=0\), the five
strictly positive coefficients in \(B\) force all coordinates except
\(p_{14}\) to vanish. For a unit Plücker vector this is the coordinate
plane 14. Both \(S\) and \(G\) vanish there, so the kernel condition
and the energy bound are satisfied. This closes the only denominator
degeneracy for this certificate.

The claimed strictness also passes review. Enumerating the supports of
the 36 monomials gives three maximal monomial-zero coordinate planes:
\(\{p_{12},p_{24}\}\), \(\{p_{13},p_{34}\}\), and
\(\{p_{14},p_{23}\}\). The Plücker relation cuts the last one down
to its two axes. Both \(S\) and \(G\) vanish on all four resulting
branches. Since the Gram matrices are positive definite, a zero Schur
numerator must lie on one of these branches and therefore has \(g=0\).
Consequently the energy inequality is strict whenever \(g>0\), exactly
as stated in the algebra note.

The prior independent exact quadratic certificate already proved this
particular support direction on every \(U(4)\). The new contribution is
an explicit direct Schur-energy SOS on the entire real Grassmannian.
It must not be described as a newly settled spectral direction or as a
general solution of (3).


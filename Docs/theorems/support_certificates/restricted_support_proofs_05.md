## Investigation 030 — Tight one-sided torus averages

**Accepted.** The argument in `root_twirl_closure.inc` applies to the
specified 130-ray cone and one-sided diagonal-phase averages. The zero-set
classification and real-profile purification are essential inputs, both
already audited earlier in this campaign.

For

\[
 f(U)=\sum_{I,J}\gamma_{I,J}|\det U[I,J]|^2,
 \qquad (\mathcal T_Vf)(U)=\int f(VDU)\,dD,
\]

Cauchy–Binet gives one summand for each intermediate subset \(K\).
The character belonging to that summand is \(\prod_{k\in K}D_{kk}\).
Distinct subsets give distinct torus characters, so all cross terms
disappear. Therefore

\[
 (\mathcal T_Vf)(U)=
 \sum_{I,J,K}\gamma_{I,J}
 |\det V[I,K]|^2|\det U[K,J]|^2.
 \tag{30.1}
\]

Right diagonal phases leave all squared minors unchanged, whence
\((\mathcal T_Vf)(I)=f(V)\). Both identities hold for arbitrary complex
unitaries; realness is used only in the intermediate analysis of zeros.

### Complete discrete coverage of the hard-generator zeros

For the conventions of the root's quaternion matrices, the hard-generator
equality classification gives

\[
 q^2=(a,a,b,b),\qquad r^2=(b,b,a,a),\qquad a+b=\tfrac12,
 \qquad \prod q_i>0,\quad \prod r_i<0
 \tag{30.2}
\]

when \(a,b>0\), with simultaneous coordinate relabeling allowed. I
independently substituted \(q_i=\pm X\) or \(\pm Y\), with complementary
choices for \(r_i\), into a separately rebuilt \(L(q)R(r)\).
Each entry is a polynomial in the independent basis \(X^2,XY,Y^2\).
The complete enumeration consists of six two-element subsets, eight even
sign choices for \(q\), and eight odd sign choices for \(r\).

All **384** cases have **exactly four** permutations whose selected four
entries vanish identically as polynomials. This verifies the supplied
records, including the recorded first permutation and number of choices.
There are six different first choices across the records. Thus the JSON
phrase `all_have_identical_zero_transversal` must be read as an
*identically zero transversal in each case*, not one permutation shared by
every case.

The endpoints \(a=0\) or \(b=0\) are included directly: assign the signs
of zero coordinates to complete the required sign parities and specialize
the same polynomial identities. No compactness choice of a varying
permutation is required.

### Common laws, including degenerate and complex profiles

The earlier zero-transversal theorem is recorded with a full proof in
`../moc100/review_rounds_021_040.md`, investigations 021–023. Its dense
zero-diagonal case has squared-entry pattern

\[
 \begin{pmatrix}
 0&x&y&z\\ x&0&z&y\\ y&z&0&x\\ z&y&x&0
 \end{pmatrix},\qquad x+y+z=1.
\]

It uses the three double-transposition weights \(x^2,y^2,z^2\) and six
four-cycle weights \(xy,xy,xz,xz,yz,yz\). These reproduce every squared
minor. The sparse proof separately covers a forced unit entry, two
disjoint two-by-two blocks, and their degenerations. It therefore applies
to every unitary with a zero transversal, not merely the dense real case.

Consequently every real profile in (30.2) has a common permutation law.
The second-generator equality classification gives either the uniform
quaternion-square pair with the required opposite product signs, already
included in (30.2), or two distinct coordinate vertices. The latter yield
monomial matrices and have deterministic common laws.

Now let a complex unitary profile have a finite positive decomposition
into real orthogonal profiles, as supplied by the previously proved
profile purification. If a nonnegative generator has value zero at the
complex profile, every component with positive weight has value zero.
Combine the component permutation laws to obtain one law for the original
complex profile. This step is legitimate because the generator is linear
in the profile and nonnegative at every real component. It does not assert
that an arbitrary complex unitary has a pointwise real normal form.

Substituting that law into (30.1) proves

\[
 \mathcal T_V f=\sum_{\sigma}\mu_\sigma f(P_\sigma\,\cdot)
 \quad\text{if }f\in\{H,T_0\},\ f(V)=0.
 \tag{30.3}
\]

Row and column relabelings transport both common laws and zero conditions,
so the same conclusion applies to all 96 relabeled generators. Basic
minor indicators already remain positive combinations of basic indicators
under (30.1), without any zero condition. A positive combination of these
averages that vanishes at the identity has each positive-weight summand
vanishing there, hence belongs to the original cone \(C_{130}\).

This is a limitation of this specific contact-preserving averaging
construction. It does not rule out correlated two-sided averages or new
generators. Positive finite combinations are sufficient for the claim;
any convergent extension by positive integrals would also require, and
can use, closedness of the finite polyhedral cone.


### Actual spectral and quaternion setup for the sextic theorem

Use the spectra \(a,b\), phase \(\eta\), and identity-maximizing column order displayed in Section 1, equations (1)–(4), of the retained [quaternion support theorem](algebra_quaternion_cubic_support.md). Section 2, equations (6)–(11), defines the exact matrices \(L(q),R(r)\), the model \(O=L(q)R(r)\), the Hodge-minor quartics \(\Phi(q,r)\), and the rational coefficient vector \(w_0\). In the notation below,
\[
F_c(q,r)=w_0\cdot\Phi(q,r),\qquad
c_\pi=\operatorname{Re}\!\left(\eta\prod_i(a_i+b_{\pi(i)})\right).
\]
The symbol \(R(r)\) denotes the right quaternion multiplication matrix; \(R_n\) below denotes the scalar squared norm.

The original-order input is retained as the [source certificate](../../../data/certificates/theorems/support_certificates/polyhedral_combined_separation_exact.json). The reordered spectra, supporting phase, profile coefficients, eight cubic bases, and rational Gram matrices are all retained in the [sextic certificate](../../../data/certificates/theorems/support_certificates/algebra_quaternion_cubic_exact.json). Use the reordered data for the identity-maximizing formulas below; do not interchange its last two columns a second time. The cited companion proves the passage from the quaternion identities to the stated full-unitary theorem for this direction; no unrestricted extension is asserted.

Write

\[
 Q_n=\|q\|^2,\quad R_n=\|r\|^2,\quad D=Q_n-R_n,
 \qquad f=hQ_nR_n-F_c(q,r).
\]

The actual source is `polyhedral_combined_separation_exact.json`, with its
third and fourth columns reordered to make the identity maximize. The
independent check reconstructs all 24 actual complex products from the
stored spectra and phase, verifies the reordered profile coefficients,
and obtains

\[
 h=\frac{111645445527}{976562500000}.
\]

It also verifies, as complete polynomial identities,

\[
 OO^T=Q_nR_nI,\qquad \det O=(Q_nR_n)^2,
\]

all 36 equal-norm Hodge-minor identities, and

\[
 h\det O-
 \sum_{\pi}\operatorname{sgn}(\pi)c_\pi
       \prod_iO_{i,\pi(i)}
 \equiv Q_n^2 f\pmod D.
 \tag{31.1}
\]

Thus the target is the actual spectral support expression on unit
quaternion pairs, not an arbitrary common-minor interpolation.

## Investigation 033 — A successful sextic certificate for the same target

**Accepted as an exact positive theorem.** This supersedes the numerical
status of the degree-six probe. The final certificate in
`algebra_quaternion_cubic_exact.json` proves the specified actual spectral
support inequality for every \(U\in U(4)\).

Let

\[
 N=\frac{Q_n+R_n}{2}.
\]

The saved eight blocks consist of explicit vectors \(v_b(q,r)\) of 13
homogeneous cubic polynomials and rational symmetric matrices \(G_b\).
Using separately implemented eight-variable polynomial arithmetic, I
verified

\[
 \boxed{Nf\equiv\sum_{b=1}^{8}v_b^TG_bv_b\pmod{Q_n-R_n}.}
 \tag{33.1}
\]

Every matrix is strictly positive definite, with all **104 exact LDL
pivots** positive. Expanding all matrix products and reducing modulo the
norm equation gives exactly the independently reconstructed sextic
target, whose chosen normal form has 129 terms. The check uses the actual
complex products and determinant identity (31.1), rather than relying
only on equality of 24 vertex samples.

On \(D=0\), the multiplier \(N\) is positive except at the origin. Hence
(33.1) gives \(f\ge0\) at every nonzero equal-norm pair; at the origin
the homogeneous quartic is zero. In particular it proves the support
inequality on the two unit spheres. Every element of \(SO(4)\) is
\(L(q)R(r)\) for a unit pair, and a row sign change handles the other
orthogonal component without changing squared minors. Finally the
already proved equality of unitary and orthogonal profile convex hulls
transfers this linear support inequality to every \(U(4)\).

The source columns were reordered only to simplify contact coordinates;
an all-unitary statement is unchanged by undoing that permutation.
The original source pair is

\[
 a=\left(0,\frac12,1,
 \frac{27223}{109707}+i\frac{24421}{36569}\right),
\]

\[
 b=\left(\frac{352}{3},
 \frac{-19103+16810i}{51493},
 \frac{-501033-262235i}{1603673},
 \frac{-836163-439684i}{1331525}\right),
\]

with the fixed support coefficient

\[
 \eta=\frac{500249382399}{125000000000000}
      -i\frac{997971562341}{62500000000000}.
\]

For these values the theorem is

\[
 \operatorname{Re}\!\left[
   \eta\det\bigl(\operatorname{diag}(a)+
      U\operatorname{diag}(b)U^*\bigr)\right]
 \le \frac{111645445527}{976562500000}
 \quad\text{for all }U\in U(4).
 \tag{33.2}
\]

The same target lies outside the earlier finite cone, its fixed-anchor
quadratic enlargement, and the two quaternion quartic templates audited
above. There is no inconsistency: multiplication by \(N\) permits cubic
squares, which belong to a different certificate class. The positive
identity is a concrete advance beyond those obstructions. It covers this
one \(\eta\), not all supporting phases for the displayed spectral pair.

For acceptance of a positive certificate, completeness of the cubic
symmetry decomposition is unnecessary: the explicit polynomial identity
and positive matrices suffice. Thus this proof does not rely on trusting
the discovery program's symmetry or optimization choices.


## Investigation 035 — An explicit neighborhood and the equality set

**Accepted.** The final corollary in
`algebra_quaternion_cubic_neighborhood_exact.json` follows from exact
signed Gram identities and the strict positivity in investigation 033.
Its claim is a full neighborhood in the real anchored cost coordinates;
actual complex spectral costs are included by intersection.

Let \(p_j\), \(j=1,\ldots,20\), be the quartic anchored profile
polynomials and let \(e_j=p_j(I)\). For a real coefficient vector \(w\),
the centered support deficit is

\[
 f_w(q,r)=\sum_{j=1}^{20}w_j(e_jQ_nR_n-p_j(q,r)).
 \tag{35.1}
\]

The stored center \(w_0\) gives precisely the actual quartic \(f\)
from investigation 033, and \(w_0\cdot e=h\).

### Exact correction identities

For every \(j\), the file supplies eight rational symmetric matrices
\(H_{jb}\), without any positivity requirement, satisfying

\[
 N(e_jQ_nR_n-p_j)
 \equiv\sum_{b=1}^{8}v_b^TH_{jb}v_b\pmod D.
 \tag{35.2}
\]

I independently expanded all 20 identities from the sparse upper-triangle
records, including the factor of two for off-diagonal matrix entries.
All identities match the independently rebuilt profile polynomials
exactly. The 20 target deficits span dimension 13; separately rebuilding
the complete eight-block Gram coefficient image gives rank 178. Those
ranks agree with the reported values. In particular, the neighborhood
argument does not assume that the spectral nonic is locally preserved by
an arbitrary perturbation.

Consequently an exact Gram representation of \(Nf_w\) is

\[
 G_b(w)=G_b(w_0)+\sum_j(w_j-w_{0j})H_{jb}.
 \tag{35.3}
\]

### The rational radius is sufficient

For each center block define

\[
 T_b=\operatorname{tr}(G_b(w_0)^{-1}),\qquad
 B_b=\sum_{j=1}^{20}\sum_{r,s=1}^{13}|(H_{jb})_{rs}|.
\]

I recomputed every inverse matrix with independent rational elimination,
then took its trace. This checks the saved inverse traces through a
different calculation from the author's inverse-LDL formula. I also
recomputed every \(B_b\) from the expanded symmetric correction
matrices, rather than just their sparse upper triangles.

Since the center matrices are positive definite,

\[
 \lambda_{\min}(G_b(w_0))\ge \frac1{T_b}.
\]

If \(\|w-w_0\|_\infty\le\varepsilon\), the perturbation in (35.3)
has operator norm at most \(\varepsilon B_b\): its operator norm is
bounded by its entrywise absolute sum. The exact check gives

\[
 2\varepsilon T_bB_b\le1\quad\text{for every block},
 \qquad \varepsilon=\frac1{100000000000}.
 \tag{35.4}
\]

Thus the perturbation is bounded below by
\(-\lambda_{\min}(G_b(w_0))I/2\), which in turn is bounded below
by \(-G_b(w_0)/2\). Hence

\[
 \boxed{G_b(w)\succeq\tfrac12G_b(w_0)\succ0.}
 \tag{35.5}
\]

The displayed radius is a conservative bound in this particular
20-coordinate representation. It is not claimed sharp or invariant under
arbitrary changes of coordinate scaling. The closed coefficient ball
satisfies the inequality, so it certainly contains an open neighborhood.
Combining (35.2)–(35.5) with the argument of investigation 033 proves

\[
 w\cdot\operatorname{profile}(U)
 \le w\cdot\operatorname{profile}(I)
 \quad\text{for every }U\in U(4)
 \quad\text{whenever }\|w-w_0\|_\infty\le10^{-11}.
 \tag{35.6}
\]

### Equality is exactly the identity profile

At an equal-norm unit quaternion pair, equality in (35.6) means the
positive sum \(\sum_bv_b^TG_b(w)v_b\) is zero. Strict positivity of all
eight matrices forces every cubic vector \(v_b\) to vanish. Applying all
20 signed identities (35.2) then gives every anchored profile coordinate
equal to its identity value. Conversely, that profile has zero deficit
for every coefficient vector.

For an actual unitary, these anchored coordinates force a diagonal
matrix. The two singleton rows give \(|U_{00}|=|U_{22}|=1\), fixing
those rows and columns. The squared minor with rows and columns
\(\{0,1\}\) equals one, forcing \(|U_{11}|=1\); unitarity then fixes
the last row and column. Thus the remaining freedom is diagonal phases.

The extension of the equality statement from real to complex matrices
uses the same positive real-profile decomposition: equality in the
linear support functional forces each real component to be an equality
profile, hence the identity profile. The complex profile therefore is
also the identity profile. In the original, unreordered spectral
coordinates, undo the fixed maximizing column permutation.


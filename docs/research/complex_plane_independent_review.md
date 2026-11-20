### 1. Correction: specify the frame used for the coefficient calculation

At `organized/research/branch_B_positive_gap_budget.md:111`, the frame \(Y\) is arbitrary. However, the coordinate identity at `organized/research/branch_B_positive_gap_budget.md:168–178`,
\[
T=G^{1/2}SG^{1/2},\qquad YTY^*=KSK^*,
\]
uses the particular frame
\[
\boxed{Y_0=KG^{-1/2}.}
\]

**Suggested correction:** insert “For this coefficient calculation choose \(Y=KG^{-1/2}\).”

For another frame \(Y=Y_0Q\), use the generator \(Q^*TQ\). The optimized energy and entire orbit are frame-independent, so this is a local coordinate-convention correction, **not a counterexample or change to \(\kappa_*\)**.


### 2. Projector, frame normalization, and every \(M_{ij}\): **PASS**

References: `organized/research/branch_B_positive_gap_budget.md:99–133` and `organized/research/branch_B_positive_gap_budget.md:168–200`.

Direct calculation verified
\[
J^2=-3I,\quad P^*=P,\quad P^2=P,\quad \operatorname{tr}P=2,
\]
and
\[
G=K^*K=
\begin{pmatrix}
\frac12&-\frac{i}{2\sqrt3}\\
\frac{i}{2\sqrt3}&\frac12
\end{pmatrix},
\qquad
\det G=\frac16,
\qquad KG^{-1}K^*=P.
\]

I also constructed an explicit normalized frame using a Cholesky factor and verified \(Y^*Y=I\) and \(YY^*=P\).

For **each of the six edges**, I independently expanded
\[
144\,(KSK^*)_{ij}\overline{(KSK^*)_{ij}}
\]
and compared every polynomial coefficient with the displayed quadratic form. **All six matched exactly**, including all mixed terms and signs.

The geometric assertions also check:
\[
P_{ii}=\frac12,\qquad P_{12}P_{23}P_{31}=-\frac{i}{24\sqrt3}.
\]
Thus the plane is neither coordinate-containing nor gauge-real.

### 3. Every cubic coefficient and optimized-energy normalization: **PASS**

References: `organized/research/branch_B_positive_gap_budget.md:180–214`.

I calculated each \(C_{ijk}\) in two ways:

* from the normalized Plücker expression, using raw-frame minor products divided by \(\det G\);
* directly from
  \[
  -\Im\operatorname{tr}\bigl(\operatorname{adj}(W_i)W_jTW_k\bigr).
  \]

Both calculations gave the following coefficient vectors for \(48\sqrt3\,C_{ijk}\):

| Triple | Exact coefficient vector |
|---|---|
| \(123\) | \((-1,-1,-2,4)\) |
| \(124\) | \((1,1,-2,-4)\) |
| \(134\) | \((-1,1,0,-2)\) |
| \(234\) | \((-1,1,0,2)\) |

Consequently both normalizations are correct:
\[
\mathcal A(u)=\frac1{144}u^TMu,\qquad
\ell(u)=\frac1{12\sqrt3}q^Tu.
\]

In particular,
\[
\frac14\ell^T\mathcal A^+\ell
=\frac14\frac{144}{(12\sqrt3)^2}q^TM^+q
=\boxed{\frac1{12}q^TM^+q}.
\]
The singular cases were checked separately; this calculation is not relying on an unjustified ordinary inverse.

### 4. Reflection gap, Schur complement, and factor-two scaling: **PASS**

References: `organized/research/branch_B_positive_gap_budget.md:217–240`.

I checked **all 24 signed permutation weights**
\[
\operatorname{sgn}(\pi)\prod_iR_{i,\pi(i)}.
\]
Exactly the nine derangements have weight \(1/9\); all other weights vanish. Also \(\det R=1\). Hence
\[
\boxed{g_R=D/9}.
\]

The block certificate is correctly normalized:
\[
\begin{pmatrix}M&q\\q^T&4\kappa D/3\end{pmatrix}\succeq0
\quad\Longleftrightarrow\quad
q\in\operatorname{range}M,\quad E\le\kappa D/9,
\]
with \(M\succeq0\).

I explicitly repeated the calculation with actual deficits and doubled deficits. Under doubling,
\[
(M,q,D,E,g_R)\longmapsto(2M,2q,2D,2E,2g_R).
\]
Thus **there is no hidden factor-two error** in the ray table or sample.

### 5. Complete extreme-ray enumeration: **PASS**

References: `organized/research/branch_B_positive_gap_budget.md:234–270`.

I independently reconstructed all 24 product-coefficient vectors from the actual spectra, rather than importing a cone certificate.

Exact results:

* determinant witness: \(450\);
* minimum interior slack at \((137,83,-292,19)\): \(262\);
* triples examined: **1,771**;
* triples of rank three: **1,740**;
* feasible orientations before deduplication: **39**;
* distinct primitive feasible rays: **14**.

The resulting ordered ray list agrees **exactly** with all 14 displayed rays.

The completeness argument is sound: the determinant witness eliminates lineality, the strict slack witness establishes full dimension, and every extreme ray therefore has three independent active constraint rows. Exhausting those triples and both orientations finds every extreme ray.

### 6. All ray ratios, singular cases, and 434 principal minors: **PASS**

References: `organized/research/branch_B_positive_gap_budget.md:253–274`.

Every one of the **14 rational energy-to-gap ratios** matches the table exactly.

For every ray, I checked \(q\in\operatorname{range}M\). The only rank-three matrices are the stated tenth and eleventh rays; all others have rank four. On the singular rays I additionally verified the energy using the Moore–Penrose pseudoinverse.

For \(H_{\kappa_*}\), I computed all 31 nonempty principal minors on every ray:

\[
\boxed{434\text{ checked};\quad 425>0,\quad 9=0,\quad 0<0.}
\]

The zero counts are:

* tenth ray: four;
* eleventh ray: four;
* maximizing thirteenth ray: one.

Since \(H_{\kappa_*}\) is linear in the cost coordinates, PSD on the complete ray set proves PSD throughout the cone. **This step covers singular cone boundaries as claimed.**

### 7. Actual sharpness sample and endpoint derivative: **PASS**

References: `organized/research/branch_B_positive_gap_budget.md:278–314`.

Direct multiplication from the actual \(z,\eta\), independently of the ray construction, gives
\[
\eta z=35-5i,\qquad h=143.
\]
All **24 listed deficits** agree exactly.

I obtained
\[
(s_{123},s_{124},s_{134},s_{234})=(-91,353,59,-121),
\]
\[
q=(506,382,-524,-2136)^T,
\]
and the actual, unscaled matrix
\[
M=
\begin{pmatrix}
756&104&-158&-1878\\
104&1228&-786&-1878\\
-158&-786&1568&1416\\
-1878&-1878&1416&9072
\end{pmatrix}.
\]

Direct reflection-determinant evaluation gives
\[
\det(A+RBR^*)=\frac{1697+1850i}{2061},
\]
and therefore
\[
g_R=\frac{506}{3},\qquad
E=\frac{13540961942}{289924245},\qquad
\frac E{g_R}=\boxed{\frac{6770480971}{24450277995}}.
\]

Thus sharpness is attained by finite actual spectra with positive gap and nonzero cubic covector.

I also differentiated the actual determinant at the reflection endpoint, symbolically in all four generator coordinates, and verified the endpoint-gradient identity with its stated sign and normalization.

### 8. Full symbolic Cayley identity and extension to all \(U(2)\): **PASS**

References: `organized/research/branch_B_positive_gap_budget.md:78–88` and `organized/research/branch_B_positive_gap_budget.md:274–276`.

This check was **not limited to evaluations at selected Hermitian matrices**.

Writing
\[
Z=KSK^*,\quad d=\det(G)\det S,\quad \tau=\operatorname{tr}(GS),
\quad \alpha=1-d-i\tau,
\]
I constructed the polynomial ambient Cayley numerator
\[
N=\alpha I+2i(1-i\tau)Z-2Z^2
\]
and verified identically
\[
(I-iZ)N=\alpha(I+iZ).
\]

I then expanded the actual determinant numerator over \(\mathbb Q(\sqrt3,i)\), performed exact polynomial division, and checked **every coefficient** of the gap identity for each of the four independent real cost-coordinate basis vectors. All residual polynomials were zero.

This independently establishes, throughout this spectral slice,
\[
[h-F(U_Y(V(T)))]\det(I+T^2)
=4\mathcal A(T)-2d\,\ell(T)+g_Rd^2.
\]

The extension is valid: the energy budget makes the numerator nonnegative, \(\det(I+T^2)>0\) for Hermitian \(T\), and the Cayley chart is dense in \(U(2)\). Continuity includes the omitted unitaries.

### 9. Supporting-base circle distinction: **PASS**

References: `organized/research/branch_B_positive_gap_budget.md:29–48` and `organized/research/branch_B_positive_gap_budget.md:135`.

I also verified the circle numerator and the identities
\[
D=T+2B-3A,\qquad
\sum_{\text{three-cycles}}g_\pi=2T-4A.
\]
At \(A=0\), nonnegative deficits indeed give \(D\ge T\) and \(|K|\le2T\), making the circle budget automatic.

The stated inclusion in the plane orbit is correct, explicitly:
\[
U(r)=\frac{r+i\sqrt3}{\sqrt{r^2+3}}\,
U_Y\!\left(\frac{r-i\sqrt3}{r+i\sqrt3}I_2\right).
\]
The prefactor is an irrelevant global unitary phase.


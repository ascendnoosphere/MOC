# Contact geometry, orbit, and realification: Cycle 03/04 audit

This symbolic pass started from commit 16e1462, not the older commits
discussed in the attachments. In particular the exact-profile closure,
varying-gap continuation, difference-only isolation, and narrow
imaginary-shift theorem at exactly $2n-1$ contacts are already checked
at that baseline. The Jacobian below is not imported from isolation.

| Cycle 04 / Cycle 03 | New result or test | Remaining gate |
|---|---|---|
| 01 / 01: global contact geometry | [ContactDifferential](MOC/ContactDifferential.lean) checks the ordinary polynomial derivative of every matching product and pivot difference at arbitrary spectra, including vanishing cross-sums, and its quotient form where denominators are nonzero. Opposite translation and compensated common infinitesimal fractional motion are null for every matching coordinate. | Differential rank at the *given* isolated witness need not be full. Higher-contact strata and the near-constant quadratic-margin and relative-dimension gates were not closed. |
| 05 / 04: orbit flow | [DoubleBracketScore](MOC/DoubleBracketScore.lean) checks the trace cycling and differentiable score derivative, equal to the squared commutator Frobenius norm (twice the proposed rank-one variance). | The consecutive assignment-score logistic lower bound is a separate inequality. No tied spectral labels are promoted to true orbit reordering ties. No flow convergence, triple Schur separation, or exhaustive orbit test is claimed. |
| 06 / 06: contact motifs and isolated fibres | [ContactGraphCertificates](MOC/ContactGraphCertificates.lean) selects at most $n-1$ actual old contact labels whose relative moves form a connected graph. Grow the reachable component using one cut-crossing old label at each step; each step adds a new vertex and one label. | Edges are not necessarily active transpositions, and their graph rank is not the polynomial rank. There is no classification of all eight-contact order-four or nine-contact order-five terminal motifs. The suggested finite-chart Bézout count is not an enumeration or support sign proof. |
| 08 / 09: orthogonal realification | [Fixed-anchor order-five obstruction](FixedAnchorOrderFiveObstruction.md) proves on paper that some actual order-five unitary singleton and anchored two-minor tables cannot be mixtures of real orthogonal tables with the anchor row moduli fixed. [GraphEffectIndependence](MOC/GraphEffectIndependence.lean) is the symbolic independence test behind the paper result. | Anchors allowed to vary are not refuted, nor is the objective-specific bound. The graph realization and transfer to actual effect tensors are separate paper steps. The root track handles the repaired paired $T_{85}$ branch. |
| 09 / 08: fractional normalization and moving jets | [FractionalFiniteNormalization](MOC/FractionalFiniteNormalization.lean) maps three prescribed distinct signed spectral points to exactly $0,1,R$, with arbitrarily large real $R$, avoiding poles on the entire prescribed finite spectra. | This does not provide a uniform Schur disk margin and does not justify using a transform at an input pole. Corank jumps, higher-corank moving jets and candidate-neighborhood coverage remain open. |
| 15 / 15: transposition topology | [ContactGraphCertificates](MOC/ContactGraphCertificates.lean) states the precise nonzero graph boundary theorem for *every* nonzero contact of the zero-height strict witness. It gives an actual inactive nonzero transposition neighbor. | No extension to positive height or zero pivot. No graph enclosure, winding argument, or path of flat determinant rotations is inferred. |

**Gauge check.** If $P_\sigma=\prod_j(a_{\sigma(j)}+b_j)$, its raw
derivative is the sum of the omitted-factor products times
$a'_{\sigma(j)}+b'_j$. With
$c=(\sum a_i-\sum b_j)/n$, the fractional tangent is
$a'_i=a_i^2-ca_i$, $b'_j=-b_j^2-cb_j$. Each derivative summand
factors through $(a_{\sigma(j)}+b_j)(a_{\sigma(j)}-b_j-c)$, so the
entire derivative is zero, even at zero factors. On paper, the
two gauges are independent whenever one spectrum has at least
three distinct values: dependence makes the fractional species a
constant translation, putting that spectrum in the roots of a
nonzero monic quadratic. This verifies the rank ceiling modulo
both gauges in that regime, not a lower rank bound.

**Missing Zheng branch.** Beyond the paired case, the concrete
unresolved part of [Zheng, DOI
10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923)
is the positive upper-height, unpaired $T_{85}$ inequality on a
strict candidate with at least eight contacts and $P_0=P_7$.
Because $g_5$ is nonzero, one can normalize its nonzero imaginary
offset and eliminate $g_{14}$ exactly from
$g_5g_{14}=g_{18}g_9$. This leaves the remaining inequality on the
real support-slice strata with at least two extra active labels.
The sharp-count imaginary-shift theorem does not remove the
forced collapse there: its count hypothesis in order four is at
most seven. No missing case table or unnamed positivity premise
was used to close the unpaired branch.

This pass used symbolic proofs and targeted Lean verification.
It did not rerun numerical motif searches, optimize dense orbit
samples, or seek a passing arithmetic certificate.

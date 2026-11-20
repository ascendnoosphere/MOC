# The oriented nonic sheet and the unrestricted kernel chart

31 October 2026.

The following equivalence holds on the whole matching space:

\[
 n_+(M(g)),n_-(M(g))\leq4
 \quad\Longleftrightarrow\quad
 \operatorname{adj}M(g)\succeq0
 \quad\Longleftrightarrow\quad
 \det M(g)=0,\quad\operatorname{tr}(\operatorname{adj}M(g))\geq0.
 \tag{1}
\]

Thus the live sufficient target for unrestricted MOC4 is

\[
 g\in V_{14},\qquad g_\pi\geq0,\qquad
 \operatorname{adj}M(g)\succeq0
 \quad\Longrightarrow\quad
 g=\operatorname{diag}(VXV^T),\quad X\succeq0.
 \tag{2}
\]

We have not proved (2). The exact face30 escape has the opposite adjugate
orientation and therefore does not refute it. Equation (1) includes every
singular-kernel and lower-rank pencil; it needs no source or contact
regularity assumption.

## Proof of the inertia reduction

For a symmetric form with inertia \((p,q,r)\), write \(R\) for its radical.
An isotropic subspace \(U\) of dimension three satisfies

\[
 \dim(U\cap R)\geq\max(0,3-\min(p,q)).
\]

Indeed, the image of \(U\) in the nondegenerate quotient is isotropic and
has dimension at most \(\min(p,q)\).

The universal pencil vanishes on each of the four spaces

\[
 U_i=\{\operatorname{vec}(l_i v^T):v\in\mathbb R^3\},
\]

where \(l_i\) is a tetrahedral row of \(L\). Any three tetrahedral rows
are independent. The corresponding three spaces therefore form a direct
sum equal to \(\mathbb R^9\). Their intersections with \(R\) are also
independent, so every member of the universal pencil obeys

\[
 3\max(0,3-\min(p,q))\leq r.                 \tag{3}
\]

If \(r\geq2\), (3) and \(p+q+r=9\) imply \(p,q\leq4\). In particular,
**every pencil of rank at most seven is neutral in the required sense**.
At rank eight, the only possible inertias are

\[
 (5,3,1),\quad(4,4,1),\quad(3,5,1).
\]

At rank eight the adjugate is a nonzero rank-one matrix. Its nonzero
eigenvalue has the sign of the product of the eight nonzero pencil
eigenvalues. It is positive precisely in the middle case. At rank at most
seven the adjugate vanishes. A nonsingular pencil has both positive and
negative eigenvalues by (3), and its adjugate is indefinite. These facts
prove both equivalences in (1).

The scalar polynomial \(S_8(g)=\operatorname{tr}(\operatorname{adj}M(g))\)
is homogeneous of degree eight. The neutral locus is the oriented sheet
\(N_9(g)=0, S_8(g)\geq0\), with the common rank-at-most-seven boundary
included. This orientation does not assert hyperbolicity of \(N_9\).

When \(S_8(g)>0\), the rational matrix
\(\operatorname{adj}M(g)/S_8(g)\) is the Euclidean orthogonal projector
onto the pencil radical. It supplies a rational projective kernel \(h\).
This projector is not itself a matching Gram.

## A signed Gale representation of the full pencil

Let \(O_\pi=L^T P_\pi L\), let the row \(Q_\pi\) be the row-major
vectorization of \(O_\pi\), and set \(S=\operatorname{diag}(\operatorname{sgn}\pi)\).
Then

\[
 32M(g)=Q^T\operatorname{diag}(\operatorname{sgn}(\pi)g_\pi)Q,
 \qquad
 V_{14}=\ker\bigl([\mathbf1,Q]^TS\bigr).       \tag{4}
\]

The frame \([\mathbf1,Q]\) has rank ten. The exact checker verifies the
pencil identity on all fourteen independent feature columns. It also
checks the orthogonality and both complementary dimensions in (4).

For strictly positive \(g\), a full matching Gram is equivalent to a
correlation matrix \(Y\succeq0\), \(\operatorname{diag}Y=\mathbf1\), with

\[
 \ker Y\supseteq
 \operatorname{col}\bigl(\operatorname{diag}(\sqrt g)S[\mathbf1,Q]\bigr).
 \tag{5}
\]

To see this, write the desired evaluation Gram as
\(Z=\operatorname{diag}(\sqrt g)Y\operatorname{diag}(\sqrt g)\). Its
diagonal is \(g\), and (5) says its range lies in \(V_{14}\). An arbitrary
basis for \(V_{14}\) then gives the fourteen-feature Gram by congruence.
Zero entries of \(g\) require deleting those evaluation rows and first
restricting the feature space to functions vanishing at the contacts.

This is the correlation-matrix realization formulation of ellipsoid
fitting; see Saunderson, Chandrasekaran, Parrilo, and Willsky,
[Diagonal and Low-Rank Matrix Decompositions, Correlation Matrices, and
Ellipsoid Fitting](https://users.cms.caltech.edu/~venkatc/scpw_dlr_simax12.pdf),
Proposition 3.1. Their coherence-below-one-half sufficient criterion does
not cover a generic four-contact cost here: the reduced missing subspace
has dimension ten in twenty evaluation coordinates, so its average
diagonal projection entry is already one half. Formula (4) supplies the
additional signed structure that a proof of (2) would have to use.

## An exact obstruction to a pointwise shorted block formula

There is a cost-dependent rational frame retaining all fourteen matching
directions. Split the rows of \(W=[\mathbf1,Q]\) by permutation parity,
and suppose \(g>0\). Put

\[
 A_e=W_e^T D_{g_e}W_e,\qquad A_o=W_o^T D_{g_o}W_o.
\]

Choose two-column bases \(K_e,K_o\) for \(\ker W_e^T,\ker W_o^T\).
Define ten global matching features \(C\) by

\[
 C_e=D_{g_e}W_e A_e^{-1},\qquad
 C_o=D_{g_o}W_o A_o^{-1}.
\]

Extend \(K_e,K_o\) by zero to the opposite parity. The columns of
\(F_g=[C,K_e,K_o]\) form a basis for \(V_{14}\): applying \(W^TS\) gives
\(I-I=0\) on \(C\), and each parity kernel vanishes separately. The
exact coordinate change in the replay has nonzero determinant.

The proposal to use a block-diagonal Gram
\(T_{10}\oplus E_2\oplus O_2\succeq0\) in this frame is **false**.
Take the previously certified actual ellipsoid-control integer gap vector
\(g_0\) and set

\[
 g=g_0/\max(g_0)+1/10000.
\]

This cost has exact pencil inertia \((4,4,1)\) and an exact strictly
positive fourteen-feature Gram. Nevertheless, a rational evaluation
functional \(x\) has all three diagonal moment blocks

\[
 C^TD_xC\succ0,\qquad K_e^TD_xK_e\succ0,
 \qquad K_o^TD_xK_o\succ0,
\]

while

\[
 x\mathbin{\cdot}g=-268367/200000<0.
\]

The exact LDL pivots prove the three strict inequalities. The replay also
exports a negative integer vector for the full matching moment, so \(x\)
is not a full-SOS separator. It rejects the block restriction. The full
fourteen-feature positive Gram comes from the old exact Gram plus

\[
 \frac{1}{70000}\sum_{j=0}^{33} v_jv_j^T,
 \qquad Vv_j=r_j,
\]

in fourteen-feature coordinates, since the binary ordinary features sum to the
constant seven and span all fourteen dimensions. Cross terms between the
ten common-metric directions and parity kernels are therefore needed even
on this strictly positive actual neutral cost.

Replay:

```
python3 code/research/moc_unrestricted_neutral_shorted_exact.py
```

The output is `neutral/shorted_block_exact.json` in the build directory.

A larger ansatz uses one PSD block on the ten \(C\)-features and another
on the six-dimensional space

\[
 \operatorname{span}\{g,\;g f_h,\;K_e,\;K_o\},
 \qquad f_h=Qh.
\]

Both \(g\) and \(g f_h\) belong to \(V_{14}\), because the constant and
\(h\) are radical directions of \(W^TSD_gW\). They also lie in the
ten-dimensional \(C\)-space. This ansatz restores couplings between the
radical and parity-kernel directions. It still omits thirty-two possible
couplings between the remaining eight \(C\)-directions and the four
parity-kernel directions.

At an added constant of \(10^{-7}\), all 360 neutral nonordinary fixtures
from the vertex tests below, plus three controls, gave repaired numerical
PSD Grams in this larger cone. The smallest Gram eigenvalue in orthonormal
block coordinates was about 0.1247, and the largest cost residual was below
\(1.5\cdot10^{-15}\). This verifies the numerical construction on those
inputs. Uniform feasibility remains unproved. The least-Frobenius-norm
linear section of this larger cone is indefinite at the exact ellipsoid
control, so a positive linear section does not follow from these tests.

A further 3,000 actual complex-source samples, half Gaussian integer
sources and half perturbations of the exact triangle countercost, passed
this larger ansatz at an added constant of \(10^{-6}\). Their numerical
least-norm sections were positive. These samples impose no finite-spectrum
classification or global claim.

The common-metric basis also gives a closed partial positive construction.
Let \(G=A_e+A_o\) and

\[
 R=G^{-1/2}(A_e-A_o)G^{-1/2},\qquad
 T=\tfrac12G^{1/2}(I-|R|)G^{1/2}.
\]

Since \(-I\prec R\prec I\), \(T\succ0\). Set

\[
 A_\infty=\tfrac12G^{1/2}(|R|+R)G^{1/2},\qquad
 B_\infty=\tfrac12G^{1/2}(|R|-R)G^{1/2}.
\]

Then \(A_e-A_\infty=A_o-B_\infty=T\). The two residual matrices are PSD
and each has rank four on the generic neutral sheet. The parity identity

\[
 D_{g_e}=C_eA_eC_e^T+
 K_e(K_e^TD_{g_e}^{-1}K_e)^{-1}K_e^T
\]

follows by inverting the \(D_{g_e}^{-1}\)-orthogonal basis \([C_e,K_e]\).
It gives a positive matching evaluation Gram

\[
 X_{\rm base}=CTC^T+
 K_e(K_e^TD_{g_e}^{-1}K_e)^{-1}K_e^T+
 K_o(K_o^TD_{g_o}^{-1}K_o)^{-1}K_o^T,
\]

with \(g=\operatorname{diag}X_{\rm base}+r\), where
\(r_e=\operatorname{diag}(C_eA_\infty C_e^T)\) and
\(r_o=\operatorname{diag}(C_oB_\infty C_o^T)\). Thus the remaining
nonnegative residual has four amplitudes on each parity. This is a
uniform partial identity, not a full Gram reconstruction.

The parallel-sum recursion explains this formula without selecting a
common positive plane:

\[
 A'=A(A+B)^{-1}A,\quad B'=B(A+B)^{-1}B,
 \qquad A'-B'=A-B.
\]

Whitening the initial sum makes the two matrices commute, reducing their
sum recursion to the scalar Newton iteration for an absolute value.

This particular residual cannot simply be declared SOS. On both exact
actual controls it lies outside \(V_{14}\), and full-moment numerical
separators give pairings approximately \(-0.1063\) and \(-0.0670\).
Those numerical diagnostics are in `neutral/partial_shorting.json`.
A successful completion must redistribute the positive base rather than
add a separately positive Gram for this residual.

## Unrestricted chart experiments

We used all nine entries of an invertible real \(H\) and all four entries
of a balanced real \(B\), with

\[
 A=\frac{2H(B\circ H)^TH-sH}{\det H},
 \qquad s=\sum_{ij}B_{ij}H_{ij}^2.
\]

The resulting pencil kills \(\operatorname{vec}H\) identically. We recovered
the twenty-four costs by the global signed-assignment formula and shifted
them by their minimum. This samples the unrestricted invertible-kernel
chart, rather than a prescribed support family.

A run with 18,770 valid, moderately conditioned \(H,B\) pairs gave 17,167
neutral pencils. Each of these costs passed the ordinary-cone linear
program, providing numerical ordinary-square decompositions. These
counts do not establish a density or covering claim.

To reach the smaller nonordinary region, we optimized the four \(B\)
coordinates at each \(H\). With mean cost fixed, nonnegativity is a
four-variable linear program. Over 12,000 random \(H\) with a wider
singular-value range, a fixed ordinary-cone facet selected sixteen
nonordinary neutral costs, each with four contacts. A full contact-null
moment barrier found no negative feasible pairing. Six were provisionally
actual under the separate numerical lift test; ten were provisionally
nonactual. Neither the positive barrier values nor the numerical lift
labels are exact certificates.

The trace-moment oracle includes all fourteen features before contact
reduction. It checks whether the cost lies in the full product image;
a failure gives a separating moment-kernel direction. This matters at
the cap itself, where the reduced feature space has dimension one. The
oracle correctly separates that known non-SOS cap and accepts an ordinary
ray. Positive returned values remain upper bounds on the dual minimum.

A further 15,000 global and 15,000 local \(H\) trials minimized three exact
full-PD dual pairings over the full four-dimensional chart polytope.
Only the known face30 escape anchor gave a negative pairing. Its inertia
was \((5,3,1)\). No neutral negative candidate resulted. The large contact
masses in these fixed duals make their negative regions narrow, so this
failure provides little evidence for (2).

We also enumerated full four-dimensional cost-polytope vertices at
1,000 global \(H\) and 1,000 \(H\) near the known escape. The runs produced
63,451 and 57,190 numerical vertices. Among them, 244 and 116 nonordinary
vertices were neutral. None gave a negative full moment pairing. These
are unrestricted-chart discovery tests, not a proof by contact types.

A pointwise alternating search then varied all nine \(H\) entries, solved
the four contact equations for \(B\), and alternated full moment updates.
Analytic cost and spectral derivatives were checked against independent
centered differences. Its 240 recorded endpoints produced no negative
candidate meeting the nonnegativity and oriented-minor constraints.

## Replays and remaining work

The exact replay is

```
python3 code/research/moc_unrestricted_neutral_adjugate.py
```

It writes `build/moc_unrestricted_20261031/neutral/adjugate_exact.json`.
The search code and raw records are in

```
code/research/moc_unrestricted_neutral_kernel_search.py
code/research/moc_unrestricted_neutral_dual_chart.py
code/research/moc_unrestricted_neutral_vertices.py
code/research/moc_unrestricted_neutral_variational.py
code/research/moc_unrestricted_neutral_shorted.py
code/research/moc_unrestricted_neutral_shorted_actual.py
build/moc_unrestricted_20261031/neutral/
```

The unresolved step is a positive fourteen-feature Gram for (2), or an
exact counterexample to (2). In the latter case the source-selected complex
structure and Lorentz real form must remain in the actual-only target.
The oriented-adjugate reduction does not supply that missing source data.

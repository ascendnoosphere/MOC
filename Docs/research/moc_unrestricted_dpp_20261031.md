# Source-dependent row transport for unrestricted MOC

31 October 2026. This pass does not prove unrestricted MOC or produce a
counterexample to it. The full row-mixture statement below remains the target.
Two narrower mechanisms fail by exact rational certificates, and an earlier
prescribed-row obstruction is replayed. These are distinct from the target.

The verifier and search are in
[moc_unrestricted_dpp_transport.py](../../code/research/moc_unrestricted_dpp_transport.py).
Artifacts are in `build/moc_unrestricted_20261031/dpp/`.

## The complete first-row transport target

For a unitary (U\in U(n)), complex spectra (a,b), and permutations

\[
z_\pi=\prod_i(a_i+b_{\pi(i)}),\qquad
d=\det(D_a+UD_bU^*),\qquad q_{ij}=|U_{ij}|^2,
\]

put

\[
K_i=\sum_jq_{ij}\operatorname{conv}
       \{z_\pi:\pi(i)=j\},\qquad
K=\operatorname{conv}\bigcup_iK_i.
\tag{1}
\]

The candidate is (d\in K), for every (n,U,a,b). Each (K_i) is contained
in the ordinary permutation hull, so this candidate would prove all orders
of MOC. It allows the first row to be random and source-dependent. It does
not require the conditional minors of (U) to obey a smaller MOC statement.

There are three exactly equivalent finite formulations of this candidate:

* (d\in K).
* For every complex support direction (\eta),
  \[
  \Re(\eta d)\le\max_i\sum_jq_{ij}
       \max_{\pi(i)=j}\Re(\eta z_\pi).
  \tag{2}
  \]
* There are nonnegative numbers (t_{i\pi}) with
  \[
  \sum_{i,\pi}t_{i\pi}=1,\quad
  \sum_{\pi:\pi(i)=j}t_{i\pi}
     =q_{ij}\sum_\pi t_{i\pi},\quad
  \sum_{i,\pi}t_{i\pi}z_\pi=d.
  \tag{3}
  \]

To check the equivalence, a law with row (i) fixed has independent choices
of a convex combination in every fiber \(\pi(i)=j\), weighted by (q_{ij}).
This gives exactly (K_i). Mixing the row choices gives (3), with
\(\alpha_i=\sum_\pi t_{i\pi}\). Taking a support function gives (2).
Conversely, separation of a point from the finite polygon (K) gives a
direction violating (2). Thus a proof of the support inequality constructs
a positive global matching law; a single support violation disproves this
particular transport law.

This distinction matters: choosing a different row for each support
direction is sufficient to prove membership in the *convex hull* (K).
It does not establish membership in the union of the (K_i).

## The prescribed-row counterexample is real

The earlier obstruction in `moc_global_barycentric_conditioning.py` is
replayed exactly, so random tests of a prescribed row must not be interpreted
as evidence of a universal prescribed-row law. Set

\[
U=\frac1{\sqrt{525}}
\begin{pmatrix}5&16&-10&-12\\16&-11&-12&2\\-10&-12&-5&-16\\-12&2&-16&11\end{pmatrix},
\]

\[
a=(0,1,197/50-193i/50,7/100-19i/100),
\]

\[
b=(339/100-31i/50,21/100+4i,43/100+17i/100,-21/100+7i/50),
\quad\eta=6218+7832i.
\]

The actual support value exceeds the row-0 bound by

\[
\frac{45051533162935063}{13781250000000}>0.
\]

The excesses over the other three row bounds in this same direction are
negative, approximately (-41236,-59973,-64275). Thus this is an exact
failure of (d\in K_0), while the mixed-row support inequality survives
this direction. Positive ordinary-hull weights on permutation indices

\(4,9,16\) are also checked. `--prescribed-exact` writes the complete
rational replay to `prescribed_row_exact_replay.json`.

## Exact failure of adaptive polar boundary completion

Let

\[
U=\frac17\begin{pmatrix}6&-2&-3\\-2&3&-6\\-3&-6&-2\end{pmatrix},
\quad a=(3,0,-3),\quad b=(4,3,0).
\]

This is the rational Householder reflector (I-vv^T/7), (v=(1,2,3)^T).
For an invertible matrix (T), write

\[
F(a,b,T)=\frac{\det(D_aT+TD_b)}{\det T}.
\]

Delete row (i), column (j) from (U), obtaining (W); let (r) be the
remaining part of row (i), and \(s=|U_{ij}|>0\). Then

\[
P=\frac{r^Tr}{1-s^2},\qquad
Q=W\left(I+\frac{r^Tr}{s(1+s)}\right),\qquad
W=Q(I+(s-1)P).
\]

The matrices (Q) and (Q(I-2P)) are rational orthogonal matrices. The
unitary-completion circle is (Q(I+(\zeta-1)P)), \(|\zeta|=1\).
For the deleted spectra the observable has the form

\[
F(\zeta)=A\zeta+B+C/\zeta,\qquad A,B,C\in\mathbb R.
\]

Consequently the largest real full-branch value on the entire circle is

\[
(a_i+b_j)B+|(a_i+b_j)(A+C)|,
\]

attained at one of \(\zeta=\pm1\). This bounds *every positive probability
measure* on that circle, including measures that depend on all the spectra.
The three row bounds after weighting branches by (q_{ij}) are exactly

\[
\left(-\frac{1294299}{207025},
      -\frac{8343}{1225},
      -\frac{5571}{1225}\right).
\]

But

\[
d=-\frac{207}{49},\qquad
d-\max_i(\text{row boundary bound})=\frac{396}{1225}>0.
\tag{4}
\]

Thus even mixing rows and arbitrary positive branch boundary measures does
not repair this polar-completion ansatz.

The full row transport (1) does hold for this example. In zero-based
lexicographic order on (S_3), the positive permutation weights are

\[
(0,36,4,0,0,9)/49.
\]

They have every Born marginal (q_{ij}) and reproduce (-207/49). In
particular the target lies in every (K_i). The verifier checks this
control as well as every Laurent coefficient and boundary maximum.
The artifact is `polar_adaptive_exact.json`.

## Exact failure of a positive-compound shortcut

A tempting way to prove (2) is to retain only positivity of all squared
minors. That relaxation is insufficient, even for actual product spectra.
Use

\[
a=(0,100,-214+146i,269-294i),\quad
b=(-207-148i,-28-84i,-59+82i,83+104i),\quad\eta=-9+4i.
\]

In lexicographic order on (S_4), take the real signed coefficients

\[
y=\frac1{48}(1,5,-3,1,1,-5,5,5,5,3,-3,1,
             5,-3,3,5,1,5,3,1,5,-3,5,5).
\]

Their total is one, and all 70 subset-matching coordinates

\[
\rho(I,J)=\sum_{\pi:\pi(I)=J}y_\pi
\]

are nonnegative. Their singleton matrix is

\[
q=\frac13\begin{pmatrix}0&1&1&1\\1&1&1&0\\1&1&0&1\\1&0&1&1\end{pmatrix}.
\]

Nevertheless, with (h_\pi=\Re(\eta z_\pi)),

\[
\sum_\pi y_\pi h_\pi=19153162888,
\]

whereas the four first-row support bounds are

\[
\frac13(56891674091,56989233595,57224272499,57246457720).
\]

The signed observable exceeds their maximum by exactly

\[
\frac{213030944}{3}>0.
\tag{5}
\]

It exceeds their mean by (495438917/4). Thus neither the full mixed-row
inequality nor its stronger uniform-row version follows merely from
nonnegative compound coordinates and the actual-source product relations.

This pseudo-profile is not the squared-minor profile of a unitary matrix.
Rows 0 and 1 of any unitary with this (q) overlap only in columns 1 and 2,
where all four entry moduli equal (1/\sqrt3). Orthogonality forces the two
terms in that row inner product to cancel. It then forces the squared
minor on rows 01, columns 12 to be (4/9). The pseudo-profile instead has
\(\rho(01,12)=1/3\). This is an explicit missing unitary constraint, rather
than an unexplained failure of an LP relaxation.

Equivalently, set

\[
M_{ij}=\max_{\pi(i)=j}h_\pi,\qquad
\delta_\pi=\frac14\sum_i M_{i,\pi(i)}-h_\pi\ge0.
\]

Then (\sum_\pi y_\pi\delta_\pi=-495438917/4). Hence this source deficit
cannot be a nonnegative linear combination of subset-matching indicators.
The artifact is `uniform_row_cone_failure.json`; `--cone-exact` verifies all
70 signs, both strict gaps, and the unrealizability check in rational
arithmetic.

## Search coverage and source normalization

The inherited search fixed (a_0=0,a_1=1) and tested only real parts.
Such a chart still requires a free support angle. General affine
normalization rotates all products by a common complex scalar, so omitting
that angle does not cover all spectral inputs and support directions.
The new search includes \(\eta=e^{i\theta}\).

There is a further useful exact normalization. For

\[
f(z)=\frac{\alpha z+\beta}{\gamma z+\delta},\quad
a'_i=f(a_i),\quad b'_j=-f(-b_j),
\]

assume the denominators are nonzero. Both (d) and every (z_\pi) are
multiplied by

\[
L=\frac{(\alpha\delta-\beta\gamma)^n}
        {\prod_i(\gamma a_i+\delta)\prod_j(\delta-\gamma b_j)}.
\tag{6}
\]

For matrices, multiply (A'+B') on the left by \(\gamma A+\delta I\)
and on the right by \(\delta I-\gamma B\). The result is
\((\alpha\delta-\beta\gamma)(A+B)\), since the ordered (AB) terms
cancel. Taking determinants proves (6); the scalar products give the
same formula directly. The eigenvectors and (q) do not change.
Therefore the entire row-mixture test is covariant under this transformation.
A generic chart can fix three distinct (a)-points to (0,1,i), while
retaining the free support angle. The code supports both charts.

All-angle checks explicitly construct the planar polygons (K_i) by
Minkowski sums and then take their joint convex hull. Covariance whitening
reduces numerical problems for thin product clouds. This is a finite
geometric membership computation, not a proof of universal validity.

The inherited (n=4,5) optimized candidates pass this all-angle replay.
A scan of 4,099 existing noncontrol (n=4) records used 256 support angles
and polygon checks when the grid gap exceeded (-10^{-4}). It found no
robust violation. A nearly scalar, nearly permutation record has a positive
floating gap of order (10^{-18}) in the normalized physical coordinates;
this is not evidence of a strict mathematical counterexample.

Further searches vary the actual spectra, support angle, and real or
complex Cayley coordinates of (U). Searches near dense (Q_{59}) use an
entry-square cap to avoid the uninformative equality limit at permutation
matrices. These are adversarial numerical tests, not exhaustion or interval
certificates. Search settings, seeds, matrices, spectra, and evaluations
are stored in the JSON records.

The completed new searches have the following counts. Two (n=4) runs
optimize the stronger uniform-row bound; every evaluation also tests the
full mixed-row bound.

| Dimension | Optimized runs | Source support evaluations | Largest optimized mixed-row gap |
| --- | ---: | ---: | ---: |
| 4 | 20 | 4,842,729 | (-6.4658\cdot10^{-9}) |
| 5 | 2 | 343,546 | (-2.6652\cdot10^{-5}) |
| 6 | 2 | 254,232 | (-6.9934\cdot10^{-6}) |

All 24 optimized source tuples also pass the all-angle polygon check.
The near-zero (n=4) tuple has a unitary approaching a permutation matrix,
so it does not suggest an unexplained dense equality case. The three-point
Möbius chart and capped searches near (Q_{59}) remain strictly negative,
with best normalized gaps about (-1.06\cdot10^{-5}) and

(-2.20\cdot10^{-5}), respectively. The inherited 11 fixed-unitary runs
contain another 2,022,925 evaluations. None of these counts denotes an
independent random sample or a finite exhaustive proof.

A separate seeded stress test of 770,000 sources with real (a) and purely
imaginary (b), in dimensions 4, 5, and 6, also finds no positive real-support
gap. It includes rational reflectors, complex Haar mixers, (Q_{59}),
(O_{525}), and the real Paley conference matrix of order 6. This restricted
test is recorded separately in `real_imag_batch.json`.

`transport_summary.json` consolidates the optimized runs and recomputes
their polygon checks with the current whitening code.

The remaining proof obligation is precisely (2) for genuine unitary
profiles. The two exact obstructions identify what a proof cannot discard:
the full conditional permutation hulls and the orthogonality relations
between different minors.

## Reproduction

```sh
python3 code/research/moc_unrestricted_dpp_transport.py --exact --cone-exact --prescribed-exact
python3 code/research/moc_unrestricted_dpp_transport.py --replay-saved
python3 code/research/moc_unrestricted_dpp_transport.py --corpus --n 4
python3 code/research/moc_unrestricted_dpp_transport.py --summarize
python3 code/research/moc_unrestricted_dpp_transport.py --search --kind real --n 4 --base Q59 --init-saved Q59 --chart 3 --radius 10 --unitary-radius .3 --cap .85 --iters 1800 --restarts 2 --popsize 9 --seed 1210031
```

No external theorem is invoked in the two new obstruction proofs or in
the transport-body equivalence. Existing context about projection DPP
couplings and Grace-like polynomials is documented with primary sources in
`moc_moonshot_fermionic_20261031.txt` and
`grace_semigroup_bridge_20261031.txt`; neither supplies (2).

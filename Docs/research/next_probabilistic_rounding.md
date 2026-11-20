# Positive flag disintegration with an observable-only change of measure

## Outcome and first missing step

This note constructs and exactly verifies a positive stochastic bridge at an
input that excludes every unmodified projection-DPP flag law. It also solves an
independent capped-positive-operator problem. The bridge preserves the evaluated
determinant, rather than all minor marginals; the all-source inequality needed
for unrestricted Marcus–de Oliveira (MOC) remains open.

Write
\[
 d=\det(D_a+UD_bU^*),\qquad z_\pi=\prod_i(a_i+b_{\pi(i)}).
\]
For a full-support reference flag law \(q\), define the diagonal normal observable
\(T=\operatorname{diag}(z_\pi)\). A sufficient bridge is a positive diagonal
operator \(R\) satisfying
\[
 0\preceq R\preceq C I,\quad \operatorname{Tr}(Q R)=1,\quad
 \operatorname{Tr}(QRT)=d,\qquad Q=\operatorname{diag}(q_\pi).
 \tag{1}
\]
Here \(R\), and even \(C\), may depend on both spectra. An arbitrary positive
law is recovered as \(w_\pi=q_\pi R_{\pi\pi}\). Keeping \(R=I\), or requiring its
change of measure to preserve all prefix marginals, is demonstrably too strong.

The remaining all-source bound compares the scalar support
\(\Re(\eta d)\) with the capped-operator support in (8), for an actual
unitary flag reference and some controlled finite \(C\). Taking
\(C=1/\min q_\pi\) makes this equivalent to MOC itself. The results below
supply the positive-operator optimization, flag disintegration, and a small
exact repair at a singleton-obstructed unitary input.

## 1. What the principal archive arguments actually permit

The archive's common-law transfer theorem is valid: real signed Leibniz
amplitudes
\[
 c_\pi=\Re\left(\operatorname{sgn}(\pi)
             \prod_i U_{i,\pi(i)}/\det U\right)
\]
have total one and every subset marginal \(|\det U[I,J]|^2\). Laplace expansion
and the complementary-minor identity prove this. They are generally signed.
A strictly positive common law at one mixer can be transported to a small
unitary neighborhood by adding the difference of these signed amplitudes.
This argument is local and cannot be extended through a negative weight
without another construction.

The categorical forest proof eliminates interference because a forest has at
most one edge subset of prescribed vertex degrees. On one alternating cycle,
two admissible intermediate subsets instead give a rank-one middle-degree
interference term. The archive's explicit parity correction is positive for
balanced gates and restricted biased-gate phases. That restriction is a real
positivity condition, not something monoidal composition removes.

The repeated-eigenvalue proof is an edge-to-vertex flow: the wedge masses
\(|x_i y_j-x_j y_i|^2\) obey the cut inequalities by Cauchy–Binet. The n=4
zero-pair proof uses a different, smaller doubly stochastic matrix containing
only surviving minors. Neither needs or implies a full all-minor common law.
The large-shift theorem proves uniform support stability only after a scalar
shift; it is not a continuation back to the original spectra.

The existing heat calculation has genuinely positive finite-time weights,
not a determinant martingale at time zero. Its two decay rates \(-4,-6\)
permit even a point initially at the permutation centroid to move away.
Exact obstructions exclude the existing polar boundary completion and every
single-projector reducer. General rank-two reducers remain a separate stopping
family to investigate.

## 2. Exact legitimate DPP disintegrations

Fix a row order and let
\[
 V_k=\operatorname{span}\{\overline{U_{1,:}},\ldots,
                          \overline{U_{k,:}}\},\quad
 P_k=U_{[k],:}^*U_{[k],:},\quad
 \mu_k(J)=|\det U[[k],J]|^2\quad(|J|=k).
\]
The conjugation in the definition of \(V_k\) matters for complex matrices.
The \(P_k\) are nested orthogonal projections. A covering coupling is a
nonnegative array \(L_k(I,J)\), supported on \(I\subset J\), with marginals
\(\mu_k,\mu_{k+1}\). Projection-DPP stochastic domination supplies existence;
in a finite instance it can instead be checked by an exact transportation
flow. Define, on positive-mass states,
\[
 K_k(I,J)=L_k(I,J)/\mu_k(I).
 \tag{2}
\]
Then \(J_0\subset\cdots\subset J_n\) is a genuine Markov flag with these DPP
marginals. The added label at step \(k\) is \(\pi(k)\). Its probability is
\[
 q_\pi=\prod_{k=0}^{n-1}K_k(J_k,J_{k+1}).
 \tag{3}
\]
Zero-probability states need no conditional distribution; arbitrary versions
there do not alter the process. Full support is **not** asserted for every
unitary. It is proved by explicit positive flows for the instance below.

A different legitimate disintegration, useful for sampling a single fixed
projection-DPP, is Palm conditioning. For a rank-k projection \(P\), select
an occupied coordinate \(j\) with probability \(P_{jj}/k\), and replace its
kernel on the remaining coordinates by
\[
 P^{(j)}=P_{\bar j,\bar j}
       -P_{\bar j,j}P_{j,\bar j}/P_{jj}.
 \tag{4}
\]
This is a rank-(k-1) projection. Successive selection samples an ordered
DPP set, each ordering having probability \(\det P[J,J]/k!\). Formula (4)
follows from the determinant Schur complement and the projection identity.
It does not by itself couple different row-prefix subspaces; confusing these
two disintegrations would silently add unsupported compatibility.

Every flag satisfying the prefix marginals has
\[
 \Pr(\pi(k)=j)=\Pr(j\in J_k)-\Pr(j\in J_{k-1})=|U_{kj}|^2.
 \tag{5}
\]
Thus choosing different covering couplings, different row orders, or mixing
such laws cannot evade the archive's singleton obstruction.

## 3. Change the measure, rather than claiming extra DPP compatibility

Let \(g:\mathbb C\to[0,\infty)\) with
\(E_q g(z_\pi)=1\). At an ordered-prefix history \(t\), put
\[
 h(t)=E_q[g(z_\pi)\mid t],\qquad
 K^h(t,tj)=K(J,J\cup\{j\})\,h(tj)/h(t).
 \tag{6}
\]
The second formula is used only when \(h(t)>0\). The backward equation
\(h(t)=\sum_jK(J,Jj)h(tj)\) proves positivity and normalization. Telescoping
gives terminal law \(w_\pi=q_\pi g(z_\pi)\). In particular
\[
 E_w z_\pi=d\quad\Longleftrightarrow\quad E_q[g(z_\pi)z_\pi]=d.
 \tag{7}
\]
Now \(M_k=E_w[z_\pi\mid t_k]\) is a bounded complex martingale with
\(M_0=d\), \(M_n=z_\pi\). This martingale exists **after** solving (7); invoking
the tower property does not solve (7).

The tilted process generally is not a projection-DPP flag. That is an
intended, necessary change. If a state-compressed implementation is desired,
retain the chosen set **and the running product**
\(r_k=\prod_{i\le k}(a_i+b_{\pi(i)})\). The original transition depends on the
set and the terminal reward depends on the final running product, so backward
conditioning is Markov on this augmented state. Set-only conditioning loses
spectral information. Full ordered histories always work, including zero
factors, collisions of partial products, and singular determinant matrices.

## 4. Independent auxiliary problem: capped positive expectation

**Problem.** Given a finite probability space \((\Omega,q)\), a diagonal
normal observable \(T\), and \(C\ge1\), determine all expectations attainable
by density operators \(0\le R\le CI\), \(\operatorname{Tr}(QR)=1\).
Allowing non-diagonal R makes no difference, since only its diagonal enters
these traces and its diagonal lies in [0,C].

**Solution.** For a real direction \(\eta\), order
\(x_\omega=\Re(\eta T_\omega)\) decreasingly as
\(x_1\ge\cdots\ge x_N\), carrying masses \(q_i\). Let m be the first index
with \(C\sum_{i\le m}q_i\ge1\). The exact support function is
\[
 H_C(\eta)=C\sum_{i<m}q_i x_i+
             (1-C\sum_{i<m}q_i)x_m.
 \tag{8}
\]
Ties and zero masses cause no problem. The attainable set is precisely the
intersection of the halfplanes \(\Re(\eta z)\le H_C(\eta)\).

Proof: if \(x_i>x_j\), \(w_i<Cq_i\), and \(w_j>0\), moving the smaller of
the available masses from j to i strictly improves the objective. Repeating
leaves exactly the greedy weights in (8). They are feasible, so the bound is
attained. Compact convex separation proves the final assertion. This solves
a positive-operator problem without determinant assumptions.

A useful companion problem is the **least total-variation repair**:
minimize \(\tfrac12\sum|w_\pi-q_\pi|\) subject to probability and the one
complex moment. Write \(w=q+p-m\), \(p\ge0\), \(0\le m\le q\), and minimize
\(\sum p\). With \(A_\pi=(1,\Re z_\pi,\Im z_\pi)^T\), this is the finite
positive-measure LP
\[
 [A,-A](p,m)=(0,\Re(d-E_qz),\Im(d-E_qz))^T.
 \tag{9}
\]
At optimum p and m never overlap, proving that its value really is TV.
The code verifies primal feasibility, exact dual reduced-cost signs, and
primal=dual over the rationals, not just a solver success flag.

The attempted general proof was to apply (8) to an honest flag q and control
\(H_C-\Re(\eta d)\) using only nested DPP identities. It stops here: those
identities force (5), and the strict example below already makes C=1 fail.
Increasing C genuinely repairs the example, but positivity or negative
association alone does not establish (8) at that larger C for every spectrum.
No general upper bound on the necessary C has been derived.

## 5. Exact repair of a singleton-obstructed input

Use
\[
 U=\frac1{59}\begin{pmatrix}-25&46&16&22\\-46&-31&20&-2\\
 -16&20&-11&-52\\22&2&52&-17\end{pmatrix},
\quad a=(0,1,-2+2i,2-2i),\quad b=(2+i,-2-2i,1+i,2).
\]
Then \(d=(94358-98282i)/3481\). The actual row-prefix DPP masses are,
in lexicographic subset order,
\[
 \mu_1=(625,2116,256,484)/3481,
\quad\mu_2=(2401,16,324,576,100,64)/3481,
\quad\mu_3=(289,2704,4,484)/3481.
\]
Reserve one integer unit on every legal covering edge, then solve the
remaining integer transportation problems. All remaining supplies and
demands are feasible; the script checks every exact row and column sum.
This gives an honest full-support q with minimum mass \(1/1127844\).
Its moment is not d:
\[
 E_qz=112887644/4264225-25720411943i/921072600.
\]
The independently certified exact answer to (9) is
\[
 \min_w\operatorname{TV}(w,q)=
 \frac{41057033}{10463384736}=0.00392387683678881\ldots.
 \tag{10}
\]
An exact dual multiplier is
\((10/71,1/568,-2/213)\) with the bound corrections recorded by the code.
All 24 products are distinct. Consequently \(g(z_\pi)=w_\pi/q_\pi\) is an
observable-only density, not a hidden dependence on the permutation label.
Its largest value is
\[
 C=\frac{305940425}{264883392}=1.15500040485739\ldots.
 \tag{11}
\]
The exact backward h-equations, normalized transition probabilities, complex
martingale tower identities, and terminal moment are all verified. Some
terminal densities are zero; no division by zero is used at unvisited
histories. Thus a **0.3924% total-variation change** of this DPP flag law reproduces
the determinant, with a maximal density increase of 15.5%.

There is also a universal lower bound against *any* honest flag reference
at this U and these spectra. Set
\[
 G=\begin{pmatrix}124&24&108&0\\4&-136&44&0\\
104&-776&416&0\\0&0&0&0\end{pmatrix},\quad H_\pi=\sum_iG_{i,\pi(i)}.
\]
All 24 exact inequalities
\(7\Re z_\pi+\Im z_\pi\le212+H_\pi\) hold. Equation (5) fixes
\(E_qH=\sum G_{ij}|U_{ij}|^2\), whereas reproducing d forces its increase
by at least \(6392/3481\). Since expectation differences are bounded by
\(\operatorname{osc}(H)\operatorname{TV}(w,q)\),
\[
 \operatorname{TV}(w,q)\ge799/570884>0.
 \tag{12}
\]
The nearest-law result (10) is above this reference-independent lower bound.

For completeness, the all-minor obstruction is checked separately:
\[
 f=\rho(3,3)+\rho(2,4)+\rho(12,13)-\rho(13,23)\ge0
 \quad\hbox{at all permutation matrices},\qquad f(U)=-55/3481.
\]
The script verifies every permutation inequality and all four actual minors.
This is a full exact archive argument showing why common minor laws fail;
it is not asserted to be Drury's original counterexample matrix.

## 6. Kovačec's 2026 conjecture: actual argument inspected

Read the full seven-page primary preprint, DMUC 26-11 v1, 7 April 2026:
<https://www.mat.uc.pt/preprints/ps/p2611.pdf>. Proposition 2 is the exact
2-by-2 Givens segment identity. Corollary 4 places all transposition segments
in the determinant image. Definition 6 uses ray visibility, not merely the
unbounded-face terminology. Conjecture 7 says that the image stays within
the resulting Jordan polygon, stronger than the original convex hull.
The numerical Givens/streak evidence in pp. 6–7 does not prove containment
for general paths.

The archive counterexample's proof addresses those qualifications rather
than comparing to the wrong convex hull. Reran
`python3 code/research/verify_kovacec_polygon_tenths.py`: exact planarization
has 316 vertices, 342 face cycles, one simple 14-vertex outer polygon and
strict star-kernel point (32,15). The explicit determinant has an escaping
ray missing all 72 segments (57 behind, 10 to one side, 5 to the other), yet
lies strictly inside the triangle of original matching points 0,1,5.
The star kernel makes ray visibility agree with the outer polygon exterior:
for exterior p, the outward ray p+t(p-k) cannot reenter the polygon, since
that would put p on a segment from kernel point k to a point inside.
The archived example therefore contradicts Conjecture 7's stated qualification
while preserving MOC.

## 7. Reproduction, reading scope, and limits

Run from `/data/MOC`:

```
OPENBLAS_NUM_THREADS=1 python3 code/research/next_probabilistic_rounding.py
python3 code/research/verify_kovacec_polygon_tenths.py
```

The new script writes no artifacts. Its stdout contains all base and repaired
weights, target, terminal densities, exact minimum-TV dual and bound-active
coordinates, allowing an independent replay. NumPy/SciPy only discover the
minimum-TV active basis; SymPy checks every equality/sign thereafter.
The flow and Doob calculations do not trust numerical tolerances.

Substantive complete arguments read: broader positive-law transfer,
pair-rotation optimizer, zero-pair theorem and historical 27-facet proof;
categorical coupling notes, forest/cycle variational notes and tensor
independent audit; structural large-shift all-U, Haar coverage, and discrete
coverage proofs; both independent rank-two/referee notes. Research notes
read completely: unrestricted DPP and martingale; moonshot RMT/fermionic;
joint-row-kernel, coordinate-fiber duality and exact obstruction; Markov
cycle-capacity and Gauss bridge; heat-weight Lean scope; singleton obstruction;
and both Kovačec exact counterexample notes. Corresponding code inspected:
full categorical forest verifier, full rational neighborhood verifier,
full Kovačec tenths verifier, first 190 lines of fermionic code and first
180 lines of unrestricted DPP code. Those last two files were **not** read
in full. Repetitive contact-face tables and saved finite campaigns received
grouped data coverage rather than a full-content reading.

Drury's primary 1992 compound paper was sought at DOI
10.1016/0024-3795(92)90296-M and the publisher PDF endpoint; both returned
403. Author research pages had no accessible copy; a search-proposed
CiteSeer PDF returned 404. Drury's original paper therefore remains unread;
the compound-separation argument above was reconstructed and verified from
the archive. Kovačec's
primary preprint was accessible and read in full. Verification here consists
of the written arguments and exact computations, without Lean formalization
or an exhaustive stochastic search.

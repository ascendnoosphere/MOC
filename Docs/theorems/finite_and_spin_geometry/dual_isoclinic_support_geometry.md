# Isoclinic support geometry and its exact remaining budget

## Scope

This note analyzes the one-parameter orthogonal family
\[
J=\begin{pmatrix}
0&-1&-1&-1\\
1&0&-1&1\\
1&1&0&-1\\
1&-1&1&0
\end{pmatrix},\qquad
U(r)=\frac{rI+J}{\sqrt{r^2+3}},\qquad r\in\mathbb R.
\tag{1}
\]
Since \(J^T=-J\) and \(J^2=-3I\), every \(U(r)\) lies in \(SO(4)\). The limiting profile at \(r=\infty\) is the identity profile.

There are three exact conclusions.

1. Every scalar Temperley--Lieb support deficit on this family is a quartic with four explicit permutation-gap coefficients.
2. The complete squared-minor profile has a common permutation law exactly for \(r=0\) or \(|r|\ge\rho\), where \(\rho^3+3\rho-2=0\).
3. At the spectral boundary where all nine derangements maximize, the M8 secant equations force the whole support functional to be a nonnegative diagonal assignment penalty. This last result holds for every complex unitary, by dual_derangement_secant_rigidity.md.

The intermediate central region remains open for arbitrary actual complex spectral supports. Failure of a common permutation law in that region does not constitute a counterexample to MOC.

## 1. The exact quartic support formula

Let \(c_\pi\) be a real cost in the fourteen-dimensional Temperley--Lieb cost space. For an actual normal-spectral support,
\[
c_\pi=\operatorname{Re}\!\left(\lambda\prod_i(a_i+b_{\pi(i)})\right).
\]
Write \(h=\max_\pi c_\pi\), \(g_\pi=h-c_\pi\ge0\), and define
\[
A=g_{\mathrm{id}},\qquad
T=\sum_{\text{six transpositions}}g_\pi,\qquad
D=\sum_{\text{nine derangements}}g_\pi.
\tag{2}
\]
For each three-cycle, put
\[
\epsilon_\pi=\operatorname{sgn}(\pi)
 \prod_{\{i:\pi(i)\ne i\}}J_{i,\pi(i)}\in\{1,-1\},
\]
and define
\[
K=\sum_{\text{eight three-cycles}}\epsilon_\pi c_\pi.
\tag{3}
\]
There are four signs of each kind, so
\(K=-\sum\epsilon_\pi g_\pi\).

The normalized Leibniz coefficients for \(U(r)\) are:

| Permutation class | Count | Numerator per permutation |
|---|---:|---:|
| Identity | 1 | \(r^4\) |
| Transposition | 6 | \(r^2\) |
| Three-cycle of positive orientation | 4 | \(r\) |
| Three-cycle of negative orientation | 4 | \(-r\) |
| Derangement | 9 | \(1\) |

Their sum is \((r^2+3)^2\). Expansion of the determinant therefore gives
\[
\boxed{
h-c(U(r))
=\frac{Ar^4+Tr^2-Kr+D}{(r^2+3)^2}.
}
\tag{4}
\]
The identity extends by linearity from rank-two product costs to the full Temperley--Lieb cost space. The exact verifier additionally checks it on all seventy squared-minor coordinates, so it does not rely only on selected scalar examples.

This explains the relevant “start and ends” obstruction precisely. The center sees \(D\), the identity limit sees \(A\), and the odd coherence term \(Kr\) can make the interior negative even when both ends are safe.

## 2. Relations forced before using the spectral secant condition

The costs satisfy an exact relation on every three-label triangle. For its two oriented three-cycles and its three transpositions,
\[
g_{\tau_+}+g_{\tau_-}
=g_{(ij)}+g_{(jk)}+g_{(ik)}-g_{\mathrm{id}}.
\tag{5}
\]
It is the vanishing determinant of the corresponding \(3\times3\) rank-two submatrix, extended linearly to all Temperley--Lieb costs.

Summing over the four triangles yields
\[
\sum_{\text{eight three-cycles}}g_\pi=2T-4A.
\]
Hence
\[
\boxed{T\ge2A,\qquad |K|\le2T-4A.}
\tag{6}
\]

The full alternating relation gives
\[
A-T+\sum_{\text{three-cycles}}g_\pi
+\sum_{\text{double transpositions}}g_\pi
-\sum_{\text{four-cycles}}g_\pi=0.
\]
Consequently,
\[
\boxed{
D=T-3A+2\sum_{\text{three double transpositions}}g_\pi
\ge T-3A.
}
\tag{7}
\]
The exact verifier checks all four triangle relations and the full alternating relation directly in the fourteen-dimensional cost coordinates.

Several regimes are already safe without any spectral restriction.

- If \(A=0\), then \(D\ge T\) and \(|K|\le2T\), so \(K^2\le4TD\).
- More generally, \(D\ge T\) implies the same quadratic budget.
- If \(T=0\), then \(A=0\) and \(K=0\).
- Writing \(T=2A+B\), \(B\ge0\), equations (6)--(7) imply
  \[
  Ar^4+Tr^2-Kr+D
  \ge A(r^4+2r^2-1)+B(|r|-1)^2.
  \tag{8}
  \]
  Thus every such cost is safe for
  \(|r|\ge\sqrt{\sqrt2-1}\).

Section 4 sharpens the last interval to the exact common-law threshold by using the whole permutation profile.

## 3. Exact scalar SOS criterion

For arbitrary \(A,T,D\ge0\), not necessarily arising from spectra, consider
\[
P(r)=Ar^4+Tr^2-Kr+D.
\]
When \(A>0\) and \((T,D)\ne(0,0)\), let
\[
z=\frac{\sqrt{T^2+12AD}-T}{6A}\ge0,
\qquad H=T+2Az.
\tag{9}
\]
Equivalently \(D=3Az^2+Tz\). If \(D>0\), the cancellation-free expression is
\[
z=\frac{2D}{T+\sqrt{T^2+12AD}}.
\]
The exact criterion is
\[
\boxed{
P(r)\ge0\ \text{for all real }r
\quad\Longleftrightarrow\quad
K^2\le4z(T+2Az)^2.
}
\tag{10}
\]

For necessity, minimize \(Ar^3+Tr+D/r\) over \(r>0\). Its unique minimum, when \(D>0\), occurs at \(r^2=z\) and equals \(2\sqrt z(T+2Az)\). The inequality for both signs of \(r\) is exactly the bound on \(|K|\).

For sufficiency, use the identity
\[
\begin{aligned}
P(r)={}&A(r^2-z)^2
+H\left(r-\frac{K}{2H}\right)^2\\
&+zH-\frac{K^2}{4H}.
\end{aligned}
\tag{11}
\]
The last term is nonnegative exactly under (10). The verifier checks this as a polynomial identity after multiplying by \(4H\).

The degenerate cases are explicit.

- If \(A=0\), \(T>0\), the criterion is \(K^2\le4TD\).
- If \(A=T=0\), the criterion is \(K=0\).
- If \(D=0\), any nonzero \(K\) causes a negative value near zero; thus \(K=0\) is necessary and sufficient.
- If \(A>0\), \(T=D=0\), this is the preceding \(D=0\) case.

One may also state (10) as the existence of the \(3\times3\) Gram matrix
\[
\begin{pmatrix}
A&0&\eta\\
0&T-2\eta&-K/2\\
\eta&-K/2&D
\end{pmatrix}\succeq0.
\tag{12}
\]
The choice \(\eta=-Az\) realizes the exact threshold. For \(A>0\), its squared critical value is
\[
K_{\mathrm{crit}}^2
=\frac{2}{27A}
\left[(T^2+12AD)^{3/2}-T^3+36ATD\right].
\tag{13}
\]

The simpler condition \(K^2\le4TD\) is sufficient because it discards the nonnegative quartic term \(Ar^4\). It is stronger than the exact criterion when \(A,D>0\). It remains unproved for all actual spectral costs.

## 4. Exact common-law threshold from an \(A_4\) quotient

A common permutation law means nonnegative numbers \(p_\pi\) with \(\sum p_\pi=1\) such that simultaneously for every pair of equal-size subsets \(I,J\),
\[
|\det U[I,J]|^2
=\sum_\pi p_\pi\,1_{\{\pi(I)=J\}}.
\tag{14}
\]
It controls every Temperley--Lieb cost at once.

The full profile of \(U(r)\) is invariant under conjugation by the alternating group \(A_4\). One direct proof uses the signed Leibniz representation in Section 1: its coefficient is unchanged by every even conjugation. This is checked for the complete profile in code/theorems/finite_and_spin_geometry/dual_isoclinic_support_exact.py.

If a common law exists, averaging it under \(A_4\) gives another common law constant on the six conjugacy classes below. Their averaged full profiles span an affine three-dimensional space. In exact affine coordinates \((x,y,w)\), the six vertices are:

| \(A_4\)-conjugacy class in \(S_4\) | Size | \(x\) | \(y\) | \(w\) |
|---|---:|---:|---:|---:|
| Identity | 1 | \(1\) | \(1\) | \(0\) |
| Transpositions | 6 | \(1/3\) | \(0\) | \(0\) |
| Double transpositions | 3 | \(-1/3\) | \(1\) | \(0\) |
| Four-cycles | 6 | \(-1/3\) | \(0\) | \(0\) |
| Positive three-cycles | 4 | \(0\) | \(-1/2\) | \(1/2\) |
| Negative three-cycles | 4 | \(0\) | \(-1/2\) | \(-1/2\) |

These coordinates can be obtained from the \((3,1)\) and \((2,2)\) representation blocks. No representation-theoretic assumption is needed for verification: the script checks that the six seventy-coordinate class profiles have linear rank four and exactly the same linear relations as the four rows \((1,x,y,w)\) in the table.

The transposition point is the average of the identity and the two three-cycle points. The other five points have exactly six facets:
\[
\begin{array}{rlrl}
y+3w&\le1,&y-3w&\le1,\\
3x-2y&\le1,&-3x-2y&\le1,\\
-3x+2w&\le1,&-3x-2w&\le1.
\end{array}
\tag{15}
\]
Every facet is verified by exact enumeration of all triples of the five vertices.

For the isoclinic family,
\[
x=\frac{r^2-1}{r^2+3},\qquad
y=\frac{r^4+3}{(r^2+3)^2},\qquad
w=\frac{4r}{(r^2+3)^2}.
\tag{16}
\]
Multiplying each facet slack by \((r^2+3)^2\) gives
\[
\begin{aligned}
1-y\mp3w&:\quad 6(r\mp1)^2,\\
1-3x+2y&:\quad24,\\
1+3x+2y&:\quad6(r^2+1)^2,\\
1+3x\mp2w&:\quad4(r^4+3r^2\mp2r).
\end{aligned}
\tag{17}
\]
Only the last pair can be negative. Therefore
\[
\boxed{
U(r)\text{ admits a common permutation law}
\iff
r=0\quad\text{or}\quad |r|\ge\rho,
}
\tag{18}
\]
where
\[
\rho^3+3\rho-2=0,\qquad
\rho=2\sinh\!\left(\frac13\operatorname{arsinh}1\right)
\approx0.5961.
\]
The cubic is strictly increasing, so its positive root is unique. The profile at \(r=\infty\) is included by continuity.

For \(0<r<\rho\), exactly the facet \(-3x+2w\le1\) fails; for \(-\rho<r<0\), exactly its opposite-orientation partner fails. This is an exact localization of the common-law obstruction, not a spectral counterexample.

The root independently obtained the same threshold by restricting the complete common-minor facet catalog to this curve. The present six-class proof is self-contained and does not use that catalog.

## 5. The nonspectral obstruction and its spectral exclusion

On the five-dimensional derangement-zero face from dual_derangement_secant_rigidity.md, take
\[
(a,b,c,d,e)=(1,0,1,0,1).
\]
All twenty-four permutation deficits are nonnegative, but
\[
A=2,\qquad T=6,\qquad D=0,\qquad K=4.
\]
Thus
\[
P(r)=2r^4+6r^2-4r
=2r(r^3+3r-2)<0
\quad(0<r<\rho).
\tag{19}
\]
This is a genuine common-law separating cost. Its restricted cubic data are \(F=Q=1\), and its unique constant lift onto the cubic has Hessian determinant \(-4\). Therefore it cannot be an actual complex spectral support cost, a sum of two real product costs, or any other point in the projected complex secant closure.

The complete face theorem is stronger than exclusion of this one normal. If an actual spectral cost has \(D=0\), every derangement has zero deficit. The theorem forces
\[
g_\pi=\sum_iw_i1_{\{\pi(i)=i\}},\qquad w_i\ge0,
\]
with at most two nonzero weights. Hence
\[
T=3A,\qquad K=0,\qquad
h-c(U(r))=\frac{Ar^2}{r^2+3}\ge0.
\tag{20}
\]
Indeed, the same cost is safe for every complex unitary by its diagonal penalty formula.

Thus the dangerous generic \(D=0\) end of the central interval is completely controlled by the actual spectral secant condition.

## 6. The precise remaining problem

Combining the results, a hypothetical violation on this family must have
\[
0<|r|<\rho,\qquad A>0,\qquad 0<D<T.
\tag{21}
\]
The exact remaining inequality is (10), with \(A,T,D,K\) coming from actual normal-spectral costs. Proving the stronger budget
\[
K^2\le4TD
\tag{22}
\]
would also suffice on this entire isoclinic family, but would still not by itself prove unrestricted MOC for arbitrary unitary matrices.

The face classification proves the correct boundary behavior at \(D=0\). It does not give a quantitative rate of approach that controls \(K^2/D\) throughout \(D>0\). A continuation proof needs that extra rate or another algebraic inequality; it cannot simply interpolate the endpoint values.

There is an exact spectral saturation example in the CH chart:
\[
\beta=(0,0,-1,4),\qquad
\lambda_0=1,\qquad\lambda_1=0.
\]
Its cost is
\[
c_\pi=\beta_{\pi(1)}(1+\beta_{\pi(2)})\beta_{\pi(4)},
\]
and the exact coefficients are
\[
h=0,\quad A=0,\quad T=D=4,\quad K=8.
\]
Thus \(K^2=4TD\) and \(P(r)=4(r-1)^2\). The candidate quadratic budget, if valid, cannot have a uniformly smaller constant.

## 8. Verification and attribution

code/theorems/finite_and_spin_geometry/dual_isoclinic_support_exact.py verifies with rational arithmetic:

- \(J^2=-3I\), every normalized signed Leibniz coefficient, and all seventy squared-minor profile identities;
- \(A_4\) invariance, the six class averages, their affine coordinate map, and all six quotient facets;
- every facet-slack polynomial on the curve;
- the four triangle relations and the total alternating relation;
- the quartic SOS identity and the exact spectral saturation example.

A registry abstract for a report by Sidney Holden dated September 13, 2026 claims a related forty-eight-region analysis and sharp \(SO(4)\) common-minor bound. Only the abstract overlap was checked. We therefore make no priority claim and do not use unread lemmas from that report. The arguments and verifiers in this note were derived and checked within the present campaign.


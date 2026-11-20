# Unrestricted coupled-spin calibration and higher jets

31 October 2026. The source coefficients throughout are the six complex
coordinates in `moc_global_bell_pair_quadratic_20261031.txt`. The universal
support inequality has not been proved in this lane.

## Exact bridge to the inverse pencil

Write the real exposed objective, with its constant suppressed, as

\[
 f(R,S)=\sum_{ij}\alpha_{ij}(R_{ij}^2+S_{ij}^2)
                       +\beta_{ij}R_{ij}S_{ij}.
\]

Let

\[
 K=\begin{pmatrix}0&-1&1\\1&0&-1\\-1&1&0\end{pmatrix}.
\]

For the matching support cost `g=h-f`, the global cofactor normal form of
the universal inverse pencil is exactly

\[
 M(g)=\operatorname{matrix\_from\_form}
        \left(-\frac{\beta}{4},-\frac{K\alpha K^T}{4}\right).
 \tag{1}
\]

Here `matrix_from_form(A,B)` represents
`<A,cof H>+sum B_ij H_ij^2`. Formula (1) is valid for all eighteen free
real coefficients, before imposing physical source coupling. Row and
column potentials in `alpha` contribute constants and disappear under
`K alpha K^T`.

To check the constants directly, a signed-assignment matrix `O` has
vertex gap `h-2<alpha,O entrywise_squared>-<beta,O>`. The cofactor normal
form evaluates a matching function as

\[
 c+4\langle A,O\rangle+
       \frac89\langle K^T B K,O\mathbin\circ O\rangle.
\]

Substitute (1), use `K^T K=3(I-11^T/3)`, and discard row and column
potentials. The replay checks the full inverse-pencil equality on every
one of the eighteen coordinate directions and all twenty-four
permutations. For an actual source the already proved complex-rank-four
factorization therefore applies to this explicit spin pencil. No
arbitrary-coefficient neutrality assertion is substituted for the source.

## The ordinary outer relaxation fails on the designated hard source

For physical rotations set

\[
 Q=(R\mathbin\circ R+S\mathbin\circ S)/2,
 \qquad T=R\mathbin\circ S.
\]

Then `Q` is doubly stochastic, `-Q<=T<=Q` entrywise, and `T` belongs to
the convex hull of the twenty-four tetrahedral signed permutations. The
last statement follows from the singleton squared-entry matrix of the
associated real `SO(4)` matrix and ordinary Birkhoff decomposition.

These constraints define a useful small LP, but they discard precisely
the additional minor compatibility that the proof needs. They are
insufficient even with actual source coefficients. An exact witness is
the previously established source

```
a=(0,100,-214+146i,269-294i)
b=(-207-148i,-28-84i,-59+82i,83+104i), eta=-25+i.
```

Let `O_pi=L^T P_pi L` and let

```
w=(-1,2,1,-1,-1,0,1,-1,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0)/3.
```

The matrices

\[
 Q_* =\sum_\pi w_\pi(O_\pi\mathbin\circ O_\pi),\qquad
 T_* =\sum_\pi w_\pi O_\pi
\]

satisfy every constraint of this LP. In particular
`sum w_pi P_pi` is an entrywise nonnegative doubly stochastic matrix,
so `T_*` has the required convex-hull membership despite some negative
`w_pi`. Nevertheless their exact exposed excess is

\[
 \frac{42246975256}{3}>0.
\]

This is an outer-relaxation counterexample, not a physical mixer or a MOC
counterexample. The exact source has a known weighted-minor proof.
All six critical-centroid normalizations of this same source also defeat
the LP numerically, with normalized excess between `0.007163` and
`0.020076`. Thus choosing another traceless normalization does not repair
the relaxation. A preceding 5,000-source generic pass missed this known
adversary and has no universal significance.

## A global quartic formula for coupled flat directions

Let `A,B` be arbitrary complex four-by-four matrices. Let `J_1,J_2,J_3`
be a real isoclinic quaternion basis, and put

\[
 K(v)=\sum_i v_iJ_i,\qquad r=\sum_i v_i^2,
 \qquad W=cI+sK(v),\qquad c^2+rs^2=1.
\]

Then `W` is in `SO(4)` and the determinant is an exact homogeneous
quartic in the circle coordinates:

\[
 \det(A+WBW^T)
  =\det\big(c(A+B)+s(AK+KB)\big).                 \tag{2}
\]

Indeed `W W^T=(c^2+rs^2)I`, `det W=(c^2+rs^2)^2`, and

\[
 [c(A+B)+s(AK+KB)]W^T=(c^2+rs^2)A+WBW^T.
\]

The checker verifies the last matrix identity with all thirty-two entries
of `A,B` free, as well as the quaternion relations with all three `v_i`
free. Formula (2) has no inverse and remains valid at singular sums and
repeated source spectra.

If the support restriction is

\[
 F(c,s)=a c^4+b c^3s+d_2c^2s^2+d_3cs^3+d_4s^4,
\]

stationarity at `(1,0)` gives `b=0`, and zero Hessian in this direction
gives `d_2=2ra`. Consequently the entire circle obeys

\[
 F(c,s)-a=d_3cs^3+(d_4-r^2a)s^4.                 \tag{3}
\]

Thus a nonzero cubic coefficient is a finite ascending move, and a genuine
maximum with zero cubic must satisfy `d_4<=r^2a`. A negative semidefinite
Hessian alone misses this condition.

For the exact Walsh example from `moc_pair_maximum_moonshot.txt`, the
whole three-dimensional physical real Hessian kernel, rather than only
three separately flat axes, has the identity

\[
 F((cI+sK(v))U)=24+384cs^3v_1v_2v_3.
 \tag{4}
\]

Its null cubic is `2304 v_1 v_2 v_3`. The zero set is the union of three
planes. This makes explicit why testing a basis of null directions is
insufficient: the entire cubic tensor on the kernel must vanish at a
maximum. Formula (4) is audited with all three `v_i` symbolic.

## The mixed fourth-order condition

This condition applies to the original smooth supported determinant on
the full physical unitary flag, in exponential coordinates. Let `H,T,Q`
be its second, third and fourth derivative tensors at a stationary point.
Suppose `H` is negative semidefinite and let `N=ker H`.

At a genuine local maximum,

\[
 T|_{N^3}=0.                                            \tag{5}
\]

The diagonal assertion follows from the third-order Taylor expansion;
polarization gives the full assertion. For `v in N`, define
`b_v(w)=T(v,v,w)`. Equation (5) says that `b_v` annihilates `N`. Along
the curve `x(t)=t v+t^2 w/2`, the fourth-order term is

\[
 \frac{t^4}{24}
       \{Q(v,v,v,v)+6b_v(w)+3H(w,w)\}.
\]

Maximizing this expression over accelerations in the range of `H` gives
the exact necessary inequality

\[
 Q(v,v,v,v)-3b_v^T H^\dagger b_v\ \leq\ 0
       \qquad(v\in N).                                \tag{6}
\]

The sign matters: `H^dagger` is negative semidefinite, so allowing coupled
acceleration adds a nonnegative term to the raw fourth derivative. A
negative raw fourth derivative does not settle local maximality. Formula
(6) follows by completing the square with
`w=-H^dagger b_v`; the replay audits its numerical constants symbolically.

For a hypothetical violation, compactness supplies a global maximum with
support strictly above all twenty-four products. It must satisfy the
source-coupled stationarity equations, the full negative semidefinite
Hessian, (5), and (6). The Walsh control is excluded by (5). No implication
from the actual six-complex source formulas and the strict above-hull
premise to a violation of (5) or (6) has been established here. In
particular these necessary conditions are not declared sufficient.

Replays:

```
python3 code/research/moc_unrestricted_spin_calibration.py
python3 code/research/moc_unrestricted_spin_higher_jet.py
python3 code/research/moc_unrestricted_spin_visualize.py
```

Reports are `build/moc_unrestricted_20261031/spin/calibration.json` and
`higher_jet.json`. The earlier fixed-mixer stationarity inversion accepted
308 source-coupled critical points in the 20-by-20 run; every accepted point
had a positive real-spin Hessian eigenvalue. This numerical observation
does not replace any of the higher-order or global sign arguments above.

The standalone figure `build/moc_unrestricted_20261031/spin/higher_jet.png`
(also SVG) shows the full null cubic and the exact finite ascent curve.

## Chirality success has an exact, harmless zero locus

Use the full-source kernel from
`moc_unrestricted_fierz_chirality56.py`, with its 280 amplitudes

\[
 h_{I,J,e}=[i_1i_2][i_2i_3][i_3i_1]
           [j_1j_2][j_2j_3][j_3j_1][e_1e_2]^2.
\]

For eight nonzero spinors, **all these amplitudes vanish if and only if
some projective spinor label occurs at least four times**.

The reverse implication is immediate: the two rainbow triples and the
distinct-color edge in a nonzero channel can use any projective point at
most three times. For the forward implication suppose every multiplicity
is at most three. There are at most two colors of multiplicity three.
Choose a distinct-color edge containing one vertex of each such color;
if there is only one, choose its other endpoint from another color. If
there are none, choose any distinct-color edge. Every remaining color
then occurs at most twice among six labels. Put the two copies of every
repeated color in different triples and fill the remaining slots with the
distinct singleton colors. Both triples are rainbow, and the selected
amplitude is nonzero. This construction works on the projective line,
including a label at infinity; only bracket nonvanishing is used.

The entire zero locus has a direct positive permutation law. Suppose
exactly four labels equal a projective point `zeta`, with `r` in the row
group. After row and column reorderings, place the row cluster first and
the **noncluster** columns first. The bracket-masked matrix is block
triangular. With the scalar factors of the coincident spinors included
in `p0`, one has polynomially for every matrix `U`

\[
 \det([u_i,v_j]U_{ij})=p_0\det U_{11}\det U_{22}.
\]

For a unitary, complementary minors give

\[
 d=p_0|\det U_{11}|^2.
\]

The permutation products are `0` or `p0`; for `r=0,4` all equal `p0` and
the coefficient is one. If five or more labels coincide, every matching
has a zero bracket and both the determinant and all products vanish.
The symbolic audit checks all five splits `r=0,...,4`, all sixteen free
mixer entries, arbitrary remaining homogeneous spinors, and all twenty-four
products. This boundary statement needs no support maximality or balance.

Consequently any basis `b56` of the full chirality space has
`||b56(x)||^2>0` at every remaining source. A certificate can normalize its
success effect to dominate this kernel and handle its zeros by the
explicit minor formula above.

## One positive angular matrix contains the coupled cubic and quartic

For either isoclinic family in (2), expand the supported quartic as

\[
 f(c,sv)=a c^4+b(v)c^3s+d_2(v)c^2s^2+d_3(v)cs^3+d_4(v)s^4,
\]

where `d_k` is homogeneous of degree `k` in the three real coordinates
`v`, and `r=|v|^2`. At a stationary point the exposed `b(v)` vanishes.
The exact defect is

\[
 a-f(c,sv)=s^2(c,s)
 \begin{pmatrix}
 2ar-d_2(v)&-d_3(v)/2\\
 -d_3(v)/2&ar^2-d_4(v)
 \end{pmatrix}
 \binom c s,
 \qquad c^2+rs^2=1.                              \tag{7}
\]

Thus at a true global maximum the displayed homogeneous two-by-two matrix
`H(v)` is PSD for every real `v`. This includes the full finite isoclinic
circle, rather than only its Hessian.

Associate six channels in its first row with the quadratic monomials
`v1^2,v1 v2,v1 v3,v2^2,v2 v3,v3^2`, and three channels in its second row
with `v1,v2,v3`. For channel `alpha` write its row and monomial as
`r_alpha,m_alpha`. Define the real symmetric nine-by-nine matrix

\[
 L_{\alpha\beta}=
 \int_{S^2}m_\alpha(v)m_\beta(v)
      H_{r_\alpha r_\beta}(v)\,\frac{d\Omega}{4\pi}.
 \tag{8}
\]

For any real channel vector, its quadratic form is an integral of a
quadratic form of `H(v)`, so `L` is PSD at a global maximum. Every
integrand has degree six. The complete coefficients are therefore
rational combinations of `1/7,1/35,1/105`. In particular `L` is **linear
in the full fourteen source coordinates**. Both isoclinic families give
such a matrix.

The choice of channel degrees matters. A constant first-row channel and
linear second-row channels would erase the Walsh harmonic cubic under
angular averaging. With (8), the exact Walsh source instead gives

\[
 \operatorname{spec}L=
 \{(-64/35)^3,\ 0^3,\ (64/35)^3\}.
\]

Its only nonzero entries, in the listed channel order, are symmetric
off-diagonal pairs `(1,8),(2,7),(4,6)`, all equal to `-64/35` with
zero-based indices. This excludes the Hessian trap by a single positive
matrix test that retains the coupled cubic. The replay exports both
`81 by 14` coefficient matrices for Q59 and checks the quartic source
formula against exact determinant evaluations at rational quaternions
on the known nonordinary source.

## A joint positive support-defect cone

Let `s_ij=p_ij d+d(tau_ij x)` be the cross-transposition section from the
CS-disk identity, and let `g_a=D_a d` be the six real-spin mixer gradient
sections. All these are full linear source sections. For a fixed real
mixer, seek constant real matrices in the exact complex source-ring
identity

\[
 \sum_\pi(d-p_\pi)\,b^*E_\pi b
 +\sum_{ij}s_{ij}\,b^*C_{ij}b
 +\sum_{\varepsilon=\pm}\sum_{\alpha\beta}
       L^\varepsilon_{\alpha\beta}\,b^*G^\varepsilon_{\alpha\beta}b
 +\sum_a g_a\,b^*D_a b=0.                         \tag{9}
\]

Here `b=b56`, every `E_pi,C_ij` is PSD, each `D_a` is unrestricted real
symmetric, and each complete block matrix `G^epsilon` on `R9 tensor R56`
is PSD. Its off-diagonal `56 by 56` blocks are retained. Require

\[
 \sum_\pi E_\pi\succeq I_{56}.                    \tag{10}
\]

This is a concrete sufficient positive-defect identity. At a hypothetical
support maximum strictly above all twenty-four products, the first sum
has strictly positive real part whenever `b!=0`. The exposed CS sections
are nonnegative, both exposed matrices `L^epsilon` are PSD, and the
gradient terms have zero real part. Contracting either PSD `G^epsilon`
against the actual feature vector `b` gives a PSD nine-by-nine matrix,
so its pairing with the exposed `L^epsilon` is nonnegative. Equation
(9) is impossible. The case `b=0` is already covered by the exact positive
minor formula. Uniform effects satisfying (9)--(10) for every real mixer
would therefore prove the entire unrestricted four-dimensional inequality
through the audited realification theorem.

The code implements the whole coefficient problem on `R3 tensor conjugate
R2`, using the full degree-three source ring of dimension364. It does not
fit a finite source sample. The success inequality uses a PSD slack, not
only a trace normalization. The scalar CS version was tested for Q59:
after200 initial and1000 continued steps its coefficient residual was
`0.00149877`; success minimum eigenvalue was `0.999419`. Adding the two
PSD504 blocks for (8) and taking80 seeded steps gave residual
`0.00148602`. These are unresolved numerical cone solves, not certificates
or separating duals. No uniform effect construction has been obtained.

Additional replays:

```
python3 code/research/moc_unrestricted_spin_chiral_calibration.py --mixer Walsh
python3 code/research/moc_unrestricted_spin_chiral_calibration.py --mixer Q59
python3 code/research/moc_unrestricted_spin_jet9.py --mixer Q59
```

The exact reports are `spin/chiral_calibration_Walsh_exact.json`,
`spin/chiral_calibration_Q59_exact.json`, and `spin/jet9_Q59.json`. The
numerical effects and complete operator arrays are retained in
`spin/chiral_calibration_Q59.npz` and
`spin/chiral_calibration_Q59_jet9.npz`.

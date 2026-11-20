## Round 021 — The two-dimensional compression law is exactly a Bell-locality problem

**Status: proved equivalence, including both directions. The resulting
arbitrary-outcome locality assertion remains open in this investigation.**

Let X=[x_1,...,x_m] and Y=[y_1,...,y_n] be complex two-row coisometries:
XX*=YY*=I_2. Set

\[
q^X_{ik}=|\det[x_i,x_k]|^2,\qquad
q^Y_{jl}=|\det[y_j,y_l]|^2,\qquad
F_{ij}=|\det[x_i,y_j]|^2.
\]

A common matching law is a probability distribution on size-two matchings
of K_{m,n}. Its selected left and right pairs must have marginals q^X and
q^Y, and its expected edge-incidence matrix must be F. As established by
Cauchy–Binet, such a law gives the desired spectrum-independent convex
formula for det(XD_aX*+YD_bY*).

Consider the singlet

\[
|\psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2
\]

and two rank-one qubit POVMs E_i=x_i x_i*, G_j=y_j y_j*. Both parties may
choose E or G. Direct evaluation, with no appeal to a Bell theorem, gives

\[
\begin{aligned}
P(i,k\mid E,E)&=q^X_{ik}/2,\\
P(j,l\mid G,G)&=q^Y_{jl}/2,\\
P(i,j\mid E,G)&=F_{ij}/2,\\
P(j,i\mid G,E)&=F_{ij}/2.
\end{aligned}
\]

The equal-outcome same-setting probabilities are zero. Here q is extended
symmetrically to ordered distinct indices.

Given a matching {(i,j),(k,l)}, choose either ordering of its two edges with
probability one half. Define deterministic outputs

\[
(A_E,B_E,A_G,B_G)=(i,k,l,j)
\]

for the displayed ordering. The swapped ordering exchanges the parties.
The two same-setting pair laws are q^X and q^Y, and the two ordered mixed
laws are F/2. Thus the matching law produces a local hidden-variable model.

Conversely, any finite-outcome local behavior has a distribution on
deterministic four-tuples (A_E,B_E,A_G,B_G). The observed same-setting
zeros imply A_E != B_E and A_G != B_G almost surely. Associate the matching

\[
\{(A_E,B_G),(B_E,A_G)\}.
\]

Its left-pair marginal is q^X, its right-pair marginal is q^Y, and its edge
expectation is the sum of the two mixed-setting distributions, namely F.
This proves equivalence.

It follows that the proved (3,3) and (2,n) compression laws are also exact
locality theorems for these identical-setting singlet experiments. A
counterexample to the arbitrary-parent common law would give a Bell
inequality violated by two POVMs used identically on both parties. This is
stronger than ordinary Bell scenarios allowing four independently chosen
measurements.

## Round 022 — The first open case is a fractional edge-coloring inequality

**Status: proved exact reduction and dual criterion; universal validity of
that criterion is not established.**

Suppose X has three columns and Y has n columns. A matching selects exactly
two of the three left vertices. Therefore its left-pair probabilities are
forced by its left degrees: the probability of selecting {i,k}, with
remaining index r, is

\[
1-\sum_jF_{rj}=1-\|x_r\|^2=q^X_{ik}.
\]

The final equality follows from a two-row coisometry's complementary
minor identity in three columns. Consequently the q^X constraints may be
deleted entirely.

Start with the complete graph on the n right vertices, with edge {j,l}
of mass q^Y_{jl}. Distribute each edge's mass among assignments of two
different colors i,k in {1,2,3} to its endpoints j,l. The required total
mass of color i at vertex j is F_{ij}. This colored-edge allocation is
equivalent to the common law.

There are 6 C(n,2) nonnegative variables w_{ik;jl}, i != k, j<l. The
constraints are

\[
\sum_{i\ne k}w_{ik;jl}=q^Y_{jl},\qquad
\sum_{\substack{\text{edge incident at }j\\
                 \text{color at }j=i}}w=F_{ij}.
\]

Eliminating the edge-price variables from the finite linear-programming
dual gives a particularly small exact target:

\[
\boxed{
\sum_{ij}c_{ij}F_{ij}\ \ge\
\sum_{j<l}q^Y_{jl}
\min_{i\ne k}(c_{ij}+c_{kl})
\quad\text{for every real matrix }c.
}
\]

Necessity follows by evaluating every allocated edge. Sufficiency follows
from separating F from the Minkowski sum of the edge-allocation simplices;
equivalently it is finite LP duality.

For n=4 this turns the first open compression case into a small,
fully explicit family of inequalities on a three-by-four cost matrix.
The real difficulty is that the different edge colors must coexist
globally; checking each color separately only yields necessary cut
conditions.

## Round 023 — The event-space dimension and all its linear dependencies

**Status: proved rank formula for the common-law marginal map.**

For m,n >= 2, place q^X, q^Y and F in one vector, without imposing
normalization. The number of coordinates is

\[
N={m\choose2}+{n\choose2}+mn.
\]

Every matching vector satisfies the m+n degree identities

\[
\sum_jF_{ij}=\sum_{k\ne i}q^X_{ik},
\qquad
\sum_iF_{ij}=\sum_{l\ne j}q^Y_{jl}.
\]

These identities are linearly independent. A linear combination with
coefficients alpha_i,beta_j has F coefficient alpha_i+beta_j. If these
vanish, alpha is constant and beta its negative; the pure-pair
coefficients then force that constant to be zero.

There are no additional linear dependencies. Indeed, suppose costs
u_{ik},v_{jl},c_{ij} evaluate to zero on every matching. Comparing the two
matchings on {i,k} x {j,l} gives

\[
c_{ij}+c_{kl}-c_{il}-c_{kj}=0.
\]

Hence c_{ij}=alpha_i+beta_j. The remaining equation says

\[
u_{ik}+alpha_i+alpha_k+
v_{jl}+beta_j+beta_l=0.
\]

The first bracket must be a common scalar t and the second -t. Absorbing
t/2 into the additive gauge of alpha,beta expresses the functional as a
combination of the degree identities.

Thus the marginal matrix has rank

\[
\boxed{
{m\choose2}+{n\choose2}+mn-m-n.
}
\]

Its probability slice has affine dimension one less. In particular,
(3,4) has rank fourteen and affine dimension thirteen. This removes
redundant constraints from both constructive flow and separating-witness
searches. The numerical coincidence with the fourteen-dimensional
n=4 qubit permutation quotient does not itself identify the two bodies.

## Round 024 — Three-outcome qubit POVMs can always be made real

**Status: proved geometric simplification of the (3,n) problem.**

Write each nonzero rank-one effect as

\[
E_i={w_i\over2}(I+\mathbf n_i\cdot\boldsymbol\sigma),
\qquad w_i>0,\quad |\mathbf n_i|=1.
\]

Completeness says sum w_i=2 and sum w_i n_i=0. For three effects, the
three Bloch vectors are linearly dependent, and therefore lie in a
plane through the origin. A spatial rotation sends that plane to the
xz-plane. Its SU(2) lift conjugates all effects to real symmetric
matrices. Choosing a real vector in each effect's one-dimensional range
and adjusting each column phase makes the entire two-by-three
coisometry real.

This transformation does not change any q^X, q^Y or F if both frames are
rotated together; independent column phases are also harmless. Thus the
(3,4) problem may be attacked with X real and only Y carrying complex
geometry.

This does not make both frames real. Four generic Bloch vectors span all
of R^3, and their imaginary direction cannot be removed by the remaining
coordinate freedom. The reduction identifies precisely which side of
the first open case can be flattened.

## Round 027 — Identical binary coarse-graining preserves locality

**Status: proved limitation on possible separating witnesses.**

Any two-outcome qubit POVM is a classical postprocessing of a projective
measurement in the eigenbasis of its first effect. Indeed, if
E=lambda_+ P_+ + lambda_- P_- with 0 <= lambda_± <= 1, measure
{P_+,P_-} and output the first outcome with conditional probability
lambda_±.

For two projective directions used identically by both parties on the
singlet, an explicit local model exists. Let unbiased binary variables
Z_0,Z_1 have correlation

\[
\mathbb E Z_0Z_1=\mathbf n_0\cdot\mathbf n_1.
\]

For example choose Z_0 uniformly and choose Z_1=Z_0 with probability
(1+n_0 dot n_1)/2. Alice outputs Z_x and Bob outputs -Z_y. Their
correlations are exactly -n_x dot n_y, and all marginals are unbiased.
Independent local postprocessing gives the desired pair of binary POVMs.

Therefore applying the same binary binning on both parties to each of
the two arbitrary multi-outcome POVMs in Round 021 yields a local
behavior. CHSH after such identical binning cannot expose a failure.

The same-binning restriction is essential. Different binnings at the
two parties are still legitimate postprocessings of the original Bell
experiment, but create four different effective binary observables.
The argument above does not establish their locality or rule out a
CHSH certificate constructed with those different binnings.

## Round 028 — A single internal phase has an exact common-minor convex law

**Status: proved all-dimension reduction to two real orthogonal endpoints.**

Let O_1,O_2 be real orthogonal matrices and

\[
U(\phi)=O_1\operatorname{diag}(e^{i\phi},1,\ldots,1)O_2.
\]

For any equal-size row and column sets I,J, Cauchy–Binet shows

\[
\det U(\phi)_{I,J}=A_{I,J}+e^{i\phi}B_{I,J},
\qquad A_{I,J},B_{I,J}\in\mathbb R.
\]

Only subsets containing the distinguished internal coordinate acquire
the phase. Therefore

\[
|\det U(\phi)_{I,J}|^2
=A^2+B^2+2AB\cos\phi.
\]

Writing theta=(1+cos phi)/2 gives the simultaneous identity

\[
\boxed{
|\det U(\phi)_{I,J}|^2
=\theta|\det U(0)_{I,J}|^2
 +(1-\theta)|\det U(\pi)_{I,J}|^2
}
\]

for every grade and every I,J, with one common theta. Hence any
spectrum-independent common law at the two real endpoints transfers
immediately to the complex one-phase family. Even without such an
operator law, MOC for the two endpoints at specified spectra transfers,
because the determinant expansion is linear in the squared minors.

The endpoint hypothesis matters: MOC for arbitrary real orthogonal
matrices in arbitrary dimension was not established by this derivation.
The theorem enlarges every proved real class by a concrete complex
one-phase operation.

## Round 029 — Givens phases, forests, and the first cycle variable

**Status: proved gauge reduction and single-final-gate closure; no blanket
claim for all unicyclic words.**

A complex Givens rotation on an edge (i,j) has the form

\[
\begin{pmatrix}
\cos t&e^{i\phi}\sin t\\
-e^{-i\phi}\sin t&\cos t
\end{pmatrix}.
\]

Conjugating the full word by a diagonal unitary changes the edge phase
by a difference of endpoint potentials. If the interaction graph is a
forest, solve those potentials successively from a root in each
component and remove every phase. If the graph has one independent
cycle, all but one edge phase can be removed; the remaining phase is
the signed sum around that cycle.

There is also a direct final-gate statement. Let V be real orthogonal
and U(phi)=G_ij(t,phi)V. A minor containing exactly one affected row is
A+e^{±i phi}B with real A,B; a minor containing both is unchanged by the
two-row determinant-one action. Thus all its squared minors are affine
in cos phi, giving the same two-endpoint convex law as Round 028.

Consequently a final complex gate may be reduced to its two real signs
whenever the preceding word is real. When a unique cycle phase occurs
in the middle of a word, subsequent real factors do not automatically
preserve this one-exponential form: both e^{i phi} and e^{-i phi} can
enter the same minor. The forest gauge argument by itself does not
justify stripping that interior cycle phase.


## Round 031 — The first-cycle support condition is a gap-sensitive Gram inequality

**Status: exact support criterion for one fiber; global verification remains open.**

Use the two-row fiber representation from Round 003:

\[
f(x)=c+\delta x^*Tx,\qquad
x=(\cos t,e^{i\phi}\sin t).
\]

Let F_0=Re(eta f(e_1)), F_1=Re(eta f(e_2)), and let h be the largest
permutation support value for the original spectra. Put

\[
A=\eta\delta T_{12},\qquad B=\eta\delta T_{21}.
\]

The fiber support at fixed t is

\[
\cos^2t\,F_0+\sin^2t\,F_1+
\sin t\cos t\,|A+\overline B|.
\]

This follows from maximizing
Re(A e^{i phi}+B e^{-i phi}) over phi. Assuming the endpoint deficits
d_0=h-F_0 and d_1=h-F_1 are nonnegative, the entire fiber stays below h
if and only if

\[
\boxed{|A+\overline B|^2\le4d_0d_1.}
\]

Indeed the required inequality is
c^2 d_0+s^2 d_1 >= cs |A+bar B| for all c,s >=0 with c²+s²=1.
The two-by-two quadratic form is nonnegative exactly under the boxed
condition.

Thus an induction that adds a cycle must control interference by the
geometric mean of the two available support margins. Merely knowing
that both endpoints satisfy MOC leaves the cross term unbounded.
When either endpoint is already on the support line, a successful
extension requires A+bar B=0. This identifies a sharp boundary
compatibility obligation rather than a uniform, spectra-free norm bound.

## Round 032 — Singular stationary points force the active spectrum onto a circle

**Status: proved necessary condition and algebraic classification of the
rank-one commutator condition. This excludes a broad singular branch.**

Let A=diag(a_1,...,a_n) have distinct entries, C=UBU*, M=A+C, and
eta !=0. Suppose rank M=n-1, so

\[
Q=\operatorname{adj}M=\kappa r l^*,\qquad \kappa\ne0,
\]

where r and l are right and left nullvectors. Stationarity of
Re(eta det(A+e^{tK}Ce^{-tK})) for every skew-Hermitian K means

\[
0=\operatorname{Re}\operatorname{tr}
  \bigl(\eta[C,Q]K\bigr).
\]

The real orthogonal complement of the skew-Hermitian matrices is the
Hermitian matrices. Since [M,Q]=0, the stationarity condition is exactly

\[
W=-\eta[A,Q]\quad\text{Hermitian}.
\]

Put t=-eta kappa. Its entries are
W_ij=t(a_i-a_j)r_i bar(l_j). If r_i !=0 but l_i=0, choose j with
l_j !=0. Then j !=i and W_ij !=0 while W_ji=0, contradicting
Hermiticity. The converse follows similarly. Hence

\[
\operatorname{supp}r=\operatorname{supp}l=S.
\]

For i in S put w_i=r_i/l_i. Hermiticity becomes

\[
t(a_i-a_j)w_i
=-\overline t\,\overline{(a_i-a_j)}\,\overline{w_j}.
\]

Taking absolute values shows that all |w_i| are equal. Write w_i=rho u_i
with |u_i|=1. Multiplying by u_j yields

\[
{t\over\overline t}u_i u_j
=-{\overline{a_i-a_j}\over a_i-a_j}.
\]

Multiply the equations for (i,j),(k,l), then divide those for
(i,k),(j,l). The u's and the t factors cancel. Consequently

\[
R_{ijkl}=
{(a_i-a_j)(a_k-a_l)\over(a_i-a_k)(a_j-a_l)}
=\overline{R_{ijkl}}.
\]

All cross-ratios on S are real. Equivalently, the distinct points
{a_i:i in S} lie on one generalized circle, meaning an ordinary circle
or a straight line. Three points impose no restriction; four do.

The commutator condition is sharp as a purely algebraic statement.
If a_i=z_0+R e^{i theta_i} lie on a circle, choose
u_i=e^{-i theta_i-i arg t}; the displayed Hermiticity equations hold.
For a straight line a_i=z_0+e^{i theta}x_i, choose
u_i=i e^{-i theta-i arg t}. This converse constructs a rank-one Q with
the required commutator, not a normal C realizing it as an adjugate.

For n=4 and four nonconcyclic eigenvalues of A, every rank-three singular
stationary point must therefore have nullvectors supported on at most
three A-eigenvectors. A full-support singular maximum is impossible.
The sparse-nullvector branch and nonsingular maxima remain to be treated.

The independent reviewer audited the circle derivation. The reviewer
also notes that the established external-vertex result already proves
the MOC4 inclusion when the actual determinant is zero. Thus the circle
lemma is a classification of critical geometry, not a claim of a new
determinant-zero MOC4 case. Its possible use in larger dimensions is
separate.

## Round 033 — A transverse determinant-zero stratum is a saddle

**Status: proved conditional exclusion for every nullity.**

Let M=A+C have rank n-k. Choose unitary left and right coordinates in
which

\[
M=\begin{pmatrix}D&0\\0&0_k\end{pmatrix},
\qquad \det D\ne0.
\]

Let L_0 and R_0 denote the left and right nullspace frames, in the
original coordinates. For a skew-Hermitian K put

\[
\mathcal L(K)=L_0^*[K,C]R_0\in M_k(\mathbb C).
\]

The block determinant expansion along the orbit gives

\[
\det(A+e^{tK}Ce^{-tK})
=\gamma\, t^k \det \mathcal L(K)+O(t^{k+1}),
\]

where gamma is a fixed nonzero scalar including det D and the changes
of left/right coordinates. The formula holds because a lowest-degree
nonzero determinant term must use one first-order entry in each of the
k null rows and columns; cross-block corrections cannot contribute
before that order.

If the real-linear map L is onto M_k(C), choose K with L(K) diagonal
and determinant of any prescribed complex phase. For either sign of
Re(eta gamma det L(K)), the leading term is realized. Thus the
determinant-zero point cannot be a local support maximum or minimum.

For k=2 this is a concrete eight-real-coordinate rank test. It handles
singular points whose first derivative vanishes identically because
adj M=0. The surjectivity assumption is essential; this investigation
does not prove it for every normal-matrix orbit, or for every putative
violating singular point.

## Round 034 — The full mixed Hessian makes the interior proof obligation explicit

**Status: exact necessary equations and a direct full-MOC proof attempt;
the required exclusion has not been proved.**

At an invertible M=A+C write N=M^{-1}, z=det M, and
D_K=[K,C]. Along a single generator K,

\[
{d^2\over dt^2}\det(A+e^{tK}Ce^{-tK})\bigg|_{t=0}
=z\left[
\operatorname{tr}N[K,[K,C]]
+(\operatorname{tr}ND_K)^2
-\operatorname{tr}(ND_KND_K)
\right].
\]

Polarization gives the real support Hessian

\[
\begin{aligned}
\mathcal H(K,L)=\operatorname{Re}\eta z\bigg[
&{1\over2}\operatorname{tr}N\bigl([K,[L,C]]+[L,[K,C]]\bigr)\\
&+\operatorname{tr}(ND_K)\operatorname{tr}(ND_L)
-\operatorname{tr}(ND_KND_L)
\bigg].
\end{aligned}
\]

A global violating maximum would satisfy simultaneously:

1. eta[C,adj M] is Hermitian;
2. H is negative semidefinite on all skew-Hermitian generators modulo
   the stabilizer of C;
3. Re(eta z) exceeds all permutation support values.

The root-ellipse tests inspect the restrictions of H to individual
two-row or two-column directions. They do not automatically control
the mixed K,L terms above. Those terms include both products of first
logarithmic derivatives and a noncommutative trace, so there is no
general diagonalization by row-pair labels at a noncommuting point.

The attempted proof was to combine the exact root deficits from Round
031 with a Gram representation of this mixed Hessian. No such
representation with the required sign was derived. In particular,
real stationarity only says Re(eta z tr ND_K)=0; it does not imply the
complex quantity tr ND_K vanishes. Dropping its product term would be
an invalid proof.

This leaves a precise interior target: rule out the three displayed
conditions using the normality and spectral rank structure. Rounds
032–033 separately remove some singular branches but do not settle
this nonsingular target.


## Round 036 — Plücker triangles force second-order saturation at permutation vertices

**Status: proved tangent-cone restriction.**

At a signed block-permutation vertex, a row has one occupied position j:
m_j=2, h_j=sigma with sigma in {-1,1}; its other entries vanish. Consider
a differentiable path in the nonnegative row-Plücker region,

\[
m_j=2+t\mu+o(t),\qquad h_j=\sigma+t\nu+o(t),
\]

and all off-position m_l,h_l=O(t). Since |h_l|<=m_l/2,
X_l=m_l²-4h_l²=O(t²). The Plücker triangle says

\[
\sqrt{X_j}\le\sum_{l\ne j}\sqrt{X_l}=O(t).
\]

Hence X_j=O(t²). But

\[
X_j=4t(\mu-2\sigma\nu)+o(t).
\]

Therefore every such tangent direction satisfies

\[
\boxed{\mu=2\sigma\nu.}
\]

In fact m_j-2sigma h_j=O(t²) under a bounded-derivative path, because
X_j=(m_j-2sigma h_j)(m_j+2sigma h_j) and the second factor tends to four.

A straight segment from the vertex toward a virtual point with
mu-2sigma nu>0 fails the Plücker condition for every sufficiently
small positive t. This explains why mixing a false linear-relaxation
witness with a permutation need not make it realizable.

The restriction is a tangent condition on the nonlinear moment set.
It is not a linear inequality valid on its whole convex hull: convex
mixtures of different realizable moment points need not satisfy an
individual Plücker triangle.

## Round 037 — A quantitative reduction from nearly saturated blocks to an improper O(3) factor

**Status: proved approximation theorem on actual SO(6).**

Let R in SO(6) be divided into three-by-three two-by-two blocks. Assume
each diagonal block has negative determinant. By determinant-one
left/right rotations inside each coordinate plane, put it in the form
diag(-a_i,b_i), with 1>=a_i>=b_i>=0. Define

\[
e=\sum_i(1-a_i^2)<1.
\]

Regroup the first coordinate from each plane before the second:

\[
R=\begin{pmatrix}T&E\\F&Q\end{pmatrix},
\qquad T_{ii}=-a_i,\quad Q_{ii}=b_i.
\]

The first three row norms give

\[
\|T+I\|_F^2+\|E\|_F^2
=\sum_i(1-a_i)^2+e\le e^2+e,
\]

and the corresponding column norms give ||F||_F²<=e. Orthogonality
implies Q*Q=I-E*E. Because ||E||_F²<=e<1, Q is invertible.
Let W be its orthogonal polar factor. Its singular-value formula gives

\[
\|Q-W\|_F^2
\le(1-\sqrt{1-e})^2\le e^2.
\]

Consequently

\[
\boxed{
\left\|R-\bigl((-I_3)\oplus W\bigr)\right\|_F
\le \sqrt{2e+2e^2}<2.
}
\]

Two real orthogonal matrices in opposite determinant components have
Frobenius distance at least two, since their relative orthogonal
matrix has eigenvalue -1. Therefore the approximating block diagonal
matrix has determinant +1 and W has determinant -1.

Also

\[
|W_{ii}-b_i|\le1-\sqrt{1-e}.
\]

If each b_i is at least this bound, W has nonnegative diagonal and
lies in the improper O(3) sector used in the exact saturated-slice
classification. This moves that classification into a controlled
neighborhood of actual SO(6), but does not assert every global
support maximum is near this sector.

## Round 038 — A certified open region for the orientation penalty

**Status: proved perturbation bound and explicit nonempty open region;
this penalty alone does not prove MOC.**

Write the fixed cyclic orientation penalty as

\[
\Phi(R)=
\sum_i(m_{ii}+6h_{ii})+
4(m_{12}+m_{23}+m_{31}).
\]

As a quadratic form in the 36 real matrix entries, its operator norm
is four. On a diagonal two-by-two block,
||B||_F²+6det B has eigenvalues 4 and -2 on each of its two coordinate
pairs. Each forbidden off-diagonal block has coefficient four, and
the other blocks have coefficient zero.

Thus for R,S in O(6),

\[
|\Phi(R)-\Phi(S)|
\le4(\|R\|_F+\|S\|_F)\|R-S\|_F
=8\sqrt6\,\|R-S\|_F.
\]

Combining with Round 037 gives

\[
\Phi(R)\ge
\Phi((-I_3)\oplus W)-8\sqrt6\,\sqrt{2e+2e^2}.
\]

Whenever the right side is nonnegative this proves the actual
orientation inequality in an interior neighborhood of a saturated
point. The margin is computable from a three-by-three improper
orthogonal factor.

For a completely explicit example take

\[
W=I-\frac23\mathbf1\mathbf1^T,
\qquad
R_0=(-I_3)\oplus W
\]

and undo the coordinate regrouping. Here W is a reflection, its diagonal
is 1/3, and its off-diagonal entries are -2/3. Directly,
sum(m_ii+6h_ii)=-8/3 and the cyclic forbidden sum is 4/3, so
Phi(R_0)=8/3. Therefore

\[
\|R-R_0\|_F<1/(3\sqrt6)
\quad\Longrightarrow\quad \Phi(R)>0.
\]

This is an exact open subset of SO(6), not a numerical extrapolation
of the boundary theorem. Other symmetry copies follow by changing
the chosen coordinate planes and orientations.

## Round 039 — All codimension-two rank degenerations reduce to the rectangular law

**Status: proved general asymptotic reduction; its arbitrary-parent
endpoint theorem is conditional on the open compression law.**

Let A_0,B_0 be normal matrices of positive ranks r,s with
r+s=n-2. Their nonzero spectral subspaces have orthonormal frames
V_A,V_B whose concatenation V has independent columns. Let

\[
H=(\operatorname{range}V)^\perp,\quad \dim H=2,\quad
\delta=\det(V^*V)\in(0,1].
\]

Let gamma be the product of all nonzero eigenvalues of A_0 and B_0.
Perturb normally inside the separate kernels:
A(t)=A_0+tA_1, B(t)=B_0+tB_1, where each small normal part kills the
corresponding large spectral subspace. Block determinant expansion
in the range of V and its orthogonal complement gives

\[
\boxed{
\frac{\det(A(t)+B(t))}{\gamma t^2}
\longrightarrow
\delta\det(P_H(A_1+B_1)|_H).
}
\]

The projected small eigenframes are two-row coisometries X,Y with

\[
\#\text{columns}(X)=n-r=s+2,\qquad
\#\text{columns}(Y)=n-s=r+2.
\]

Every normalized permutation vertex has one of two limits. If all
large eigenvalues pair separately with small ones, the limit is
(a_i+b_j)(a_k+b_l), with distinct selected indices on both sides.
If any large A eigenvalue pairs with a large B eigenvalue, the limit
is zero: the extra small-small pairing contributes an extra t.
Every size-two matching product is realized by completing the
remaining small indices against the large ones.

Thus a common matching law for these two coisometries proves the
limiting MOC inclusion; delta mixes with the zero vertex. The already
proved (3,3) case gives r=s=1,n=4. The first new positive-rank case is
n=5 with (r,s)=(1,2) or (2,1), exactly the open (3,4) problem of
Round 022.

Strict inclusion in the limiting product hull yields a finite small-t
MOC neighborhood by the same support-margin argument as Round 011.
This is a precise way in which the Bell-locality theorem, if extended,
would create new interior normal-matrix regions in higher dimensions.

## Round 040 — Determinant-preserving root reflections fix every generic support maximum

**Status: proved obstruction to a proposed global rounding strategy.**

The determinant-preserving reflection from Round 020 is best viewed
on a Bloch sphere. Write a nondegenerate two-row fiber as

\[
f(\mathbf n)=c+\boldsymbol\ell\cdot\mathbf n,\qquad
|\mathbf n|=1,
\]

where a=Re ell and b=Im ell are linearly independent. Let k be the unit
normal to span(a,b). Reflection

\[
\mathbf n\mapsto\mathbf n-2(\mathbf n\cdot\mathbf k)\mathbf k
\]

preserves f and exchanges its two preimages in the ellipse interior.

Now maximize a nonzero support direction Re(eta f) on this sphere.
Its nonconstant real linear coefficient is

\[
\mathbf v=\operatorname{Re}(\eta\boldsymbol\ell)
\in\operatorname{span}(\mathbf a,\mathbf b).
\]

Nondegeneracy makes v nonzero. The maximizing Bloch vector is
n=v/||v||, hence n dot k=0. It is therefore fixed by the
determinant-preserving reflection.

In particular, any hypothetical violating global support maximum is
fixed by every nondegenerate two-row reflection and every corresponding
two-column reflection. Even a point merely optimal on all those
fibers has this fixed-point property.

Thus compositions of these involutions cannot move such a point at
all. A successful rounding argument must exploit degenerate fibers,
larger-coordinate fibers, or a move that temporarily changes the
determinant while improving the support objective. The exact reflection
is useful in ellipse interiors, but it does not by itself furnish the
missing global MOC proof.


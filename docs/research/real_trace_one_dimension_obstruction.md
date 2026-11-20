# Sharp real dimension threshold for trace-one basis decompositions

## Scope and literature

This note proves an exact obstruction for a convex-decomposition step used in
`../theorems/profile_geometry/algebra_unitary_realification.md`. It does **not**
disprove MOC, and it does not disprove unrestricted unitary-to-orthogonal minor
profile convexification in dimension five.

Let
\[
\mathcal T_d^{\mathbb R}=\{(E_1,\ldots,E_d):
 E_i=E_i^T\succeq0,\ \operatorname{tr}E_i=1,\ \sum_iE_i=I_d\}.
\]
Let \(\mathcal B_d^{\mathbb R}\) be the convex hull of tuples
\((r_1r_1^T,\ldots,r_dr_d^T)\), where the \(r_i\) form a real orthonormal
basis. These are mixtures of rank-one orthogonal measurements with one
projector per label; more general postprocessing of measurements is not being
identified with this set. Theorem 3 below separately proves a stronger
non-simulability result allowing arbitrary classical postprocessing.

Oszmaniec, Guerini, Wittek and Acín, *Simulating positive-operator-valued
measures with projective measurements*, arXiv:1609.06139, prove the complex
qutrit trace-one decomposition and give a complex dimension-four obstruction
using two copies of a tetrahedral qubit measurement. The local real
three-dimensional proof establishes the version used by MOC realification.
The construction below is real, rational, and is already the tuple of real
parts of the rank-one projectors of a complex orthonormal basis. No historical
priority claim is made for this real construction or its consequences.

## Theorem 1: the threshold is exactly three

\[
\boxed{\mathcal T_d^{\mathbb R}=\mathcal B_d^{\mathbb R}
       \quad\Longleftrightarrow\quad d\le3.}
\]

For \(d=4\), the following explicit tuple is an extreme point of
\(\mathcal T_4^{\mathbb R}\), and all four effects have rank two.

Put \(c=3/5\), \(s=4/5\), and
\[
C=\begin{pmatrix}
1&c&1&0\\
c&1&c&s\\
1&c&1&0\\
0&s&0&1
\end{pmatrix},\qquad
S=\begin{pmatrix}
1&1&1&1\\
1&1&-1&-1\\
1&-1&1&-1\\
1&-1&-1&1
\end{pmatrix}.
\]
If \(D_i\) is diagonal with the entries of row \(i\) of \(S\), define
\[
\boxed{E_i=\tfrac14D_iCD_i,\quad 1\le i\le4.}
\tag{1}
\]
More generally, the same proof works for any real \(c,s\) with
\(c^2+s^2=1\) and \(cs\ne0\).

### Positivity, normalization, and complex-basis origin

Set
\[
x_i=\tfrac12D_i(1,c,1,0)^T,
\qquad y_i=\tfrac12D_i(0,s,0,1)^T.
\]
Then \(E_i=x_ix_i^T+y_iy_i^T\), so it is positive semidefinite and has
rank two. Its trace is
\((2+c^2+1+s^2)/4=1\). The orthogonality of the columns of \(S\)
gives \(\sum_iE_i=I_4\).

For the rational choice above, the two nonzero eigenvalues of every effect
are \(13/20\) and \(7/20\). For example, the Gram matrix of \(x_i,y_i\)
is \(\frac1{100}\begin{pmatrix}59&12\\12&41\end{pmatrix}\).

The matrix
\[
V=\tfrac12S\operatorname{diag}(1,c+is,1,i)
\tag{2}
\]
is unitary. If its rows, transposed, are denoted \(z_i=x_i+iy_i\), then
\[
E_i=\operatorname{Re}(z_i z_i^*).
\tag{3}
\]
Thus failure occurs even in the restricted class of real-part effects arising
from a complex orthonormal basis, not merely for arbitrary real effects.

### Extremality: an exact four-character calculation

It suffices to show that a tuple of real symmetric perturbations \(H_i\)
supported on \(\operatorname{ran}E_i\), satisfying
\[
\operatorname{tr}H_i=0,\qquad\sum_iH_i=0,
\tag{4}
\]
must vanish. Indeed, endpoints of any convex decomposition of a positive
semidefinite effect must be supported in its range; conversely sufficiently
small supported two-sided perturbations preserve positivity.

Since \(x_i,y_i\) are independent, write uniquely
\[
H_i=a_i x_ix_i^T+b_i y_iy_i^T
       +k_i(x_iy_i^T+y_ix_i^T).
\tag{5}
\]
The trace equation is
\[
(2+c^2)a_i+(1+s^2)b_i+2cs\,k_i=0.
\tag{6}
\]
Write \(\sigma_{ij}=S_{ij}\). The diagonal entries of \(\sum_iH_i=0\)
give
\[
\sum_i a_i=\sum_i b_i=\sum_i k_i=0.
\tag{7}
\]
Here the last equation follows from the second diagonal entry and \(cs\ne0\).

The four vectors
\[
\mathbf1,\quad \chi_2=(\sigma_{i2})_i,\quad
\chi_3=(\sigma_{i3})_i,\quad \chi_4=(\sigma_{i4})_i
\]
are an orthogonal basis of \(\mathbb R^4\). Let
\(\widehat a_r=\sum_i\sigma_{ir}a_i\), and likewise for \(b,k\),
where \(r=2,3,4\).

The six off-diagonal entries in the sum equation are, after dropping nonzero
common factors,
\[
\begin{array}{c|c}
\text{entry}&\text{equation}\\ \hline
12&c\widehat a_2+s\widehat k_2=0\\
34&\widehat k_2=0\\
13&\widehat a_3=0\\
24&s\widehat b_3+c\widehat k_3=0\\
14&\widehat k_4=0\\
23&c\widehat a_4+s\widehat k_4=0.
\end{array}
\tag{8}
\]
Equation (6) holds in each character as well. For characters 2 and 4,
(8) first gives \(\widehat k_r=\widehat a_r=0\), and (6) gives
\(\widehat b_r=0\). For character 3, substitute
\(\widehat a_3=0\) and
\(\widehat k_3=-s\widehat b_3/c\) into (6). The result is
\[
(1+s^2-2s^2)\widehat b_3=c^2\widehat b_3=0.
\]
Thus this character vanishes too. Equation (7) kills the constant character.
All four characters of each coefficient vector vanish, proving \(H_i=0\).

The tuple (1) is therefore extreme. It cannot be a mixture of orthogonal
rank-one basis tuples: extremality would force every tuple in the mixture
to equal (1), whereas each effect in (1) has rank two.

### Lower and higher dimensions

The case \(d=1\) is immediate. For \(d=2\), the two effects sum to the
identity and commute; trace one makes their joint eigenvalues
\((t,1-t)\) and \((1-t,t)\), yielding two basis tuples.

For \(d=3\), if every effect has rank at least two, the space of supported
symmetric perturbations has dimension at least nine. The symmetric sum
constraint and individual traces impose at most eight independent
conditions. Hence some effect of every extreme tuple has rank one. That
effect is a projection, the other two act on its orthogonal complement,
and the dimension-two argument completes the proof.

For \(d>4\), append the coordinate projectors of \(\mathbb R^{d-4}\) to
(1), extended by zero. A hypothetical basis mixture must preserve these
rank-one effects term by term and would restrict to a basis mixture of (1),
which is impossible. This proves Theorem 1.

## Theorem 2: fixed-row minor realification fails already in dimension five

There is an explicit \(U\in U(5)\) with a nonzero real first row \(v^T\)
whose squared singleton and two-minor profiles cannot be represented as a
convex mixture of profiles of real orthogonal matrices **all having first
row \(v^T\)**.

Take
\[
h=(1,-1,-1,-1,-1)^T,\quad
R=I_5-\tfrac25hh^T,\quad
v=Re_1=\tfrac15(3,2,2,2,2)^T.
\]
Let \(Q\) consist of columns 2 through 5 of \(R\). Then
\(Q^TQ=I_4\), \(Q^Tv=0\), and \(QQ^T=I_5-vv^T\). With (2), define
\[
\boxed{U=\begin{pmatrix}v^T\\VQ^T\end{pmatrix}.}
\tag{9}
\]
This is a unitary matrix with Gaussian-rational entries.

Suppose such a fixed-row real mixture existed. For each nonfixed row, let
\(F_i=\operatorname{Re}(w_iw_i^*)=QE_iQ^T\), where \(w_i\) is the
corresponding row of \(U\), transposed. Preserving singleton minors gives
\((F_i)_{jj}\). Preserving two-minors involving the fixed row gives
\[
|w_{ij}v_k-w_{ik}v_j|^2
=v_k^2(F_i)_{jj}+v_j^2(F_i)_{kk}-2v_jv_k(F_i)_{jk}.
\tag{10}
\]
Every \(v_j\) is nonzero, so these data recover every entry of \(F_i\).
Consequently the purported profile mixture would yield a common
orthonormal-basis decomposition of the four effects \(F_i\) on \(v^\perp\).
Conjugating by \(Q^T\) contradicts Theorem 1.

The same obstruction holds if each real summand is required only to have
first-row absolute values equal to those of \(v\): column sign changes make
each first row equal to \(v\), without changing any squared minor.

**Important limitation.** A mixture whose summands have different first-row
absolute values is not excluded. Therefore (9) is not a counterexample to
unrestricted profile realification, much less to MOC. It closes the precise
fixed-row extension of the four-dimensional construction.

## Theorem 3: real measurements can require complex projective simulators

Here a measurement is projective-simulable if it is a convex mixture of
projective measurements on the **same Hilbert space**, allowing arbitrary
classical postprocessing of their outcomes. No ancilla is allowed. A real
simulator uses real orthogonal projectors in the specified basis; a complex
simulator uses complex Hermitian projectors.

**Theorem.** For real-effect POVMs, complex and real projective simulability
coincide in dimensions at most three, for every number of outcomes. They
differ in every dimension at least four. The tuple (1) is an explicit rational
counterexample in the smallest possible dimension: it is a half-and-half
mixture of two complex orthonormal-basis measurements, but admits no real
projective simulation even with arbitrary classical postprocessing.

### The two complex simulators

Equation (3) gives immediately
\[
E_i=\tfrac12 z_i z_i^*+\tfrac12\bar z_i z_i^T.
\tag{11}
\]
Both \((z_i)_i\) and \((\bar z_i)_i\) are complex orthonormal bases.

### Excluding classical postprocessing of real projectors

A stochastic postprocessing of a projective measurement is a convex mixture
of deterministic relabelings. Each deterministic relabeling is itself a
projective measurement with possibly zero or higher-rank projectors attached
to the output labels. Thus a hypothetical real simulation can be written
\[
E_i=\sum_\alpha p_\alpha P_i^{(\alpha)},
\tag{12}
\]
where each tuple \((P_i^{(\alpha)})_{i=1}^4\) consists of mutually orthogonal
real projections summing to the identity. Positivity forces
\(\operatorname{ran}P_i^{(\alpha)}\subset S_i:=\operatorname{ran}E_i\)
for every term of positive weight.

The planes in (1) obey
\[
\boxed{S_j\cap S_i^\perp=\{0\}\quad(i\ne j).}
\tag{13}
\]
For an exact check, put \(B_i=[x_i\ y_i]\). Every relative diagonal sign
\(D_iD_j\) is one of \(D_2,D_3,D_4\). The three possible cross-Gram matrices,
up to the common factor \(1/4\), are
\[
\begin{pmatrix}c^2&cs\\cs&-c^2\end{pmatrix},\quad
\begin{pmatrix}2-c^2&-cs\\-cs&-(1+s^2)\end{pmatrix},\quad
\begin{pmatrix}-c^2&-cs\\-cs&c^2\end{pmatrix}.
\tag{14}
\]
Their determinants, before the factor \(1/16\), are
\(-c^2,-(1+3s^2),-c^2\), respectively. They are nonzero, proving (13).

If a projector in a tuple in (12) had rank two, its range would be all of
\(S_i\). Every other projector would have range in \(S_j\cap S_i^\perp\),
hence would be zero by (13). Such a tuple cannot sum to \(I_4\). Therefore
all its projectors have rank at most one. There are four labels and total
rank four, so each has rank one. Equation (12) would now be a mixture of
one-projector-per-label real bases, already excluded by Theorem 1.

This verifies the stronger claim; extremality inside the trace-one set
alone would not have sufficed to exclude arbitrary classical postprocessing.

### Why dimensions two and three cannot separate real and complex simulators

Refine a complex projective simulator into rank-one basis projectors
\((Q_j)_{j=1}^d\), then include its classical postprocessing coefficients.
If the target measurement has real effects, take entrywise real parts of the
entire decomposition. Each tuple \((\operatorname{Re}Q_j)_j\) lies in
\(\mathcal T_d^{\mathbb R}\). For \(d\le3\), Theorem 1 replaces it with a
mixture of real orthonormal-basis tuples. Applying the same postprocessing
coefficients produces a real projective simulation of the target.

Conversely, every real projective simulator is also complex. This proves
equality in dimensions at most three, regardless of the number of outcomes.

For \(d>4\), extend (1) by zeros and append rank-one coordinate effects on
\(\mathbb R^{d-4}\). In a real projective simulation, every appended effect
would have to be that same rank-one projector in every positive-weight
component: its range is fixed by positivity, and its trace-one average
forces every component's rank to be one. Restricting to the remaining
four-dimensional subspace contradicts the preceding argument. The two
complex simulators in (11) extend by the same coordinate projectors.

### What this settles and what it does not

This is a fully specified, proved dimension-threshold result in the
projective-simulability setting of arXiv:1609.06139. The search performed for
this note did not locate this particular real-versus-complex theorem, but
that is not a proof of historical novelty. It does not solve the broader
open problems from that paper concerning general SDP characterizations or
optimal depolarizing-noise thresholds.

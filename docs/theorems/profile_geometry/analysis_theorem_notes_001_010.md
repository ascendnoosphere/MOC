## Round 001 — Stable generating polynomials and determinantal point processes

### Attempted principle

Try to derive MOC from stability/negative dependence of the polynomial

\[
Q_U(x,y)=\det(D_x+UD_yU^*).
\]

Every permutation polynomial is \(Q_\pi=\prod_i(x_i+y_{\pi(i)})\), so a sufficiently strong extremal theorem for this stable family could prove MOC.

### Actual derivation

Cauchy–Binet gives the identity

\[
Q_U(x,y)=\sum_{|I|=|J|}|\det U[I,J]|^2 x_{I^c}y_J.
\]

Every coefficient is nonnegative. If all variables have positive imaginary parts, the imaginary part of \(D_x+UD_yU^*\) is positive definite; the matrix is invertible. Thus \(Q_U\) is real stable.

There is a precise probability model. Let \(M=[I\ U]\), and let

\[
P=\tfrac12M^*M=\tfrac12
\begin{pmatrix}I&U\\U^*&I\end{pmatrix}.
\]

Then P is a rank-n projection. The coefficient of \(x_{I^c}y_J\), divided by \(2^n\), is the probability of the corresponding n-element set in its projection determinantal process. Normalization follows from \(Q_U(1,1)=2^n\).

This shows that MOC asks about a complex multiplicative observable of a special projection process.

### Weakest implication and outcome

The stronger polynomial claim

\[
Q_U\in\operatorname{conv}\{Q_\pi\}
\]

The coefficient-hull assertion is the stronger spectrum-independent common-minor law. Real stability does not establish this assertion; no such law is proved here.

The original scalar evaluation might still obey a more delicate stable-polynomial inequality. The missing theorem would need the multiplicative spectral observable; generic negative association cannot simply replace the entire process by a matching law.

Status: the exact representation and stability are proved; the universal scalar implication remains unresolved.

Primary context: Borcea–Brändén, Applications of stable polynomials to mixed determinants, Duke Math. J. 143 (2008), 205–223, https://arxiv.org/abs/math/0607755. The paper's mixed-determinant results are background, not a proof of the proposed MOC step.

## Round 002 — Fermionic occupation sectors and incompatible assignment maxima

### Attempted principle

Represent the determinant on fermionic Fock space, and apply ordinary doubly stochastic rearrangement separately in each particle-number sector.

For invertible A,

\[
\det(A+UBU^*)=\det A\,
\operatorname{Tr}\bigl(\Gamma(A^{-1})\Gamma(U)\Gamma(B)\Gamma(U)^*\bigr),
\]

where \(\Gamma(T)=\bigoplus_k\wedge^kT\). The polynomial minor expansion extends this through singular A.

### Actual calculation

For each k, \((|\det U[I,J]|^2)_{|I|=|J|=k}\) is doubly stochastic. In dimension four, complementary minors identify the k=1 and k=3 sectors, so I combined those before taking assignment maxima.

The combined singleton cost is

\[
C^{(1)}_{ij}=\operatorname{Re}
(a_{[4]\setminus i}b_j+a_i b_{[4]\setminus j}),
\]

and the middle cost is

\[
C^{(2)}_{I,J}=\operatorname{Re}(a_{I^c}b_J).
\]

A sectorwise rearrangement bound is valid, but the separate maximizing assignments must not be assumed to arise from one common permutation or exterior lift of a unitary.
## Round 003 — Every two-coordinate surgery is an exact filled ellipse

### Attempted principle

Construct an ascent or rounding process by repeatedly rotating two eigendirections of A. The hope is that exact one-step geometry reveals a global monotonicity rule.

### Actual proof

Keep all but the i,j block of A fixed. Write the rotated block as

\[
a_0 I+\delta\,n\cdot\sigma,\qquad n\in S^2,
\]

where \(a_0=(a_i+a_j)/2\), \(\delta=(a_i-a_j)/2\), and \(\sigma\) are the Pauli matrices.

When the complementary block F of A+C is invertible, form the 2-by-2 Schur complement T after inserting \(a_0I\). Then

\[
\det(A(n)+C)
=\det F\,[\det T-\delta^2+
\delta\operatorname{tr}(\operatorname{adj}(T)\,n\cdot\sigma)].
\]

Therefore

\[
d(n)=\alpha+\beta_1n_1+\beta_2n_2+\beta_3n_3,
\qquad \alpha,\beta_k\in\mathbb C.
\]

Continuity, or direct determinant expansion, removes invertibility of F. A real linear map from \(S^2\) to \(\mathbb R^2\) has image a filled ellipse (with possible degeneration). Its support is

\[
\max_{n\in S^2}\operatorname{Re}(\eta d(n))
=\operatorname{Re}(\eta\alpha)+
\sqrt{\sum_k[\operatorname{Re}(\eta\beta_k)]^2}.
\]

Thus a proposed global maximum must be an exact supporting endpoint of every such ellipse.

### Concrete obstruction to endpoint-only rounding

Already for

\[
A=\operatorname{diag}(0,1),\qquad
C=\begin{pmatrix}0&1\\1&0\end{pmatrix},
\]

the two coordinate placements of the eigenvalues of A both give determinant -1. The full two-coordinate rotation has determinant \(-1+n_x\), whose maximum is 0.

The ellipse step therefore cannot be replaced by checking only the two old coordinate endpoints. Those endpoints are not the spectral permutation vertices unless C is already diagonal in that basis.

Status: full local geometry proved. A global process that follows these ellipses to a common eigenbasis without losing support remains unproved.

## Round 004 — A one-parameter semidefinite completion for every Cayley ray

### Attempted principle

Use the inherited exact Cayley numerator, but avoid trying to dominate its cubic term in isolation. Reduce the entire radial inequality to a single semidefinite completion parameter.

### Actual reduction

Relabel spectra so the identity permutation maximizes the chosen support functional. For any zero-diagonal skew-Hermitian K in dimension four, put

\[
U_t=(I+tK)(I-tK)^{-1}.
\]

The prior exact decomposition implies that the support deficit numerator has the form

\[
P(t)=h|\det(I-tK)|^2-
\operatorname{Re}\bigl(\eta\det N(t)\bigr)
=t^2(q_0+q_1t+q_2t^2+q_3t^3+q_4t^4).
\]

The endpoint coefficients \(q_0,q_4\) are nonnegative sums of transposition support gaps times squared matrix entries.

A real quartic \(q(t)=q_0+\cdots+q_4t^4\) is nonnegative on the real line if and only if there is a real z such that

\[
\begin{pmatrix}
q_0&q_1/2&z\\
q_1/2&q_2-2z&q_3/2\\
z&q_3/2&q_4
\end{pmatrix}\succeq0.
\]

Indeed the displayed matrix gives a sum of squares in \(1,t,t^2\). Conversely every nonnegative univariate quartic is a sum of squares of real quadratics, and matching its five coefficients leaves exactly this one free Gram entry. Degenerate quartics are included.

Every zero-diagonal K defines a unitary for every real t. The canonical phase gauge guarantees coverage of all original U at some t, so this is a valid universal proof template.

### Exact remaining obligation

Prove that, for actual spectral coefficients, this 3-by-3 matrix always has a positive semidefinite completion z. A pointwise z need not have a universal polynomial formula.

No such universal completion was proved here. This formulation does retain quartic/cubic interaction that the previously refuted low-degree truncation discards.


## Round 006 — Exact tetrahedral spectral arrays in Spin coordinates

### Attempted principle

Separate the abstract orientation geometry from the special low-rank structure of spectral support costs.

### Actual derivation

Let the four sign vectors be

\[
\epsilon_1=(1,1,1),\ \epsilon_2=(1,-1,-1),\
\epsilon_3=(-1,1,-1),\ \epsilon_4=(-1,-1,1).
\]

Write \(a_k=a_0+\epsilon_k\cdot x\) and \(b_l=b_0+\epsilon_l\cdot y\).

For each i, with the other indices j,k, define

\[
S_{Ai}=a_0^2+x_i^2-x_j^2-x_k^2,
\]
\[
D_{Ai}=2(a_0x_i-x_jx_k),
\]
\[
Y_{Ai}=x_iS_{Ai}-a_0D_{Ai}.
\]

The vector \(Y_A\) is the tetrahedral Fourier coefficient of the complementary triple products \(a_{[4]\setminus k}\). Define the B quantities analogously.

Take complementary pair order \(12|34,\ 13|24,\ 14|23\). In the real Hodge basis for \(\wedge^2U\), write its 2-by-2 blocks \(R_{ij}\), and set

\[
m_{ij}=\|R_{ij}\|_F^2,\qquad h_{ij}=\det R_{ij}.
\]

Equivalently, entirely in unitary moments,

\[
h=\tfrac14\epsilon^T p\epsilon,\qquad
q_{I_i,I_j}=(m_{ij}+2h_{ij})/4,
\]
\[
q_{I_i,I_j^c}=(m_{ij}-2h_{ij})/4.
\]

The determinant has the exact form

\[
d=K_0+\sum_{ij}S_{Ai}S_{Bj}m_{ij}
+\sum_{ij}\bigl[4x_iY_{Bj}+4Y_{Ai}y_j-2D_{Ai}D_{Bj}\bigr]h_{ij},
\]

where

\[
K_0=\prod a+\prod b+
4(a_0\overline{b^{(3)}}+\overline{a^{(3)}}b_0).
\]

Here the overbar on \(a^{(3)},b^{(3)}\) denotes arithmetic mean, not complex conjugation; explicitly \(\overline{a^{(3)}}=\frac14\sum_k\prod_{\ell\ne k}a_\ell\).

For support direction eta, take the real part of eta times all coefficients. In particular the m coefficient matrix has real rank at most two. The h coefficient matrix is a real part of three complex rank-one matrices and has real rank at most six.

### Check and status

The formula was reconstructed at all 24 permutation points, and the identity relating h to p and q was separately checked on a general complex unitary. More importantly, it follows directly from the 2-by-2 identity \(RJR^T=(\det R)J\) and the tetrahedral Fourier expansion.

The precise spectral rank structure is now available for a cone theorem. It does not by itself imply such a theorem.


## Round 008 — Cross-row block orthogonality and a uniform exclusion radius

### Attempted principle

Find the smallest nonlinear inequality that repairs the exact ghost in round 007.

### Universal inequality and proof

For two distinct block rows r,s and a chosen block column j, orthogonality gives

\[
R_{rj}R_{sj}^T=-\sum_{k\ne j}R_{rk}R_{sk}^T.
\]

Taking Frobenius norms and using the smallest singular value of \(R_{rj}\),

\[
\frac{m_{rj}-\sqrt{m_{rj}^2-4h_{rj}^2}}{2}\,m_{sj}
\le
\left(\sum_{k\ne j}\sqrt{m_{rk}m_{sk}}\right)^2.
\]

A weaker form, useful without the nested radical, is

\[
\frac{|h_{rj}|^2m_{sj}}{m_{rj}}
\le
\left(\sum_{k\ne j}\sqrt{m_{rk}m_{sk}}\right)^2
\]

when \(m_{rj}>0\). It follows from
\(\sigma_{\min}(R_{rj})\ge |h_{rj}|/\sqrt{m_{rj}}\).
The zero case is handled without division by the original norm inequality.

For the ghost and (r,s,j)=(1,2,1), the sharp left side is 4/9 and the right side is zero.

### Exact robust exclusion

Every actual paired moment vector is at sup-norm distance greater than 1/27 from this ghost.

Suppose the distance were at most \(1/27\). Then

\[
|h_{11}|\ge8/27,\quad
m_{21}\ge35/27,\quad
m_{11}\le19/27,
\]

so the weak left side is at least \(2240/13851\). Meanwhile,

\[
(\sqrt{m_{12}m_{22}}+\sqrt{m_{13}m_{23}})^2
\le2\cdot(1/27)\cdot(56/27)
=2128/13851.
\]

The strict rational gap \(112/13851\) is impossible.

Status: proved universal nonlinear inequalities and a quantitative exclusion ball. These need not be preserved under arbitrary convex combinations of moments; round 009 supplies a separate convex-face statement.


## Round 010 — A controlled-martingale proof template with a Lyapunov requirement

### Attempted principle

Use a degenerate diffusion that preserves the complex determinant in expectation while progressively aligning the eigenspaces. This can avoid demanding that every deterministic local maximum be a permutation.

### Precise sufficient theorem

Let d(U) be the complex determinant for fixed spectra on the compact unitary quotient. Let V be a continuous nonnegative function vanishing exactly at the monomial classes (for simple spectra one may use the off-diagonal squared norm of \(UD_bU^*\)).

Suppose there is a Feller diffusion, absorbing at those classes, with generator L such that

\[
L\,\operatorname{Re}d=L\,\operatorname{Im}d=0,
\qquad LV\le-cV
\]

for some c>0, with the usual generator regularity sufficient for Dynkin's formula.

Then MOC follows.

Proof: d(U_t) is a bounded complex martingale, so it converges almost surely and in expectation. Dynkin's formula and Gronwall give
\(\mathbb EV(U_t)\le e^{-ct}V(U_0)\).
By compactness and continuity, the distance from d(U_t) to the finite set of spectral permutation values tends to zero in probability. Its martingale limit therefore belongs to that finite set almost surely. Taking expectation gives the required convex law.

### An exact nontrivial base case

For n=2, after phase reduction let \(p=|u_{11}|^2\). Then

\[
d(p)=p z_{\rm id}+(1-p)z_{\rm swap}.
\]

The Wright–Fisher generator

\[
L=p(1-p)\,\frac{d^2}{dp^2}
\]

has \(Ld=0\). For \(V=p(1-p)\), \(LV=-2V\); its endpoints are absorbing. Thus the theorem reproduces the actual convex law.

### Where a higher-dimensional construction must work

Writing

\[
L=X_0+\tfrac12\sum_r X_r^2
\]

turns preservation of d into two real linear equations in drift and positive diffusion covariance, while Lyapunov decrease is a strict inequality. At points where the determinant differential has rank two, a drift can compensate two prescribed diffusion corrections; the difficult issue is simultaneously decreasing V, crossing singular strata, and keeping the process degenerate at terminal classes.

A globally uniformly elliptic generator cannot do this: on a compact connected manifold, a harmonic real function is constant by the maximum principle, whereas d is generally nonconstant. Thus degeneracy is structurally necessary, not an implementation detail.

Status: sufficient theorem proved and n=2 construction exact. No higher-dimensional generator satisfying all three conditions was constructed. This remains a concrete speculative route, not a completed proof.


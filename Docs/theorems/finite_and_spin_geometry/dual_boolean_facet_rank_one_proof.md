# An exact rank-one certificate for a genuinely complex CH facet

## Status

This note proves one fixed complex spectral support inequality, uniformly for every unitary matrix of order four. It also classifies all equality cases and proves stability in an open neighborhood of this particular support instance. The universal support inequality for arbitrary spectra and directions remains open; this is not a proof of MOC.

All displayed Gram matrices, polynomial identities, principal minors, and permutation support values are checked over the rational numbers by `code/theorems/finite_and_spin_geometry/dual_boolean_facet_exact_certificate.py`. The argument below is independent of a numerical search or of the earlier realification theorem.

## 1. The actual unitary inequality

Write the rows of a unitary matrix as $r,v,s,t$, in that order. For a set $J$, let $\beta_J=\prod_{j\in J}\beta_j$. Define

\[
\begin{aligned}
D_1(U;\beta)&=\sum_j\beta_j|U_{1j}|^2+
 \sum_{|J|=2}\beta_J|\det U[12,J]|^2,\\
D_0(U;\beta)&=\sum_{|J|=3}\beta_J|\det U[124,J]|^2+
 \sum_{|J|=2}\beta_J|\det U[14,J]|^2.
\end{aligned}
\tag{1}
\]

Take

\[
\beta=(-4+4i,\ 2i,\ -1-2i,\ 1-3i),\qquad
\lambda_0=26+43i,\quad\lambda_1=-9+638i.
\tag{2}
\]

**Theorem 1.** For every $U\in U(4)$,

\[
\boxed{\operatorname{Re}(\lambda_0D_0(U;\beta)+\lambda_1D_1(U;\beta))\le2850.}
\tag{3}
\]

For a permutation $\pi$, the corresponding point is

\[
w_\pi=(\beta_{\pi(1)}(1+\beta_{\pi(2)})\beta_{\pi(4)},\
\beta_{\pi(1)}(1+\beta_{\pi(2)})).
\]

Exactly four permutation points have support value $2850$:

\[
2143,\qquad3214,\qquad3421,\qquad4321.
\tag{4}
\]

The twenty-four points have real affine dimension four and these four exposed points have affine dimension three. Thus (3) is an actual facet inequality of their convex hull in $\mathbb C^2\cong\mathbb R^4$.

## 2. The fixed-row compression, including complex remaining rows

Column phases do not change any squared minor. Choose them so that $v\in\mathbb R^4$, $\|v\|=1$, and put

\[
P=I-vv^T,\qquad H=v^\perp,\qquad p_\beta=\prod_j\beta_j.
\]

For a complex vector $\delta$, define the complex symmetric matrix

\[
T_\delta(v)=\left(1+\sum_j\delta_jv_j^2\right)D_\delta
 -(D_\delta v)(D_\delta v)^T.
\tag{5}
\]

Expanding the two-by-two minors gives

\[
D_1=r^*T_\beta(v)r.
\]

Complementary minors of a unitary matrix have equal squared moduli. Applying this to the two terms defining $D_0$ gives

\[
D_0=p_\beta s^*T_{1/\beta}(v)s.
\]

Consequently, with the following real symmetric compressions to $H$,

\[
M=\operatorname{Re}(\lambda_1T_\beta(v))|_H,\qquad
L=\operatorname{Re}(\lambda_0p_\beta T_{1/\beta}(v))|_H,
\tag{6}
\]

the left side of (3) is $r^*Mr+s^*Ls$. The remaining rows may be complex. A real positive semidefinite matrix is also positive semidefinite as a Hermitian matrix on the complexification, so a real matrix certificate for (6) controls these rows directly.

## 3. A sparse rank-one correction with an exact budget

Let $p_j=v_j^2$ and set

\[
K=\begin{pmatrix}
0&177/5&0&0\\-66&0&0&0\\0&0&0&0\\0&0&0&0
\end{pmatrix},\qquad y=PKv,
\tag{7}
\]

\[
\alpha=-456p_1+2525p_2+1330p_3+710p_4,
\tag{8}
\]

\[
\gamma=-1050p_1-\frac{23204}{25}p_2+1520p_3+2140p_4.
\tag{9}
\]

We will prove

\[
yy^T+\alpha I_H-M\succeq0,\qquad
yy^T+\gamma I_H-L\succeq0.
\tag{10}
\]

The objective identity is particularly simple:

\[
\boxed{\|y\|^2+\alpha+\gamma
 =2850-\frac{23409}{25}p_1p_2\le2850.}
\tag{11}
\]

Indeed, if $a=177/5$ and $b=-66$, then

\[
\|PKv\|^2=a^2p_2+b^2p_1-(a+b)^2p_1p_2,
\]

whereas $\alpha+\gamma=2850-b^2p_1-a^2p_2$.

Since $r,s,t$ are an orthonormal basis of $H_\mathbb C$, (10) implies

\[
\begin{aligned}
r^*Mr+s^*Ls
&\le\alpha+\gamma+|r^*y|^2+|s^*y|^2\\
&=\alpha+\gamma+\|y\|^2-|t^*y|^2\le2850.
\end{aligned}
\tag{12}
\]

It remains to establish the two matrix inequalities uniformly in $v$.

## 4. A reusable Gram criterion for orthogonal biquadratic slacks

For arbitrary $\delta\in\mathbb C^n$, $\kappa\in\mathbb C$, $c\in\mathbb R^n$, and a real matrix $K$ supported on $K_{12}=a,K_{21}=b$, consider

\[
\begin{aligned}
F(r,v)={}&(r^TKv)^2+(c\cdot v^2)\|r\|^2\\
&-\operatorname{Re}\!\left\{\kappa\left[
\left(\|v\|^2+\sum_j\delta_jv_j^2\right)\sum_i\delta_i r_i^2
-\left(\sum_i\delta_i r_iv_i\right)^2\right]\right\}.
\end{aligned}
\tag{13}
\]

For $\|v\|=1$ and $r^Tv=0$, this is the desired dual slack evaluated at $r$, with scalar $c\cdot v^2$. Define $z_{ij}=r_iv_j$ and $d_i=r_iv_i$. For $i\ne j$, put

\[
D_{ij}=c_j-\operatorname{Re}(\kappa\delta_i(1+\delta_j))
 +a^2\mathbf1_{(i,j)=(1,2)}+b^2\mathbf1_{(i,j)=(2,1)}.
\tag{14}
\]

Choose real numbers $t_{ij}=t_{ji}$ for the unordered pairs and define

\[
Q_{ij}=\begin{pmatrix}D_{ij}&t_{ij}\\t_{ij}&D_{ji}\end{pmatrix},
\tag{15}
\]

\[
G_{ii}=c_i-\operatorname{Re}(\kappa\delta_i),\qquad
G_{ij}=\operatorname{Re}(\kappa\delta_i\delta_j)
 +ab\mathbf1_{\{i,j\}=\{1,2\}}-t_{ij}.
\tag{16}
\]

**Gram criterion.** The following conditions suffice for $F(r,v)\ge0$ whenever $r^Tv=0$:

\[
Q_{ij}\succeq0\quad(i<j),\qquad G|_{\mathbf1^\perp}\succeq0.
\tag{17}
\]

The proof is the exact identity

\[
\boxed{F(r,v)=d^TGd+
\sum_{i<j}(z_{ij},z_{ji})Q_{ij}(z_{ij},z_{ji})^T.}
\tag{18}
\]

Each pair allocation cancels because $z_{ij}z_{ji}=d_id_j$. Orthogonality is exactly $\sum_i d_i=0$. Thus every term on the right is nonnegative under (17).

There is a useful completeness statement at the level of this certificate class. Conditions (17), with some choice of the pair parameters, are equivalent to a sum of squares of real bilinear forms **modulo the relation** $r^Tv=0$. To see this, average any such certificate over simultaneous sign changes $r_i,v_i\mapsto\epsilon_i r_i,\epsilon_i v_i$. The bilinear monomials split into the trivial-character space spanned by $d_i$ and, for each unordered pair, the character space spanned by $z_{ij},z_{ji}$. The averaged Gram matrix therefore splits into precisely these blocks. The coefficients of $z_{ij}^2$ fix their diagonal entries to (14); their off-diagonal entries are the parameters $t_{ij}$. The only remaining freedom on the diagonal-monomial block is a multiple of $(\sum d_i)(\sum c_i'd_i)$, which does not affect its restriction to $\mathbf1^\perp$. Conversely, a positive Gram form on $\mathbf1^\perp$ extends to a positive Gram form on the full diagonal space after such a modification. This proves the stated equivalence.

This is an equivalence for bilinear SOS certificates, not an assertion that every nonnegative orthogonal biquadratic is SOS.

## 5. The first exact slack

For $M$, take $\delta=\beta$, $\kappa=\lambda_1$, and

\[
c=(-456,2525,1330,710),\qquad
(t_{12},t_{13},t_{14},t_{23},t_{24},t_{34})
=(0,-2445,-9445,0,-1950,0).
\]

The pair blocks have the following entries.

| Pair | $D_{ij}$ | $D_{ji}$ | $t_{ij}$ | Determinant |
|---|---:|---:|---:|---:|
| 12 | $27954/25$ | $0$ | $0$ | $0$ |
| 13 | $6506$ | $919$ | $-2445$ | $989$ |
| 14 | $13506$ | $7919$ | $-9445$ | $17745989$ |
| 23 | $1366$ | $0$ | $0$ | $0$ |
| 24 | $3316$ | $1950$ | $-1950$ | $2663700$ |
| 34 | $0$ | $0$ | $0$ | $0$ |

All are positive semidefinite. The diagonal Gram is

\[
G_M=\begin{pmatrix}
2060&14198/5&-215&-835\\
14198/5&3801&1240&620\\
-215&1240&45&-575\\
-835&620&-575&-1195
\end{pmatrix}.
\tag{19}
\]

Substituting $d_4=-d_1-d_2-d_3$ yields the matrix

\[
\widetilde G_M=\begin{pmatrix}
2535&9298/5&0\\9298/5&1366&0\\0&0&0
\end{pmatrix}.
\tag{20}
\]

The determinant of its nonzero block is $117446/25>0$. This proves the first inequality in (10). Its zero mode is forced by the exposed $3421$–$4321$ block; it is not a numerical defect.

## 6. The reciprocal exact slack

For $L$, take $\delta=1/\beta$, $\kappa=\lambda_0p_\beta$, and

\[
c=(-1050,-23204/25,1520,2140),\qquad
(t_{12},t_{13},t_{14},t_{23},t_{24},t_{34})
=(0,340,0,0,0,-2538).
\]

The pair blocks are:

| Pair | $D_{ij}$ | $D_{ji}$ | $t_{ij}$ | Determinant |
|---|---:|---:|---:|---:|
| 12 | $0$ | $1531$ | $0$ | $0$ |
| 13 | $900$ | $400$ | $340$ | $244400$ |
| 14 | $1400$ | $0$ | $0$ | $0$ |
| 23 | $0$ | $26796/25$ | $0$ | $0$ |
| 24 | $0$ | $4296/25$ | $0$ | $0$ |
| 34 | $3524$ | $2624$ | $-2538$ | $2805532$ |

The diagonal Gram and its restriction are

\[
G_L=\begin{pmatrix}
-1600&-12807/5&-270&190\\
-12807/5&-73204/25&-480&140\\
-270&-480&3040&2674\\
190&140&2674&3380
\end{pmatrix},
\tag{21}
\]

\[
\widetilde G_L=\begin{pmatrix}
1400&2443/5&246\\
2443/5&4296/25&86\\
246&86&1072
\end{pmatrix}.
\tag{22}
\]

The three leading principal minors are

\[
1400,\qquad\frac{46151}{25},\qquad\frac{47478216}{25},
\]

all strictly positive. Thus $G_L|_{\mathbf1^\perp}$ is positive definite and the second inequality in (10) follows. Together with (11)–(12), this completes the proof of Theorem 1.

## 7. Complete equality classification

The exact support gap is a sum of four nonnegative terms:

\[
2850-r^*Mr-s^*Ls
=\frac{23409}{25}p_1p_2+|t^*y|^2
+r^*(yy^T+\alpha I-M)r+s^*(yy^T+\gamma I-L)s.
\tag{23}
\]

At equality, the reciprocal slack vanishes. The positive definiteness in (22), applied to real and imaginary parts of $s$, first forces $s_iv_i=0$ for every $i$. Its pair blocks then force all incidence products $s_iv_j$ to vanish except possibly

\[
s_1v_2,\qquad s_2v_3,\qquad s_2v_4,\qquad s_4v_1.
\tag{24}
\]

Because $s$ and $v$ are unit vectors, this leaves exactly three possibilities:

1. $v$ is supported on coordinate 1 and $s$ on coordinate 4.
2. $v$ is supported on coordinate 2 and $s$ on coordinate 1.
3. $v\in\operatorname{span}(e_3,e_4)$ and $s$ is supported on coordinate 2.

The $M$ slack in the first case forces $r$ onto coordinate 2; the remaining row is on coordinate 3. In the second case it forces $r$ onto coordinate 3 and the remaining row onto coordinate 4. These are the phased permutations $2143$ and $3214$.

In the third case, it forces $r\in\operatorname{span}(e_3,e_4)$ orthogonal to $v$. The remaining row is on coordinate 1. Thus the first two rows form a $U(2)$ block on columns 3 and 4, while rows 3 and 4 occupy columns 2 and 1. This is the block joining permutations $3421$ and $4321$.

Conversely, each of these patterns attains equality. For the block family, the value is the two-permutation convex combination, and both endpoint values are $2850$. This proves completeness for complex unitaries, with arbitrary row and column phases.

## 8. A local continuation theorem at this facet

The certificate supplies more than a fixed-parameter inequality.

**Theorem 2.** There is an open neighborhood of the pair (2) in

\[
\mathbb C^4_\beta\times\mathbb C^2_{(\lambda_0,\lambda_1)}
\]

on which, for every $U\in U(4)$,

\[
\operatorname{Re}(\lambda'_0D_0(U;\beta')+\lambda'_1D_1(U;\beta'))
\le\max_\pi\operatorname{Re}(\lambda'_0w_{\pi,0}(\beta')+
\lambda'_1w_{\pi,1}(\beta')).
\tag{25}
\]

This is a neighborhood of one direction as well as its spectrum; it does not assert the complete CH inclusion for every direction at nearby spectra.

Here are the needed quantitative details. Let $q_L(v,s)$ and $q_M(v,r)$ denote the two slack quadratic forms. From the positive blocks in Sections 5 and 6, there are constants $c_L,c_M>0$, independent of the unit rows, such that

\[
q_L(v,s)\ge c_L\left[1-|s_1|^2p_2-|s_2|^2(p_3+p_4)-|s_4|^2p_1\right],
\tag{26}
\]

\[
q_M(v,r)\ge c_M|r_1|^2.
\tag{27}
\]

To obtain (26), take the minimum of the positive eigenvalues of the strict pair blocks, of the positive entries in the one-entry blocks, and of a positive lower bound for the diagonal Gram on $\mathbf1^\perp$. It then controls the sum of the twelve forbidden $|s_iv_j|^2$. Their total is precisely the bracket. For (27), the strict two-dimensional diagonal block controls $r_1v_1$, while pair blocks $12,13,14$ control $r_1v_2,r_1v_3,r_1v_4$.

Near the $U(2)$ equality family, put $x=p_1+p_2$ and $z=1-|s_2|^2$. The allowed mass in (26) is at most

\[
(1-z)(1-x)+zx.
\]

For $x,z\le1/4$, the bracket in (26) is therefore at least $(x+z)/2$. Equations (23), (26), and (27) give a fixed positive multiple of

\[
p_1+p_2+(1-|s_2|^2)+|r_1|^2
\tag{28}
\]

as a lower bound on the support gap. This expression controls every matrix entry outside the specified block pattern. For example,

\[
|r_2|^2\le1-|s_2|^2,\qquad
1-|t_1|^2=|r_1|^2+p_1+|s_1|^2.
\]

In tubular coordinates around the compact block family, its off-block entries are a positive definite quadratic form in the normal tangent variables to second order. Thus (28) proves a uniform strictly negative support Hessian in every normal direction, including at the two endpoints of the block.

The two isolated phased-permutation families have the same property. Near $v=e_1,s=e_4$, (26) controls $1-p_1+1-|s_4|^2$, and the strict $M$ pair blocks $13,14$, together with (27), control $1-|r_2|^2$. Near $v=e_2,s=e_1$, (26) controls $1-p_2+1-|s_1|^2$, while the $M$ diagonal block and pair blocks $12,24$ control $1-|r_3|^2$. These quantities control the normal distances to the two phased permutations.

Two standard algebraic facts now finish the argument. First, for arbitrary perturbed spectra and coefficients, every stated block family satisfies the permutation support bound: its squared-minor profile is a convex combination of its one or two block-preserving permutations. Second, every perturbed objective has zero first derivative in directions normal to each block family. For the latter, at a block matrix, each nonzero minor is balanced across the block partition; an off-block first variation cannot change its determinant to first order. A zero minor has zero first derivative of its squared modulus. Summing the squared-minor terms proves the required identity.

By continuity, the strictly negative normal Hessian remains negative in a fixed tube around the base equality locus for sufficiently small parameter perturbations. The first derivative there remains identically zero. Taylor's formula therefore bounds every nearby value by the value at its projection onto a solved block family. On the complement of these tubes, compactness of $U(4)$ and the exact equality classification give a strictly positive base support gap. Uniform continuity preserves that gap after shrinking the parameter neighborhood. This proves (25).

## 9. What remains

The construction is adapted to one exposed facet. Its sparse $K$, affine scalar multipliers, and pair allocations have not been shown to exist for every actual facet. The Gram criterion converts that possible universal extension into explicit matrix inequalities, but it does not itself solve them. Theorem 2 rules out a first failure at this certified facet and its sufficiently small perturbations; it does not classify every possible noncommuting contact elsewhere.

No universal certificate for arbitrary actual CH facets is established here.

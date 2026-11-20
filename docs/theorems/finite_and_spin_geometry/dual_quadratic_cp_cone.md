# Quadratic positive-map certificates for actual complex CH facets

## Status and scope

This note proves a genuinely complex, fixed spectral support inequality uniformly over every complex unitary matrix of order four. The certificate has integer parameters, and its complete polynomial identities and positive semidefinite conditions are verified with rational arithmetic. 

The principal structural result is a 54-variable semidefinite feasibility formulation that is complete for a precisely defined class: real completely positive quadratic corrections, quadratic scalar multipliers, and bilinear sum-of-squares slacks modulo orthogonality. The scalar trace budget is represented exactly, rather than replaced by a stronger coefficientwise estimate. Universal feasibility of this formulation for all actual spectral facets remains open.

The fixed-chart quantifier matters. A proof of all facets for one fixed \(\beta\) would establish that complete CH inclusion in the chosen chart. It does not automatically establish MOC for every original first spectrum while keeping the original second spectrum fixed: the projective normalization of the first spectrum changes the second spectrum.

## 1. Actual unitary support and its fixed-row form

Write the rows of \(U\in U(4)\) as \(r,v,s,t\), in that order, and put \(\beta_J=\prod_{j\in J}\beta_j\). Define

\[
\begin{aligned}
D_1(U;\beta)&=\sum_j\beta_j|U_{1j}|^2+
 \sum_{|J|=2}\beta_J|\det U[12,J]|^2,\\
D_0(U;\beta)&=\sum_{|J|=3}\beta_J|\det U[124,J]|^2+
 \sum_{|J|=2}\beta_J|\det U[14,J]|^2.
\end{aligned}
\tag{1}
\]

For each permutation \(\pi\), the comparison point is

\[
w_\pi=\left(
\beta_{\pi(1)}(1+\beta_{\pi(2)})\beta_{\pi(4)},
\ \beta_{\pi(1)}(1+\beta_{\pi(2)})
\right).
\tag{2}
\]

For a complex direction \((\lambda_0,\lambda_1)\), let

\[
h=\max_\pi\operatorname{Re}(\lambda_0w_{\pi,0}+\lambda_1w_{\pi,1}).
\tag{3}
\]

Column phases preserve all squared minors, so make \(v\) real and unit. Set \(P=I-vv^T\), \(H=v^\perp\), \(p_j=v_j^2\), and \(p_\beta=\prod_j\beta_j\). The complex symmetric pencil

\[
T_\delta(v)=\left(1+\sum_j\delta_jv_j^2\right)D_\delta
 -(D_\delta v)(D_\delta v)^T
\tag{4}
\]

gives the real symmetric compressions

\[
M=\operatorname{Re}(\lambda_1T_\beta(v))|_H,\qquad
L=\operatorname{Re}(\lambda_0p_\beta T_{1/\beta}(v))|_H.
\tag{5}
\]

Expansion and complementary unitary minors give

\[
\operatorname{Re}(\lambda_0D_0+\lambda_1D_1)=r^*Mr+s^*Ls.
\tag{6}
\]

The remaining three rows may be complex. A real symmetric positive semidefinite certificate acts as a Hermitian certificate on their complexification.

Although reciprocal notation is convenient, the entries used below are polynomial in \(\beta\). The reciprocal one-body coefficients are
\(\operatorname{Re}(\lambda_0\prod_{k\ne i}\beta_k)\), and the distinct-index pair coefficients are
\(\operatorname{Re}(\lambda_0\prod_{k\notin\{i,j\}}\beta_k)\).
Thus zero spectral entries can be handled directly by cofactors.

## 2. A necessary endpoint graph for a single transport matrix

Consider a rank-one correction \(y(v)=PKv\), with a fixed real matrix \(K\), and arbitrary scalar functions \(\alpha(v),\gamma(v)\), required to obey

\[
yy^T+\alpha I_H\succeq M,\quad
yy^T+\gamma I_H\succeq L,\quad
\|y\|^2+\alpha+\gamma\le h.
\tag{7}
\]

At \(v=e_j\), both \(M,L\) are diagonal on \(j^\perp\). Write their \(i\)-th entries as \(m_{ij},\ell_{ij}\). If \(K_{ij}=0\), evaluation on \(e_i\) gives
\(\alpha\ge m_{ij}\), \(\gamma\ge\ell_{ij}\). Consequently

\[
m_{ij}+\ell_{ij}>h\quad\Longrightarrow\quad K_{ij}\ne0.
\tag{8}
\]

This elementary implication is independent of any SOS representation or assumed polynomial form for the scalar multipliers.

For the actual spectrum

\[
\beta=(-4+4i,\ 2i,\ -1-2i,\ 1-3i),
\tag{9}
\]

## 3. Shared positive corrections and complete positivity

A useful larger sufficient class replaces \(yy^T\) by any real \(Y(v)\succeq0\) on \(H\):

\[
Y+\alpha I_H\succeq M,\quad
Y+\gamma I_H\succeq L,\quad
\operatorname{tr}Y+\alpha+\gamma\le h.
\tag{10}
\]

Indeed, since \(r,s,t\) form an orthonormal basis of \(H_\mathbb C\),

\[
r^*Mr+s^*Ls
 \le\alpha+\gamma+r^*Yr+s^*Ys
 =\alpha+\gamma+\operatorname{tr}Y-t^*Yt\le h.
\tag{11}
\]

We choose

\[
Y(v)=P\left(\sum_\nu K_\nu vv^TK_\nu^T\right)P\bigm|_H.
\tag{12}
\]

Here completely positive refers to the matrix map
\(X\mapsto\sum_\nu K_\nu X K_\nu^T\); it does not mean that the Kraus matrices have nonnegative entries.

Average a putative certificate over simultaneous coordinate signs:
\(r_i,v_i\mapsto\epsilon_i r_i,\epsilon_i v_i\).
The Kraus representation splits into the trivial character, consisting of diagonal matrices, and six pair characters, one for each unordered pair \(\{i,j\}\).

The averaged correction before projection is exactly

\[
\begin{aligned}
S(v)={}&D_vRD_v\\
&+\sum_{i<j}\left[
x_{ij}p_j e_ie_i^T+x_{ji}p_i e_je_j^T+
\tau_{ij}v_iv_j(e_ie_j^T+e_je_i^T)
\right],
\end{aligned}
\tag{13}
\]

where

\[
R\succeq0,\qquad
\begin{pmatrix}x_{ij}&\tau_{ij}\\\tau_{ij}&x_{ji}\end{pmatrix}\succeq0.
\tag{14}
\]

All mixed character covariances average to zero. Conversely, factorizing the matrices in (14) reconstructs real Kraus matrices, so this representation is complete for the averaged quadratic map.

Adding a scalar multiple of the identity to a diagonal Kraus matrix does not change \(PK_\nu v\). We may therefore impose

\[
R\mathbf1=0,\quad R=ER_0E^T,\quad R_0\succeq0,\qquad
E=\begin{pmatrix}1&0&0\\0&1&0\\0&0&1\\-1&-1&-1\end{pmatrix}.
\tag{15}
\]

Averaging general real quadratic scalar multipliers likewise gives
\(\alpha=c\cdot p\), \(\gamma=d\cdot p\).

## 4. The exact bilinear Gram formulation

For one of the two pencils, write its data as \((\delta,\kappa,c)\) and define

\[
u_i=\operatorname{Re}(\kappa\delta_i),\qquad
q_{ij}=\operatorname{Re}(\kappa\delta_i\delta_j),\quad i\ne j.
\]

The first slack uses \((\beta,\lambda_1,c)\), and the second uses
\((1/\beta,\lambda_0p_\beta,d)\).

Choose six real allocation parameters \(t_{ij}\). Put

\[
D_{ij}=c_j-u_i-q_{ij}+x_{ij},\qquad
Q_{ij}=\begin{pmatrix}D_{ij}&t_{ij}\\t_{ij}&D_{ji}\end{pmatrix},
\tag{16}
\]

\[
G_{ii}=c_i-u_i+R_{ii},\qquad
G_{ij}=q_{ij}+R_{ij}+\tau_{ij}-t_{ij}.
\tag{17}
\]

For \(e_i=r_iv_i\), the homogeneous quartic slack equals

\[
F(r,v)=e^TGe+
 \sum_{i<j}(r_iv_j,r_jv_i)Q_{ij}(r_iv_j,r_jv_i)^T.
\tag{18}
\]

This is an identity: the pair allocation terms cancel by
\(r_iv_jr_jv_i=e_ie_j\).
The relation \(r^Tv=0\) is \(\sum_i e_i=0\). Consequently

\[
Q_{ij}\succeq0\quad\hbox{for every pair},\qquad E^TGE\succeq0
\tag{19}
\]

proves the slack.

These conditions are complete for bilinear SOS modulo \(r^Tv=0\). In detail, start with a certificate
\(F=\sum_\nu B_\nu(r,v)^2+(r^Tv)C(r,v)\), where all \(B_\nu,C\) are bilinear.
After sign averaging, the bilinear monomials split into the diagonal character space spanned by \(e_i\), and the six two-dimensional spaces spanned by \(r_iv_j,r_jv_i\).
Their diagonal coefficients are fixed by \(F\), and their off-diagonal coefficients are exactly the free \(t_{ij}\). The multiple of \(r^Tv\) only changes the diagonal-character Gram by a form vanishing on \(\mathbf1^\perp\).
Conversely, a positive form on \(\mathbf1^\perp\) extends to a positive form on all four coordinates after adding such a vanishing form.

This argument does not assert that every nonnegative orthogonal biquadratic is SOS.

## 5. The true scalar budget is a copositive four-by-four matrix

Define

\[
w_{ij}=x_{ij}+x_{ji}+2\tau_{ij},\qquad
\delta_{ij}=R_{ii}+R_{jj}-2R_{ij}.
\tag{20}
\]

Both are nonnegative, being quadratic evaluations of the PSD blocks.
Projection gives

\[
\operatorname{tr}Y=
\sum_j\left(\sum_{i\ne j}x_{ij}\right)p_j+
\sum_{i<j}(\delta_{ij}-w_{ij})p_ip_j.
\tag{21}
\]

Let

\[
g_j=h-c_j-d_j-\sum_{i\ne j}x_{ij}.
\]

The exact budget defect is

\[
h-\operatorname{tr}Y-\alpha-\gamma
 =\sum_jg_jp_j+\sum_{i<j}(w_{ij}-\delta_{ij})p_ip_j=p^TBp,
\tag{22}
\]

where

\[
B_{ii}=g_i,\qquad
B_{ij}=\frac{g_i+g_j+w_{ij}-\delta_{ij}}2.
\tag{23}
\]

Because \(p\) ranges over the simplex, this budget is equivalent to
\(B\in\operatorname{COP}_4\), the copositive cone.

Diananda's theorem gives
\(\operatorname{COP}_4=\mathcal S_+^4+\mathcal N^4\), where \(\mathcal N^4\) is the cone of entrywise nonnegative symmetric matrices.
A primary research paper explicitly recalls this dimension-four theorem: Dickinson, Dür, Gijben and Hildebrand, “Irreducible elements of the copositive cone,” Section 1, available at
https://optimization-online.org/wp-content/uploads/2012/03/3383.pdf .
The original source is P. H. Diananda, “On non-negative forms in real variables some or all of which are non-negative,” Mathematical Proceedings of the Cambridge Philosophical Society 58 (1962), 17–25, DOI 10.1017/S0305004100036185.

Thus the budget is represented exactly by a symmetric matrix \(T\) satisfying

\[
T\succeq0,\qquad B-T\ge0\quad\hbox{entrywise}.
\tag{24}
\]

It is unnecessary to force all four \(g_j\) to zero. That restriction discards valid budget.

## 6. The 54-variable equivalence theorem

For each fixed actual \((\beta,\lambda_0,\lambda_1,h)\), impose:

- \(R_0\succeq0\), the six correction blocks (14);
- the twelve pair slack blocks and the two diagonal restrictions in (19);
- the budget block and ten entrywise constraints in (24).

The variables are \(c,d\) (eight), directed \(x_{ij}\) (twelve), \(\tau_{ij}\) (six),
the two sets of \(t_{ij}\) (twelve), \(R_0\) (six), and \(T\) (ten): 54 in total.

**Theorem.** These affine semidefinite constraints are feasible if and only if there exists a real quadratic CP correction (12), real quadratic scalar multipliers, bilinear SOS certificates for both slacks modulo orthogonality, and the exact scalar trace budget, uniformly over real unit \(v\).

The forward implication follows from (13)–(24). The reverse follows by simultaneous-sign averaging, diagonal-Kraus gauge reduction, the character decomposition of the SOS Grams, and Diananda's exact description of \(\operatorname{COP}_4\).

Feasibility therefore proves the actual complex unitary inequality (6) for every \(U\).
The theorem describes the certificate search exactly; it does not assert universal feasibility for every actual spectral direction.

## 7. Parameters for the integer certificate

Consider (9) and

\[
\lambda_0=287+91i,\qquad
\lambda_1=772+2546i,\qquad h=11100.
\tag{25}
\]

## 8. An integer certificate for the actual facet

**Theorem.** For (9) and (25), every \(U\in U(4)\) satisfies

\[
\boxed{\operatorname{Re}\big((287+91i)D_0+(772+2546i)D_1\big)\le11100.}
\tag{28}
\]

Use

\[
c=(-808,8564,438,-6417),\quad
d=(-2501,-1400,3115,4411),
\]

\[
X=(x_{ij})=
\begin{pmatrix}
0&0&0&35\\
10201&0&7525&8472\\
4208&3936&0&3073\\
0&0&22&0
\end{pmatrix},
\]

\[
\tau=(0,0,0,-1831,0,-76),\quad
t^M=(-12,0,-20551,0,270,0),\quad
t^L=(0,-344,-988,0,0,-6405),
\tag{29}
\]

in pair order \(12,13,14,23,24,34\), and

\[
R_0=
\begin{pmatrix}
1429&-2200&-585\\
-2200&4372&-238\\
-585&-238&1588
\end{pmatrix}.
\tag{30}
\]

The leading principal minors of \(R_0\) are \(1429,1407588,45485768\).
All are positive.

The eighteen pair blocks are specified in the following table. Each triple means
\(\begin{psmallmatrix}a&t\\t&b\end{psmallmatrix}\).

| Pair | Correction \((a,b,t)\) | First slack \((a,b,t)\) | Reciprocal slack \((a,b,t)\) |
|---|---|---|---|
| 12 | \((0,10201,0)\) | \((7644,293,-12)\) | \((0,0,0)\) |
| 13 | \((0,4208,0)\) | \((14630,0,0)\) | \((875,10807,-344)\) |
| 14 | \((35,0,0)\) | \((41450,25342,-20551)\) | \((2416,649,-988)\) |
| 23 | \((7525,3936,-1831)\) | \((4875,0,0)\) | \((0,12336,0)\) |
| 24 | \((8472,0,0)\) | \((7607,614,270)\) | \((3,0,0)\) |
| 34 | \((3073,22,-76)\) | \((286,0,0)\) | \((19692,9185,-6405)\) |

The diagonal restrictions are

\[
G_M^{\mathrm{red}}=
\begin{pmatrix}
25715&13837&6455\\
13837&9872&4082\\
6455&4082&1804
\end{pmatrix},
\quad
G_L^{\mathrm{red}}=
\begin{pmatrix}
1114&1114&3863\\
1114&1114&3863\\
3863&3863&17585
\end{pmatrix}.
\tag{31}
\]

The first has leading principal minors
\(25715,62395911,1934209924\), hence is positive definite.
The second has kernel \((1,-1,0)\) and a positive rank-two restriction, since
\(1114\cdot17585-3863^2=4666921>0\).

For the budget, take \(T=0\) and

\[
B=
\begin{pmatrix}
0&0&21/2&1501/2\\
0&0&1363/2&415/2\\
21/2&1363/2&0&4\\
1501/2&415/2&4&1526
\end{pmatrix}.
\tag{32}
\]

Its entries are nonnegative. The exact defect is

\[
21p_1p_3+1501p_1p_4+1363p_2p_3+
415p_2p_4+8p_3p_4+1526p_4^2.
\tag{33}
\]

Equations (29)–(33) verify every constraint of the theorem in Section 6, proving (28).

The four exposed permutations are

\[
3124,\quad3214,\quad3241,\quad4321.
\tag{34}
\]

Their real coordinate vectors \((\Re w_0,\Im w_0,\Re w_1,\Im w_1)\) are respectively

\[
(17,-31,11,2),\quad(-9,-13,3,-4),\quad
(4,28,3,-4),\quad(32,-16,-6,-2).
\]

The first three columns of their difference matrix have determinant \(25460\ne0\).
All other support values are smaller than \(11100\), so this is a genuine facet of the full four-dimensional hull.

The proof uses the displayed exact numbers, not a numerical feasibility tolerance.
The displayed integer parameters satisfy every certificate condition exactly.

## 9. Explicit conversion back to one rank

A higher-rank shared correction need not remain higher rank in the final dual.

**Spectral clipping lemma.** Let \(Y\succeq0\) on a three-dimensional real space, with eigenvalues
\(\mu_1\ge\mu_2\ge\mu_3\ge0\) and orthonormal eigenvectors \(u_1,u_2,u_3\).
Suppose (10) holds. Define

\[
\widehat y=\sqrt{\mu_1-\mu_2}\,u_1,\qquad
\widehat\alpha=\alpha+\mu_2,\qquad
\widehat\gamma=\gamma+\mu_2.
\tag{35}
\]

Then

\[
\widehat y\widehat y^T+\widehat\alpha I-(Y+\alpha I)
=(\mu_2-\mu_3)u_3u_3^T\succeq0,
\tag{36}
\]

and likewise for the second slack. Moreover,

\[
\|\widehat y\|^2+\widehat\alpha+\widehat\gamma
=\operatorname{tr}Y+\alpha+\gamma-\mu_3\le h.
\tag{37}
\]

This proves an explicit direction-dependent rank-one certificate at every anchor \(v\) from the integer quadratic CP certificate. It requires only a three-by-three real eigendecomposition. It does not require a fixed linear formula \(\widehat y=PKv\), so no fixed linear transport matrix is required.

The same clipping domination holds in higher dimension by replacing every lower eigenvalue by \(\mu_2\); its objective is \(\alpha+\gamma+\mu_1+\mu_2\le\alpha+\gamma+\operatorname{tr}Y\).

## 10. Equality and a local open neighborhood

The support gap has the exact decomposition

\[
h-r^*Mr-s^*Ls
=p^TBp+t^*Yt+
r^*(Y+\alpha I-M)r+s^*(Y+\gamma I-L)s.
\tag{38}
\]

Each term is nonnegative.

The positive definite first diagonal Gram forces \(r_iv_i=0\) for all \(i\), even for complex \(r\), by applying it to real and imaginary parts.
Its pair blocks then allow only the incidence products

\[
r_3v_1,\quad r_3v_2,\quad r_4v_3.
\]

Since \(r,v\) are unit, there are two alternatives.

1. \(v\in\operatorname{span}(e_1,e_2)\), \(r=e_3\), up to row phases.
   The reciprocal slack then forces \(s_4v_1=0\).
   If \(v_1\ne0\), the rows \(v,s\) form a unitary two-by-two block in columns 1,2 and \(t=e_4\).
   If \(v=e_2\), the rows \(s,t\) form a unitary two-by-two block in columns 1,4.

2. \(v=e_3\), \(r=e_4\). The reciprocal pair 13 forces \(s=e_2\), and then \(t=e_1\).

Direct substitution makes the other terms in (38) zero. This is the complete equality set: the \(3124\)–\(3214\) block, the \(3214\)–\(3241\) block, and the phased permutation \(4321\).

The two continuous branches intersect at \(3214\). They are both contained in the larger proper block family
\(\mathcal S=\{U:|U_{13}|=1\}\), consisting of one fixed row and a remaining \(U(3)\) block.
Use this larger family for continuation; treating the two small branches separately would obscure their intersection.

Here are quantitative reasons that local continuation is valid.

Near the two continuous equality branches, \(p_1+p_2\ge1/2\).
The strictly positive first-slack diagonal form and the strictly positive pair blocks 12,14,24 give a uniform constant \(a>0\) with

\[
r^*(Y+\alpha I-M)r\ge
a(p_1+p_2)(|r_1|^2+|r_2|^2+|r_4|^2)
\ge\frac a2(1-|r_3|^2).
\tag{39}
\]

The right side is comparable to squared distance from \(\mathcal S\).
Near \(4321\), where \(p_3,|r_4|^2\) are bounded below, the same slack controls
\(1-p_3\) and \(1-|r_4|^2\). The reciprocal slack controls
\(p_3(1-|s_2|^2)\): pair blocks 13,34 control \(s_1,s_4\), and its diagonal restriction controls \(s_3v_3\).
Together these quantities control squared distance from the phased permutation.

Every normal first derivative vanishes on these block families for every spectral parameter.
For each squared minor separately, a minor that is nonzero on a block matrix has no first-order determinant term from an off-block perturbation: a balanced minor needs two cross-block transitions.
A minor that is zero has zero first derivative of its squared modulus automatically.
Thus the negative normal Hessians obtained from (39) persist under small changes of the complex spectra and direction.

On \(\mathcal S\), all squared minors reduce to minors of a three-by-three unitary block.
Sizes one and two are complementary, so a doubly stochastic matrix and Birkhoff decomposition give a common permutation law there. Consequently the support inequality holds on \(\mathcal S\) for every parameter, as it does at every phased permutation.

Finally, take a finite tubular cover of the compact equality set by neighborhoods where these negative normal Hessians persist. On the compact complement the base support gap has a strictly positive minimum; continuity preserves it under a uniform small parameter change.
Inside the tubes, the perturbed value is no larger than its value on the relevant proper block family, already bounded by the perturbed permutation height.

Therefore (28) holds in an open neighborhood of this particular complex support instance \((\beta,\lambda_0,\lambda_1)\).
This is local stability of one support inequality. It does not certify every direction for a nearby spectrum, and it does not exclude a first noncommuting contact elsewhere in parameter space.

## 11. A strict dual kernel and absence of weak infeasibility

There is a universal rational interior dual vector for the 54-variable block map.

Use the following positive definite weights:

- for \(R_0\), \(4(I_3+J_3)\);
- for each correction or slack pair block, \(\begin{psmallmatrix}5&-1\\-1&5\end{psmallmatrix}\);
- for each three-by-three diagonal slack restriction, \(4I_3-J_3\);
- for the budget block \(T\), \(6I_4+3J_4\);
- for the ten entrywise budget constraints, weight 9 on diagonal positions and 6 on off-diagonal positions.

Their total pairing with the affine block map annihilates all 54 variable directions exactly. The verification is in strict_haar_kernel() in the exact certificate script. At (25), its constant pairing is \(1204524\).

The coefficients arise from 72 times the Haar moments of two orthogonal real unit vectors:
\(\mathbb E(r_i^2v_j^2)=5/72\) for \(i\ne j\),
\(\mathbb E(r_iv_jr_jv_i)=-1/72\), and
\(\mathbb E(r_i^2v_i^2)=3/72\).
The simplex moments are
\(\mathbb E(p_i^2)=9/72\) and
\(\mathbb E(p_ip_j)=3/72\).
The annihilation itself is purely algebraic and independent of probabilistic interpretation.

The independent reviewer identified a useful exact interpretation of the constant:

\[
\langle Z_0,C\rangle
=72\left(h-\frac1{24}\sum_\pi
 \operatorname{Re}(\lambda_0w_{\pi,0}+\lambda_1w_{\pi,1})\right).
\tag{39a}
\]

Indeed, with \(e_k(\delta)\) denoting elementary symmetric polynomials,
\(\mathbb E_v\operatorname{tr}_{v^\perp}T_\delta(v)
=(3e_1(\delta)+2e_2(\delta))/4\).
The remaining row has conditional mean quadratic form equal to one third of this trace.
The resulting mean is exactly the permutation mean from (2).
The correction and multiplier contributions cancel between the two slack expectations and the budget expectation.

Every weight block has smallest eigenvalue at least one. Hence for any feasible certificate the sum of the traces of all 32 PSD blocks is at most the constant in (39a).
The affine block map is injective: \(R_0,X,\tau,t^M,t^L,T\) are read directly from block entries, and each \(c_j,d_j\) is then recovered from a pair diagonal.
Consequently the entire feasible 54-parameter set is compact, with explicit bounds obtained from that constant and the fixed spectral coefficients.
This strengthens boundedness modulo the affine kernel to actual boundedness of all parameters.

**No weak infeasibility.** Let the affine image be \(C+\mathcal L\) and the product PSD cone be \(\mathcal K\). The strict dual vector \(Z_0\in\operatorname{int}\mathcal K\) annihilates \(\mathcal L\).
If a sequence in \(C+\mathcal L\) approaches \(\mathcal K\), choose nearby \(P_n\in\mathcal K\).
Their pairings \(\langle Z_0,P_n\rangle\) stay bounded, so \(P_n\) stays bounded because \(Z_0\) is strictly positive in every block.
A convergent subsequence lies both in the cone and in the closed affine image.
Thus arbitrarily accurate feasibility implies actual feasibility.

For rational spectral data, any infeasible instance therefore has a rational strict separator. Strong separation gives a PSD separator with negative constant pairing. Add a sufficiently small rational multiple of \(Z_0\), then approximate inside the rational annihilator subspace. Strict positivity and the negative pairing survive. This does not assert that every feasible rational instance has a rational primal solution.

## Reproducible files

The complete exact verifiers and data are:

- code/theorems/finite_and_spin_geometry/dual_full_quadratic_exact_certificate.py.

Verification uses standard-library rational arithmetic. Universal feasibility of the 54-variable formulation for actual spectral facets remains unproved.
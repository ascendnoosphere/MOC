## 1. Which scalar inequality is actually missing?

Write
\[
c_\pi=\Re\!\left(\eta\prod_i(a_i+b_{\pi(i)})\right),\quad
h=\max_\pi c_\pi,\quad g_\pi=h-c_\pi.
\]

There are two different obligations.

### The one-parameter circle

For the source’s \(J\) and \(U(r)=(rI+J)/\sqrt{r^2+3}\),
\[
h-F(U(r))=\frac{Ar^4+Tr^2-Kr+D}{(r^2+3)^2}.
\]
The **weakest scalar condition** for both signs of \(r\) is
\[
\boxed{|K|\le
\inf_{r>0}\left(Ar^3+Tr+\frac Dr\right).}
\tag{1}
\]
Thus \(K^2\le4TD\) is generally stronger than necessary when \(A>0\), as the source explicitly notes.

At a supporting identity permutation, however, \(A=0\), and the established identities already give
\[
D\ge T,\qquad |K|\le2T.
\]
Therefore (1), whose right side is \(2\sqrt{TD}\), is automatic. **There is no remaining circle-budget gap at that supporting base.**  
Source: `organized/extracted/embedded/record/research/moc1000/direct_isoclinic_v4_geometry.md:59` and `organized/extracted/embedded/record/research/moc1000/direct_isoclinic_v4_geometry.md:222`.

### The full complex two-plane update

For an isometry \(Y:\mathbb C^2\to\mathbb C^4\), put
\[
P=YY^*,\quad R=I-2P,\quad
U_Y(V)=I+Y(V-I)Y^*.
\]
Retain the essential hypothesis
\[
\boxed{F(I)=h.}
\tag{2}
\]
Define
\[
\delta_{ij}=g_{(ij)},\qquad
\mathcal A(T)=\sum_{i<j}\delta_{ij}|y_iTy_j^*|^2,
\]
and
\[
s_{ijk}=c_{(ijk)}-c_{(ikj)},\qquad
\ell(T)=4\sum_{i<j<k}s_{ijk}C_{ijk}(T).
\]
The Plücker identity gives
\[
C_{ijk}(T)
=-\Im\!\left(p_{ik}\overline{p_{ij}}\,y_jTy_k^*\right).
\]

Let \(g_R=h-F(R)\). The exact Cayley numerator is
\[
[h-F(U_Y(V(T)))]\det(I+T^2)
=4\mathcal A(T)-2\det(T)\ell(T)+g_R\det(T)^2.
\tag{3}
\]
The kernel condition is already established. Hence the weakest remaining scalar obligation for this **fixed full plane**, equivalently the optimized-flow budget, is
\[
\boxed{E:=\frac14\ell^T\mathcal A^+\ell
      =4C_{\min}\le g_R.}
\tag{4}
\]
Sources: `organized/extracted/embedded/record/research/moc200/continuous_spectral_rank_two_budget.md:117–140`, `organized/extracted/embedded/record/research/moc200/continuous_spectral_rank_two_budget.md:144–204`.

The zero-contact theorem proves compatibility at \(g_R=0\), not (4) for positive gaps. Moreover, the universal coefficient one cannot be improved.  
Sources: `organized/extracted/embedded/record/research/moc1000/direct_zero_gap_reflections.md:391–398` and `organized/extracted/embedded/record/research/moc1000/direct_sharp_energy_constant.md:79–83`.

The calculation below attacks **(4)** directly.

## 2. New theorem: a whole complex spectral slice

Take
\[
J=\begin{pmatrix}
0&-1&-1&-1\\
1&0&-1&1\\
1&1&0&-1\\
1&-1&1&0
\end{pmatrix},\qquad
P=\frac12\left(I+\frac{iJ}{\sqrt3}\right),
\qquad R=-\frac{iJ}{\sqrt3}.
\tag{5}
\]
Here \(P\) is a rank-two orthogonal projection. Choose any \(Y\) with \(YY^*=P\).

**Theorem — proved by the exact certificate below.** For
\[
a=(0,\tfrac12,1,z),\quad b=(i,-i,1+i,-1+2i),
\]
every \(z,\eta\in\mathbb C\) satisfying (2) obeys
\[
\boxed{E\le\kappa_*g_R.}
\tag{6}
\]
The constant \(\kappa_*\) is sharp for these fixed spectral positions and this plane. In particular,
\[
\boxed{F(U_Y(V))\le h\quad\text{for every }V\in U(2).}
\tag{7}
\]

This plane is neither coordinate-containing nor gauge-real:
\[
P_{ii}=\tfrac12,\qquad
P_{12}P_{23}P_{31}=-\frac{i}{24\sqrt3}\ne0.
\]
The latter product is invariant under diagonal row phases; its nonreal value rules out making \(P\) real by those phases.

Up to an irrelevant scalar phase, the familiar \(U(r)\) lies in this orbit with scalar \(V\). Thus (7) controls substantially more motion than the already-settled supporting-base circle.

## 3. Executed proof

### A. Retain actual complex products in four real coordinates

Set \(w=\eta z\), and define
\[
P_\pi=\prod_{i=1}^{3}(a_i+b_{\pi(i)}),\qquad
Q_\pi=b_{\pi(4)}P_\pi.
\]
Then
\[
c_\pi=\Re(wP_\pi+\eta Q_\pi)=v_\pi\cdot\theta,
\]
where
\[
v_\pi=(\Re P_\pi,-\Im P_\pi,\Re Q_\pi,-\Im Q_\pi),
\quad
\theta=(\Re w,\Im w,\Re\eta,\Im\eta).
\]
For \(\eta\ne0\), every such pair \((w,\eta)\) is realized by the finite actual eigenvalue \(z=w/\eta\). We also include the harmless closure \(\eta=0\).

Because the height is fixed by the supporting identity, the relevant cone is only four-dimensional:
\[
\mathcal C=\{\theta:(v_e-v_\pi)\cdot\theta\ge0
                    \text{ for all }\pi\}.
\tag{8}
\]
This is **not** the arbitrary common-minor deficit cone: all its costs retain the displayed complex-product coefficients.

### B. Plücker computation and exact flow optimization

Use the raw frame
\[
K=P[:,\{1,2\}],\qquad G=K^*K,\qquad \det G=\tfrac16,
\]
and write
\[
T=G^{1/2}SG^{1/2},\qquad
S=\begin{pmatrix}s&x+i\sqrt3\,v\\x-i\sqrt3\,v&t\end{pmatrix},
\quad u=(s,t,x,v)^T.
\]
Then \(y_iTy_j^*=K_iSK_j^*\).

Direct expansion gives
\[
\mathcal A=\frac1{144}u^TMu,\qquad
\ell=\frac1{12\sqrt3}q^Tu,
\tag{9}
\]
where \(M\) is specified by the following six quadratic forms:
\[
\begin{array}{c|l}
ij&u^TM_{ij}u\\ \hline
12&3(s+t-4v)^2+4x^2\\
13&(t+x-3v)^2+3(s+x-v)^2\\
14&(t-x-3v)^2+3(s-x-v)^2\\
23&(s+x-3v)^2+3(t+x-v)^2\\
24&(s-x-3v)^2+3(t-x-v)^2\\
34&(s-t)^2+12v^2
\end{array}
\]
and
\[
M=\sum_{i<j}\delta_{ij}M_{ij}.
\]
The Plücker cubic yields
\[
q=
s_{123}\!\begin{pmatrix}-1\\-1\\-2\\4\end{pmatrix}
+s_{124}\!\begin{pmatrix}1\\1\\-2\\-4\end{pmatrix}
+s_{134}\!\begin{pmatrix}-1\\1\\0\\-2\end{pmatrix}
+s_{234}\!\begin{pmatrix}-1\\1\\0\\2\end{pmatrix}.
\tag{10}
\]
Consequently, the **optimized**, not prescribed-triangle, energy is
\[
\boxed{E=\frac1{12}q^TM^+q.}
\tag{11}
\]

All nine derangement terms of \(\det((a_i+b_j)R_{ij})\) have coefficient \(1/9\). Therefore, with \(D=\sum_{\pi\text{ derangement}}g_\pi\),
\[
\boxed{g_R=D/9.}
\tag{12}
\]
Thus (6) becomes the concrete rational matrix inequality
\[
\boxed{
H_{\kappa_*}:=
\begin{pmatrix}
M&q\\q^T&4\kappa_*D/3
\end{pmatrix}\succeq0.
}
\tag{13}
\]
Crucially, this matrix is **linear in \(\theta\)**. Checking it on the extreme rays of (8) proves it throughout that cone, including singular \(M\).

### C. Complete, bounded extreme-ray enumeration

For integral arithmetic, use
\[
V_\pi=2v_\pi,\qquad d_\pi=V_e-V_\pi.
\]
The table below uses scaled deficits \(\Delta_\pi=d_\pi\cdot\theta=2g_\pi\); this doubles \(E\) and \(g_R\), leaving their ratio unchanged.

Two exact checks establish the necessary cone geometry:

* The determinant of rows \(d_1,d_2,d_3,d_4\), with permutations in zero-based lexicographic order, is \(450\). Hence the cone is pointed.
* The vector \((137,83,-292,19)\) has minimum slack \(262\) over all 23 nonidentity inequalities. Hence the cone is full-dimensional.

Every extreme ray therefore has three independent active inequalities. I enumerated **all**
\[
\binom{23}{3}=1771
\]
triples, formed their four signed \(3\times3\) cofactors, tested both orientations against every inequality, and removed proportional duplicates. Exactly the following 14 primitive rays resulted:

| Primitive \(\theta\) | Exact \(E/g_R\) |
|---|---:|
| \((-15,10,-102,-4)\) | \(63043861/407853930\) |
| \((-14,2,-64,-23)\) | \(87199870553/358964577972\) |
| \((-7,1,-41,-7)\) | \(1182610081/7787416626\) |
| \((-1,1,-5,-1)\) | \(92815/340389\) |
| \((-1,2,-6,0)\) | \(5711267/22868550\) |
| \((0,0,-4,-3)\) | \(809/6160\) |
| \((0,0,-1,0)\) | \(59107/576675\) |
| \((1,3,-9,-5)\) | \(38989/389785\) |
| \((7,-1,-19,-13)\) | \(44699/386529\) |
| \((7,11,-3,5)\) | \(431071/6636350\) |
| \((9,7,-1,5)\) | \(2837641/15900725\) |
| \((31,17,-7,11)\) | \(604954/3109509\) |
| \((35,-5,-17,13)\) | **\(6770480971/24450277995\)** |
| \((85,35,-13,41)\) | \(25034360969/103763644677\) |

The tenth and eleventh rays have \(\operatorname{rank}M=3\); all others have rank four. In every case \(q\in\operatorname{range}M\).

As an independent singularity-safe verification, I checked **all 31 nonempty principal minors** of (13) on each ray: **434 exact rational checks**, all nonnegative, with nine zero minors.

Since a pointed polyhedral cone is generated by its extreme rays, linearity of (13) now proves (6) throughout \(\mathcal C\). No imported 82-ray completeness theorem, floating-point hull computation, or sampling argument enters this certificate.

Finally, (6) implies (4), and (3) proves (7) on the Cayley chart. Continuity includes all of \(U(2)\).

## 4. Actual positive-gap sharpness model

The maximizing ray is realized by
\[
\boxed{
z=\frac{-330-185i}{229},\qquad \eta=-17+13i.
}
\]
Direct multiplication gives \(h=143\). Its 24 permutation deficits, in lexicographic order, are
\[
\begin{aligned}
(&0,130,0,263,142,275,78,120,104,33,113,0,\\
 &13,275,39,55,323,77,133,353,114,0,389,55).
\end{aligned}
\]
Thus the required supporting-base hypothesis is explicitly verified.

The direct determinant evaluation and optimized energy are
\[
g_R=\frac{506}{3}>0,\qquad
E=\frac{13540961942}{289924245},
\]
so
\[
\frac{E}{g_R}=\kappa_*.
\]
Here
\[
(s_{123},s_{124},s_{134},s_{234})=(-91,353,59,-121),
\]
and (10) gives
\[
q=(506,382,-524,-2136)^T\ne0.
\]
This is genuinely a **positive-gap, nonzero-cubic** case—not the zero-contact theorem or a cycle-reversible degeneration.

I also independently differentiated the actual determinant at \(R\) and checked its agreement with the endpoint-gradient formula for \(\ell\).


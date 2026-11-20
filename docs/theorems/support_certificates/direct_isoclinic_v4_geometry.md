# Direct isoclinic attacks 019–021: singlets, four base permutations, and the remaining spectral constraint

## Outcome

Three further direct analytic investigations produced an exact spectral
formula for the isoclinic cubic term, a proof of the budget on large
regions of the support cone, a finite actual equality example proving the
coefficient four is sharp, and a uniform actual spectral support family
inside the region not covered by the elementary argument.

The universal inequality \(K^2\le4TD\) is **not proved**. The remaining
region and an exact obstruction to a proof using only the common-minor
linear relations are given below. These are three completed investigations,
bringing the direct track to 21; no additional requested rounds are counted.

All polynomial and finite identities in this note are checked with exact
rational arithmetic in `direct_isoclinic_v4_exact.py`, with results in
`direct_isoclinic_v4_exact.json`.

## 1. Definitions

Let

\[
z_\pi=\prod_{i=1}^4(a_i+b_{\pi(i)}),\quad
c_\pi=\operatorname{Re}(\eta z_\pi),\quad
h=\max_\pi c_\pi,\quad g_\pi=h-c_\pi.
\]

Use

\[
J=\begin{pmatrix}
0&-1&-1&-1\\1&0&-1&1\\1&1&0&-1\\1&-1&1&0
\end{pmatrix},\qquad
U(r)=\frac{rI+J}{\sqrt{r^2+3}}.
\]

For a three-cycle \(\pi\), set
\(\epsilon_\pi=\prod_{\pi(i)\ne i}J_{i,\pi(i)}\). Define

\[
A=g_e,\quad
T=\sum_{\text{six transpositions}}g_\pi,\quad
D=\sum_{\text{nine derangements}}g_\pi,\quad
K=-\sum_{\text{eight three-cycles}}\epsilon_\pi g_\pi.
\tag{1}
\]

The established exact support identity is

\[
h-c(U(r))=
\frac{Ar^4+Tr^2-Kr+D}{(r^2+3)^2}.
\tag{2}
\]

Thus the sufficient inequality being attacked is \(K^2\le4TD\).
It is stronger than nonnegativity of (2) when \(A>0\).

## 2. Investigation 019: the cubic term is a two-dimensional determinant

Define the two paired-difference coordinates

\[
P(a)=(a_1-a_2)(a_3-a_4),\qquad
Q(a)=(a_1-a_3)(a_2-a_4),
\]

and similarly for \(b\). The third pairing is their difference, by the
Plücker identity. Exact expansion gives

\[
\boxed{
\sum_{\text{three-cycles}}\epsilon_\pi z_\pi
=2\,[P(a)Q(b)-Q(a)P(b)].}
\tag{3}
\]

Consequently

\[
\boxed{
K=2\operatorname{Re}\!\left(
\eta\det\begin{pmatrix}P(a)&Q(a)\\P(b)&Q(b)\end{pmatrix}
\right).}
\tag{4}
\]

The verifier expands the eight matching products and checks every
coefficient in all eight spectral variables. The resulting polynomial
has 24 nonzero monomials, all of degree two in each spectrum. Thus the
orientation term uses only the two-dimensional paired-difference sector;
all one-versus-three degree contributions cancel exactly.

### An explicit formula linking the determinant to all four Klein-group values

To inspect the remaining compatibility, write the spectra in Walsh form:

\[
a_i=\alpha+\sigma_i\cdot X,\qquad
b_i=\beta+\sigma_i\cdot Y,
\]

where

\[
\sigma_1=(1,1,1),\quad\sigma_2=(1,-1,-1),\quad
\sigma_3=(-1,1,-1),\quad\sigma_4=(-1,-1,1),
\]

and \(X,Y\in\mathbb C^3\), \(s=\alpha+\beta\). These are coordinates
for arbitrary spectra, with no reality or symmetry assumption.
Put \(S_X=\sum_iX_i^2\), \(S_Y=\sum_iY_i^2\), and

\[
H_0(X)=\sum_iX_i^4-2\sum_{i<j}X_i^2X_j^2.
\]

For the four permutations in
\(V_4=\{e,(12)(34),(13)(24),(14)(23)\}\), their products are exactly

\[
\boxed{z_\epsilon=M+\sum_{i=1}^3\epsilon_iL_i,
\qquad \epsilon_i\in\{1,-1\},\quad\epsilon_1\epsilon_2\epsilon_3=1,}
\tag{5}
\]

with

\[
\begin{aligned}
M={}&s^4-2s^2(S_X+S_Y)+8s(X_1X_2X_3+Y_1Y_2Y_3)\\
&+H_0(X)+H_0(Y)-2S_XS_Y+8\sum_iX_i^2Y_i^2,
\end{aligned}
\tag{6}
\]

and, for \(\{i,j,k\}=\{1,2,3\}\),

\[
\begin{aligned}
L_i={}&4X_iY_i\,[2(X_i^2+Y_i^2)-S_X-S_Y-s^2]\\
&+8s(Y_iX_jX_k+X_iY_jY_k)-8X_jX_kY_jY_k.
\end{aligned}
\tag{7}
\]

All four identities are verified coefficient by coefficient. The other
20 products follow by permuting the three coordinates of \(Y\) before
applying (5). Thus the full spectral support maximum is the maximum over
six real tetrahedra:

\[
h=\max_{\rho\in S_3}\left[
\operatorname{Re}(\eta M_\rho)+
\max_{\epsilon_1\epsilon_2\epsilon_3=1}
\sum_i\epsilon_i\operatorname{Re}(\eta L_{i,\rho})\right].
\tag{8}
\]

In these coordinates (4) also becomes

\[
K=-32\operatorname{Re}\left\{
\eta\det\begin{pmatrix}
1&1&1\\X_1^2&X_2^2&X_3^2\\Y_1^2&Y_2^2&Y_3^2
\end{pmatrix}\right\}.
\tag{9}
\]

Equations (5)–(9) retain the actual spectral dependence that is lost by
averaging an arbitrary cost over \(A_4\).

## 3. Investigation 020: the four-base budget and its sharp actual example

Put

\[
B=\sum_{\text{three double transpositions}}g_\pi,
\qquad S=A+B,\qquad t=T-2A.
\]

The three-label determinant relations in the common-minor cost space give

\[
\sum_{\text{three-cycles}}g_\pi=2T-4A=2t,
\qquad D=T+2B-3A.
\tag{10}
\]

Both are exact linear identities on the full fourteen-dimensional
common-minor space, not merely identities for actual spectra. Therefore

\[
\boxed{
t\ge0,\qquad |K|\le2t,\qquad
T=t+2A,\qquad D=t+2S-3A.}
\tag{11}
\]

Replacing the base permutation by any of the other three members of its
\(V_4\) coset leaves \(S,t,K\) unchanged. Only \(A\), the deficit at
that particular base, changes. The four possible values of \(A\) are
nonnegative and sum to \(S\).

### The exact region settled by the support inequalities

Expanding the product in (11) gives

\[
TD-t^2=t(2S-A)+2A(2S-3A).
\tag{12}
\]

Whenever the right side is nonnegative, (11) immediately proves
\(K^2\le4TD\). In particular:

1. If \(A\le2S/3\), every term on the right is nonnegative.
2. If \(t\ge2S\), use \(A\le S\): the expression is bounded below by
   \(2S(2S-A)+2A(2S-3A)=2(S-A)(2S+3A)\ge0\).
3. If \(A=0\), then \(D\ge T\) and \(|K|\le2T\).

Since at most one of four nonnegative numbers summing to \(S\) can
exceed \(2S/3\), the budget holds for **at least three of the four
bases in every Klein-group coset**. Thus at least 18 of the 24 base
permutations are settled for every nonnegative common-minor cost.

The precise potentially unsettled region is smaller than the two
conditions \(A>2S/3\), \(t<2S\). If \(S>0\), write
\(a=A/S\), \(u=t/S\). It is

\[
\boxed{
\frac23<a\le1,\qquad
3a-2\le u<\frac{2a(3a-2)}{2-a}.}
\tag{13}
\]

The lower bound is \(D\ge0\); the upper bound is the failure of the
elementary estimate \(TD\ge t^2\). No claim that every point in (13)
is actually spectral is made.

### A phase-geometric sufficient condition

For one of the four-point sets (5), let
\(l_i=\operatorname{Re}(\eta L_i)\) and
\(H=h-\operatorname{Re}(\eta M)\). Then \(S=4H\), and the four gaps
are \(H-\epsilon\cdot l\).

If \(l_1l_2l_3\ge0\), an allowed change of signs makes all three
coefficients nonnegative. With their ordered absolute values
\(x\ge y\ge z\ge0\), support maximality gives
\(H\ge x+y+z\), and the largest gap is at most
\(H+x+y-z\le2H=S/2\). Hence the budget holds at every base in that
coset.

An unsettled coset therefore requires \(l_1l_2l_3<0\). After the
allowed sign changes take \(l=(-x,-y,-z)\), with
\(x\ge y\ge z>0\). The domination condition \(A>2S/3\) then forces

\[
x+y-z\le H<\frac35(x+y+z),
\qquad z>\frac{x+y}{4}.
\tag{14}
\]

This pinpoints the remaining phase geometry: three negative Fourier
coefficients of comparable size, with little excess support height from
the other five cosets. The determinant formula alone has not supplied the
additional inequality in this region.

### A full actual spectral family settled by this argument

If either spectrum consists of two eigenvalues, each of multiplicity two,
then the budget holds for every other spectrum, every support direction,
and every base permutation.

Indeed, when \(a=(p,p,q,q)\), the product function is unchanged by
right composition with \((12)(34)\). In every \(V_4\) coset its four
cost values therefore occur in equal pairs. Each base deficit is at most
\(S/2\), so the first sufficient region applies. The case of the
repeated spectrum \(b\) is the corresponding left-composition argument.

This proves the stronger quadratic budget for this family, and hence
the whole isoclinic support inequality. The underlying MOC special case
is not claimed as a new discovery.

### The coefficient four is attained by finite actual spectra

Take

\[
\boxed{
a=(1,1,-1,-1),\quad b=(i,-i,-i,i),\quad\eta=\frac14.}
\tag{15}
\]

Exact multiplication gives \(h=1\) and

\[
\boxed{A=0,\quad T=D=4,\quad K=-8.}
\tag{16}
\]

Thus \(K^2=4TD\), proving that a universal coefficient smaller than
four is impossible. The entire support deficit on the isoclinic curve is

\[
\boxed{h-c(U(r))=\frac{4(r+1)^2}{(r^2+3)^2}.}
\tag{17}
\]

This is an exact spectral equality model, not an optimized numerical
limit or a point of the larger nonic closure.

## 4. Investigation 021: a direct actual family in the dominated-base region

The region (13) is not empty for actual costs with nonzero \(K\).
The following family gives an explicit analytic test of it.

Let

\[
q=(1,0,0,\varepsilon),\qquad
0\le\varepsilon\le\frac12,\quad0\le\tau\le\frac12,\quad\nu\in\mathbb R,
\]

and choose actual spectra and a support direction

\[
\boxed{
a=(1,\tau+i\nu,0,0),\qquad
b_j=-\frac1{1+q_j},\qquad
\eta=2(1+\varepsilon)=\frac1{\prod_j b_j}.}
\tag{18}
\]

Then

\[
\eta z_\pi=
-q_{\pi(1)}\,[1-(\tau+i\nu)(1+q_{\pi(2)})].
\]

Since \(\tau\le1/2\) and \(q_j\le1\), its real part is
nonpositive, and some permutations have real part zero. Therefore the
actual support height is exactly zero and

\[
\boxed{g_\pi=q_{\pi(1)}[1-\tau(1+q_{\pi(2)})].}
\tag{19}
\]

Exact summation gives

\[
\begin{aligned}
A&=1-\tau,& S&=(1+\varepsilon)(1-\tau),\\
T&=3(1-\tau)+\varepsilon(1-2\tau),&
D&=\varepsilon(3-4\tau),\\
K&=2\tau\varepsilon,& t&=S-\tau\varepsilon.
\end{aligned}
\tag{20}
\]

Here \(A/S=1/(1+\varepsilon)\ge2/3\) and \(t/S\le1\).
More strongly, the actual point \(\tau=1/2,\varepsilon=1/10\) has

\[
A=t=\frac12,\quad S=\frac{11}{20},\quad
T=\frac32,\quad D=K=\frac1{10}.
\tag{21}
\]

It lies strictly in (13), since \(TD=3/20<t^2=1/4\).
Thus this example cannot be settled by the bound \(|K|\le2t\) alone.

Nevertheless, the whole family (18) satisfies the much stronger exact
inequality

\[
\boxed{K^2\le\frac13 TD.}
\tag{22}
\]

Indeed, (20) gives \(T\ge3/2\), \(D\ge\varepsilon\), and
\(K^2\le\varepsilon^2\). Thus
\(K^2/(TD)\le2\varepsilon/3\le1/3\) when
\(\varepsilon>0\); when \(\varepsilon=0\), \(K=D=0\).
Equality in (22) occurs at \(\tau=\varepsilon=1/2\), where
\(T=3/2,D=K=1/2\).

This theorem concerns the support direction specified in (18), with
arbitrary imaginary part \(\nu\) in the second eigenvalue. It does
not assert a new proof for all support directions of those spectra.

## 5. Scope of the proved regions


The formulas and the actual family above did not establish that final
compatibility inequality throughout (13). The universal isoclinic budget
and unrestricted complex MOC consequently remain unresolved in this work.

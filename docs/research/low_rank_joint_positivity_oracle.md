## 1. Proved: positivity on a rank-one \(+\)-parity subcone

Use the canonical feature order \(q=(\operatorname{coords}T,\operatorname{coords}C,d)\), with Hermitian-coordinate convention from `organized/research/joint_certificate_rank/exact_joint_structure.py:28`.

For arbitrary real \(x,z,t\), set
\[
T=i t\begin{pmatrix}
0&z&-x\\-z&0&x\\x&-x&0
\end{pmatrix},\qquad
C=\begin{pmatrix}x\\x\\z\end{pmatrix}
  \begin{pmatrix}x&x&z\end{pmatrix},\qquad d=0,
\]
and \(Y=qq^T\). Exact symbolic calculation gives
\[
\boxed{\langle Y,A_e\rangle=0\quad(e=1,\ldots,6),\qquad
       \langle Y,G_j\rangle=0\quad(j=1,\ldots,8).}
\]

Here is a nonnegative decomposition of \(\langle Y,F(z_{\rm profile})\rangle\) into **original permutation gaps**.

Define
\[
S_-=w_{12}+w_{13},\quad S_+=w_{24}+w_{34},\quad W=w_{23},
\]
\[
a=(x-z)^2,\quad b=(x+z)^2,\quad h=|xt|,
\quad \epsilon=\operatorname{sgn}(xt),
\]
taking either sign when \(xt=0\), and put
\[
L=4\{h(x^2+z^2)-x^2(z^2+t^2)\},\qquad \lambda=\max(0,L).
\]
The following quantities are nonnegative original-gap combinations:
\[
A_\epsilon=2(S_-+W)-\epsilon J_{012}/2,\qquad
B_\epsilon=2(S_++W)-\epsilon J_{123}/2,
\]
\[
C_\epsilon=d_3+2(S_-+S_+)-\epsilon(J_{012}+J_{123})/2.
\]
The first two are individual three-cycle gaps. In one-line permutation notation,
\[
C_+=\Delta_{4123}+\Delta_{3421},\qquad
C_-=\Delta_{2341}+\Delta_{4312}.
\]

The exact identity is
\[
\begin{aligned}
\langle Y,F\rangle={}&
(4ha-\lambda)A_\epsilon+(4hb-\lambda)B_\epsilon+\lambda C_\epsilon\\
&+4a(|x|-|t|)^2S_-+4b(|x|-|t|)^2S_+\\
&+4(\lambda-L)W+\bigl((x^2-z^2)^2-\lambda\bigr)d_3 .
\end{aligned}
\]
Every coefficient is nonnegative. The two nontrivial checks are
\[
4h\min(a,b)-L=4x^2(|z|-|t|)^2\ge0,
\]
\[
(x^2-z^2)^2-L=(x^2+z^2-2h)^2\ge0.
\]

Thus this subcone is positive even under the weaker, formal original-gap assumptions.

**This also handles conic sums of these matrices without splitting the allocation maximum.** Their summed allocation pairing is still zero. For any associated joint scalar multipliers and one common legal allocation \(\alpha\),
\[
\mu\cdot w+\xi\cdot r
=\mu\cdot(w-\alpha)+\nu\cdot\alpha+\xi\cdot(r+C\alpha)\ge0.
\]
Consequently no joint certificate in this generated subcone can be negative.

This is **not** a proof for every pure-\(+\) rank-one certificate: the vector underlying \(C\) here has its first two coordinates equal.

## 2. New concrete target: an exact rank-\((0,4)\), zero-support family

For \(u,v>0\) and \(k\in\mathbb R\), define four feature columns by:

| Column | Nonzero entries of \(T\) | Nonzero upper-triangular entries of \(C\) | \(d\) |
|---|---|---|---|
| \(q_0\) | \(\operatorname{diag}(u^2/v,1/v,1/v)\) | none | \(-v\) |
| \(q_1\) | \(T_{12}=k\) | \(C_{12}=i\) | \(0\) |
| \(q_2\) | \(T_{13}=k\) | \(C_{13}=-i\) | \(0\) |
| \(q_3\) | \(T_{23}=k/u\) | \(C_{23}=iu\) | \(0\) |

Complete lower entries by Hermitian symmetry, and set
\[
Y=\sum_{\ell=0}^3q_\ell q_\ell^T,\qquad \mu=\nu=\xi=0.
\]
This supplies an explicit PSD factorization, with
\[
\boxed{\operatorname{rank}Y=4,\qquad
       \langle Y,A_e\rangle=\langle Y,G_j\rangle=0
       \text{ for all fourteen directions}.}
\]
It lies entirely in the minus block, so its permitted pattern is
\[
(r_+,r_-,s)=(0,4,0).
\]

Write
\[
A=w_{12}+w_{14}+w_{23}+w_{34},\quad B=w_{13}+w_{24},\quad g=A+B,
\]
\[
D=d_1+d_3,\quad E=d_2,\quad
J=J_{012}-J_{013}+J_{023}-J_{123}.
\]
Its exact objective is
\[
\begin{aligned}
\mathcal L(u,v,k)={}&gv^2+
 \frac{Au^4+B(u^2-2)^2}{v^2}\\
&+u^2(-2A+6B+2D-2E)+4A-4B+4E\\
&+4k^2(A+B/u^2)+kJ .
\end{aligned}
\]

For \(g>0\), minimizing over \(v>0\) and \(k\), and setting \(\tau=u^2>0\), gives the exact reduced target
\[
\boxed{
\begin{aligned}
R(\tau)={}&2\sqrt{g\{A\tau^2+B(\tau-2)^2\}}\\
&+\tau(-2A+6B+2D-2E)+4A-4B+4E\\
&-\frac{J^2\tau}{16(A\tau+B)} .
\end{aligned}}
\]
Nonnegativity of this entire certificate family on actual supported spectra is equivalent to
\[
\boxed{R(\tau)\ge0\qquad\text{for every }\tau>0.}
\]

This isolates one odd coordinate: \(J=\chi/2\), using `organized/research/ODD_PROFILE_LINKAGE.md:18–32`. It gives a concrete spectral-determinant budget to attack, rather than another general rank survey.


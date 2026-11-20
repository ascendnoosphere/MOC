### 1. The determinant really is stable

For every fixed unitary \(W\), define
\[
P_W(x,y)=\det\!\left(\operatorname{diag}x+
W\operatorname{diag}y\,W^*\right).
\]
This polynomial is multiaffine and real stable in its eight variables. Indeed, when all eight variables have positive imaginary parts, the matrix inside the determinant has positive-definite imaginary part and is therefore invertible.

But the polynomial requiring nonnegativity is
\[
G_\eta(T)=\det(I+T^2)
\left[h-\Re\!\left(\eta P_{W(T)}(a,b)\right)\right],
\quad
h=\max_{\pi\in S_4}\Re(\eta p_\pi),
\quad
p_\pi=\prod_{j=1}^4(a_j+b_{\pi(j)}).
\]
This is exactly the gap in `organized/research/SINKHORN_GLOBAL_REDUCTION.md:77–91`. Its stability does **not** follow.

### 2. A universal-\(b\) identity on a two-block slice

Let
\[
u=\frac{(1,-1,0,0)^T}{\sqrt2},
\qquad
v=\frac{(0,0,1,-1)^T}{\sqrt2},
\qquad
S(s,t)=suu^T+tvv^T.
\]
Both vectors are perpendicular to \(e\), so this is a legitimate Sinkhorn Cayley slice. Put
\[
W(s,t)=(I+iS(s,t))(I-iS(s,t))^{-1}.
\]
It has two independent \(2\times2\) blocks. Their diagonal-entry squared moduli are respectively \(1/(1+s^2)\), \(1/(1+t^2)\); their off-diagonal squared moduli are the complementary quantities.

Consequently, **for arbitrary complex \(a,b\)**,
\[
\begin{aligned}
&(1+s^2)(1+t^2)\det(A+W(s,t)BW(s,t)^*)\\
&\qquad=p_{\mathrm{id}}
+s^2p_{(12)}
+t^2p_{(34)}
+s^2t^2p_{(12)(34)}. \tag{1}
\end{aligned}
\]
This follows by taking the determinant of each block separately; no spectral reality assumption is used.

Keep the original maximum over **all 24 products**, and write
\[
g_\pi=h-\Re(\eta p_\pi)\ge0.
\]
Equation (1) gives the exact, phase-unrestricted identity
\[
G_\eta(s,t)
=g_{\mathrm{id}}+g_{(12)}s^2+g_{(34)}t^2
+g_{(12)(34)}s^2t^2. \tag{2}
\]
Thus this slice has the universal-\(b\) SOS certificate
\[
G_\eta(s,t)
=(\sqrt{g_{\mathrm{id}}})^2
+(\sqrt{g_{(12)}}s)^2
+(\sqrt{g_{(34)}}t)^2
+(\sqrt{g_{(12)(34)}}st)^2.
\]
This is only a two-block slice, **not** a global certificate.


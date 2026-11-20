# Exact geometry of a full two-dimensional unitary orbit

Continuous track, campaign 2, rounds 066–070 and 079. This note proves exact finite matrix criteria for an entire $U(2)$ orbit of the actual MOC support functional.

## 1. Why six real coordinates suffice for every minor simultaneously

Diagonalize $A=\operatorname{diag}(a_i)$, write $B=W\operatorname{diag}(b_j)W^*$, and fix a complex isometry $Y:\mathbb C^2\to\mathbb C^n$. Put

\[
U_Y(V)=I+Y(V-I_2)Y^*,\qquad
F(V)=\Re\{\eta\det(A+U_Y(V)BU_Y(V)^*)\},\quad V\in U(2).
\]

For every pair $I,J$ of equally sized index sets,

\[
\det((U_Y(V)W)_{I,J})=\alpha_{I,J}+\mathcal L_{I,J}(V)+\gamma_{I,J}\det V, \tag{1}
\]

where $\mathcal L_{I,J}$ is complex linear in the four entries of $V$.

**Proof.** The selected submatrix is a fixed matrix plus $L(V-I_2)R$, a rank-two update. In its determinant the update has degree at most two. Every quadratic contribution is a $2\times2$ minor of $L(V-I_2)R$, hence a constant times $\det(V-I_2)$, by Cauchy–Binet. Now use $\det(V-I_2)=\det V-\operatorname{tr}V+1$. This proof does not require an invertible selected submatrix.

Write

\[
V=e^{it}\bigl(q_0I+i(q_1\sigma_x+q_2\sigma_y+q_3\sigma_z)\bigr),
\quad q\in S^3,
\quad p=(\cos t,\sin t)\in S^1.
\]

Multiplication of (1) by $e^{-it}$ makes it complex linear in the six real coordinates $z=(q,p)$. Consequently every squared minor is a real quadratic form $z^TL_{I,J}z$. The determinant identity

\[
\det(A+U\operatorname{diag}(b)U^*)
=\sum_{|I|=|J|}a_{I^c}b_J\,|\det U_{I,J}|^2 \tag{2}
\]

therefore gives a real symmetric $6\times6$ matrix $L$ such that

\[
\boxed{F(V)=z^TLz,\qquad \|q\|^2=\|p\|^2=1.} \tag{3}
\]

The representation is simultaneous across every exterior degree. It does not discard coherent phases.

## 2. An exact convex lift of the full squared-minor profile

Let (R(U)) denote the vector of all squared minors. The matrices above define a linear map $\Phi_Y$ by $\Phi_Y(X)_{I,J}=\operatorname{tr}(L_{I,J}X)$. Then

\[
\boxed{
\operatorname{conv}\{R(U_Y(V)W):V\in U(2)\}
=\Phi_Y\{X\succeq0:\operatorname{tr}X_{qq}=1,\operatorname{tr}X_{pp}=1\}.} \tag{4}
\]

**Proof.** A pure unitary point corresponds to $X=zz^T$ and satisfies the stated traces. Conversely, set $J_6=\operatorname{diag}(I_4,-I_2)$. The two trace conditions give $\operatorname{tr}(J_6X)=0$. Apply the isotropic decomposition lemma proved in `continuous_prescribed_height_torus.md`: write $X=\sum w_kw_k^T$, with the squared norms of the two blocks of every $w_k$ equal. If that common value is $t_k>0$, normalize $w_k/\sqrt{t_k}$ to an actual pair $(q_k,p_k)\in S^3\times S^1$. The first block trace gives $\sum t_k=1$, proving (4). Zero terms are discarded.

This also gives a decomposition into at most six actual plane unitaries, because the isotropic construction uses at most $\operatorname{rank}X\le6$ terms. This is an exact lift for a fixed plane and base; it is not the larger common-minor polytope and does not imply a permutation decomposition.

As an immediate scalar consequence,

\[
\max_{V\in U(2)}F(V)
=2\min_{\lambda\in\mathbb R}\lambda_{\max}(L-\lambda J_6), \tag{5}
\]

or equivalently $F\le h$ on the whole orbit iff

\[
(h/2)I_6-L+\lambda J_6\succeq0
\]

for some real $\lambda$. The factor two is $\|z\|^2=2$. The elementary equality S-lemma proves attainment, including non-strict cases; no genericity assumption is needed.

## 3. The stationary five-dimensional Cayley matrix

Use Hermitian coordinates

\[
T=\begin{pmatrix}s&x+iy\\x-iy&t\end{pmatrix},\qquad
d=\det T=st-x^2-y^2,\qquad
V(T)=(I+iT)(I-iT)^{-1}.
\]

Define

\[
D(T)=\det(I+T^2)=1+s^2+t^2+2x^2+2y^2+d^2. \tag{6}
\]

Let $F_0=F(I_2)$, assume $I_2$ is stationary on this $U(2)$ orbit, and let

\[
H(T,T)=\left.\frac{d^2}{d\varepsilon^2}F(e^{i\varepsilon T})\right|_{\varepsilon=0},
\qquad \Delta=F(-I_2)-F_0.
\]

There is a unique real linear functional $\ell$ on the four-dimensional real space of Hermitian $2\times2$ matrices such that

\[
\boxed{
F(V(T))-F_0=
\frac{2H(T,T)+2d\,\ell(T)+\Delta d^2}{D(T)}.} \tag{7}
\]

**Proof of the exact shape.** In (3), the six homogeneous coordinates after Cayley substitution are

\[
q=\frac{(1+d,\,2x,\,-2y,\,s-t)}{\sqrt D},\qquad
p=\frac{(1-d,\,s+t)}{\sqrt D}. \tag{8}
\]

For example, this follows directly from

\[
V(T)=\frac{(1+d)I+i(2T-\operatorname{tr}(T)I)}{1-d-i\operatorname{tr}T}.
\]

Thus $(F-F_0)D$ is quadratic in the six lifted coordinates ((1,s,t,x,y,d)). The constant is zero, stationarity removes the four linear terms in $s,t,x,y$, and a term proportional to $d$ is simply part of the quadratic form in those four coordinates. The cubic terms have the form $2d\ell(T)$. The coefficient of $d^2$ is $\Delta$, since $V(rT)\to-I_2$ for invertible $T$ as $r\to\infty$. Finally $V(T)=e^{2iT+O(T^3)}$, so the ordinary quadratic term is (2H(T,T)). This proves (7). The homogeneous degrees prove uniqueness.

Let $H_4$ be the matrix of $H$ in coordinates $s,t,x,y$, and identify $\ell$ with its coefficient column. Then

\[
\boxed{
F(V)\le F_0\text{ for every }V\in U(2)
\quad\Longleftrightarrow\quad
M_5:=\begin{pmatrix}2H_4&\ell\\\ell^T&\Delta\end{pmatrix}\preceq0.} \tag{9}
\]

**Proof of necessity, including the apparent lifting issue.** The projective directions of $(T,\det T)\in\mathbb R^5$ are dense in $\mathbb{RP}^4$. Indeed, given ((Q,c)) with $\det Q\ne0$ and $c\ne0$, choose $T=(c/\det Q)Q$. Then

\[
(T,\det T)=\frac{c}{\det Q}(Q,c).
\]

If the quadratic form in (9) were positive in any direction, it would be positive in one of these dense realized directions, contradicting (7). Sufficiency is direct. The Cayley chart is dense in $U(2)$, so continuity includes all omitted unitaries.

## 4. Derivative factors and restriction to two phases

The logarithm expansion is $\log V(rT)=2irT-(2i/3)r^3T^3+O(r^5)$. Stationarity eliminates the contribution from the cubic change of parameter. Comparing cubic coefficients in (7) gives

\[
\boxed{
\left.\frac{d^3}{d\varepsilon^3}F(e^{i\varepsilon T})\right|_0
=\frac32\det(T)\,\ell(T).} \tag{10}
\]

In particular, the third derivative vanishes on every rank-one Hermitian generator. This also proves that its homogeneous cubic polynomial is divisible by the determinant quadratic.

If $T=\operatorname{diag}(x,y)$, the plane action is the two-phase torus with phase parameters $2\arctan x,2\arctan y$. Comparing (7) with the prior $3\times3$ torus formula gives

\[
\ell_s=2f_{112},\qquad \ell_t=2f_{122}.
\]

Thus the full-plane formula has exactly the previously verified factors and signs.

## 5. The cubic covector is the opposite endpoint gradient

Write $R=-I_2$, and define the directional first and second derivatives at the reflected point by

\[
g_R(S)=\left.\frac{d}{d\varepsilon}F(Re^{i\varepsilon S})\right|_0,
\quad
H_R(S,S)=\left.\frac{d^2}{d\varepsilon^2}F(Re^{i\varepsilon S})\right|_0.
\]

Then

\[
\boxed{g_R(S)=-\ell(\operatorname{adj}S),}\qquad
\boxed{H_R(S,S)=H(\operatorname{adj}S,\operatorname{adj}S)
-\frac{\Delta}{2}\operatorname{tr}(S^2).} \tag{11}
\]

**Proof.** For invertible $S$, $V(-S^{-1})=-V(S)$, $\det(-S^{-1})=1/\det S$, and $D(-S^{-1})=D(S)/(\det S)^2$. Substitution into (7), using that the $2\times2$ adjugate is linear, gives the polynomially continuing identity

\[
F(RV(S))-F_0=
\frac{2H(\operatorname{adj}S,\operatorname{adj}S)-2\ell(\operatorname{adj}S)+\Delta}{D(S)}.
\]

Compare linear and quadratic terms at $S=0$, remembering the factor two in $V(S)=e^{2iS+O(S^3)}$. This proves (11). The second quantity is a directional second derivative even when $R$ is not stationary; no coordinate-independent Hessian at a noncritical point is asserted.

Consequently the cubic obstruction measures a genuine gradient at the rank-two reflection endpoint. If $F_0$ is a global support maximum and the reflection has the same height, (9) forces $\ell=0$, consistently with stationarity at that endpoint.

## 6. A prescribed-height full-plane certificate

In coordinates $z=(z_0,s,t,x,y,d)$, set

\[
W_6=\operatorname{diag}(1,1,1,2,2,1),\quad
J_{05}=J_{50}=1/2,\quad J_{12}=J_{21}=-1/2,\quad J_{33}=J_{44}=1.
\]

All unspecified entries of $J$ are zero. Thus

\[
z^TJz=z_0d-st+x^2+y^2.
\]

It has signature ((4,2)). For $h\ge F_0$, $c=h-F_0$, and stationary $I_2$, put

\[
N_h=cW_6-\operatorname{diag}(0,M_5).
\]

Then the exact condition is

\[
\boxed{F(V)\le h\text{ on all of }U(2)
\quad\Longleftrightarrow\quad
\exists\lambda:\ N_h+\lambda J\succeq0.} \tag{12}
\]

The chart $z_0=1,d=st-x^2-y^2$ is dense in this real projective quadric. Apply the same one-constraint quadratic lemma. At $c=0$, the zero first diagonal entry again forces $\lambda=0$, recovering (9). Formula (8) shows directly that this six-dimensional quadratic cone is a linear change of coordinates from (3).

## 7. What every rank-one test leaves invisible

At a stationary point, rank-one relative updates are precisely the Cayley directions with $\det T=0$, together with their closure. Their values determine $H$ only modulo a multiple of $\det T$, and do not determine $\ell$ or $\Delta$. The space of stationary quadratic models invisible on every rank-one fiber therefore has dimension six: one determinant component of $H$, four components of $\ell$, and one reflection coefficient.

Here the assertion about $H$ uses the elementary fact that a real homogeneous quadratic vanishing on the indefinite quadric $st-x^2-y^2=0$ is proportional to that defining quadratic. It follows either by polynomial division on the chart $s\ne0$, or by comparing coefficients after $t=(x^2+y^2)/s$.

There is an exact squared-minor example of this invisibility. Take

\[
Y=2^{-1/2}\begin{pmatrix}I_2\\I_2\end{pmatrix},\quad
U_Y(V)=\frac12\begin{pmatrix}I_2+V&V-I_2\\V-I_2&I_2+V\end{pmatrix}.
\]

The squared modulus of its upper-right $2\times2$ minor is

\[
\frac{|\det(V-I_2)|^2}{16}=\frac{d^2}{D(T)}.
\]

It vanishes on every rank-one update but equals one at $V=-I_2$. This is an actual squared-minor functional. It is **not** asserted to be realizable as an MOC spectral support functional. It rigorously prevents a proof that controls arbitrary minor observables using only their rank-one restrictions.

## Status

The exact fixed-plane positivity problem is solved by (9) or (12). The unrestricted MOC problem is not solved: one must still prove the spectral permutation budget enforces these matrices, or find a scalar-preserving route through planes. The companion note derives the actual spectral coefficients and an explicit coherent sum-of-squares certificate.

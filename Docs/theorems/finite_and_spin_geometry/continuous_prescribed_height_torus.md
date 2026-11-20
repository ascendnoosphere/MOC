# Prescribed-height certificates on a two-phase unitary torus

All results below concern the actual determinant support functional; no common permutation law is assumed.

## 1. Set-up and the complete numerator

Let $A,B$ be normal matrices, let $u,v$ be orthonormal, and put

\[
G(\theta_1,\theta_2)=I+(e^{i\theta_1}-1)uu^*+(e^{i\theta_2}-1)vv^*,\qquad
f=\Re\{\eta\det(A+GBG^*)\}.
\]

The squared-minor expansion of the determinant shows that $f$ has trigonometric degree at most one in each phase. Write $f_0=f(0,0)$, and use subscripts for derivatives at the origin. Set

\[
\Delta=f(\pi,\pi)-f_0,\qquad
x=\tan(\theta_1/2),\quad y=\tan(\theta_2/2),\quad z=(1,x,y,xy)^T.
\]

Then, without assuming stationarity,

\[
f-f_0=\frac{z^TTz}{z^Tz},\qquad
T=\begin{pmatrix}
0&f_1&f_2&0\\
f_1&2f_{11}&2f_{12}&2f_{112}+f_2\\
f_2&2f_{12}&2f_{22}&2f_{122}+f_1\\
0&2f_{112}+f_2&2f_{122}+f_1&\Delta
\end{pmatrix}. \tag{1}
\]

**Proof.** Any such real trigonometric polynomial, after its constant is removed, has a unique expansion in

\[
c_1-1,\ c_2-1,\ (c_1-1)(c_2-1),\ s_1(c_2-1),\ (c_1-1)s_2,\ s_1s_2,\ s_1,\ s_2,
\]

where $c_j=\cos\theta_j,s_j=\sin\theta_j$. Substitute $c_1-1=-2x^2/(1+x^2)$, $s_1=2x/(1+x^2)$, and the analogous formulas for $y$. The coefficients of $x,x^2y$ are $2f_1,4f_{112}+2f_2$, respectively; the other entries follow in the same way. The $x^2y^2$ coefficient is the value difference at $(\pi,\pi)$. This proves (1), including every factor and sign.

At a stationary origin, $f_1=f_2=0$, so

\[
T=\operatorname{diag}(0,M),\qquad
M=\begin{pmatrix}
2f_{11}&2f_{12}&2f_{112}\\
2f_{12}&2f_{22}&2f_{122}\\
2f_{112}&2f_{122}&\Delta
\end{pmatrix}. \tag{2}
\]

## 2. An elementary isotropic decomposition lemma

**Lemma.** Let $J$ be a real symmetric matrix with positive and negative eigenvalues. If $X\succeq0$ and $\operatorname{tr}(JX)=0$, there is a decomposition

\[
X=\sum_{k=1}^{\operatorname{rank}X}w_kw_k^T,
\qquad w_k^TJw_k=0.
\tag{3}
\]

**Proof.** Factor $X=VV^T$, with $V$ having $r=\operatorname{rank}X$ columns. The real symmetric matrix $S=V^TJV$ has trace zero. It has an orthonormal basis $q_1,\ldots,q_r$ with $q_k^TSq_k=0$. To prove this assertion inductively, if $S=0$, use any basis. Otherwise its smallest and largest eigenvalues have opposite signs, so a unit vector in their two-dimensional eigenspace has zero Rayleigh quotient. Compress to its orthogonal complement; the compressed matrix again has trace zero. Now take $w_k=Vq_k$.

**One-constraint quadratic consequence.** For real symmetric $N,J$, with $J$ indefinite,

\[
x^TNx\ge0\quad\text{whenever }x^TJx=0
\quad\Longleftrightarrow\quad
\exists\lambda\in\mathbb R:\ N+\lambda J\succeq0. \tag{4}
\]

For completeness, the converse is immediate. For the forward direction fix any positive definite $W$, and consider the compact convex set of pairs

\[
\bigl(\operatorname{tr}(JX),\operatorname{tr}(NX)\bigr),
\quad X\succeq0,\quad\operatorname{tr}(WX)=1.
\]

By (3), its slice over first coordinate zero has second coordinate nonnegative. Its lower boundary is a finite convex function on an interval containing zero in its interior, because $J$ is indefinite. A supporting line at zero therefore has finite slope $s$, and gives $\operatorname{tr}((N-sJ)X)\ge0$ for every normalized $X\succeq0$. Rank-one $X$ then give $N-sJ\succeq0$. This proves (4), including the non-strict boundary case.

This is an elementary proof of an equality form of the S-lemma. The related two-rebit isotropic decomposition is established in Caves, Fuchs, and Rungta, *Entanglement of Formation of an Arbitrary State of Two Rebits*, [arXiv:quant-ph/0009063](https://arxiv.org/abs/quant-ph/0009063), especially their real separability condition. We make no priority claim for the quadratic cone lemma. The determinant applications and explicit coefficients here are derived directly.

## 3. The exact prescribed-height test

Given $h\ge f_0$, put $c=h-f_0$ and $N_h=cI_4-T$. Define $J$ by

\[
J_{03}=J_{30}=1,\qquad J_{12}=J_{21}=-1,
\]

with all other entries zero, using indices $0,1,2,3$. Thus $z^TJz=2(z_0z_3-z_1z_2)$. Then

\[
\boxed{\quad f(\theta_1,\theta_2)\le h\ \text{for all phases}
\quad\Longleftrightarrow\quad
\exists\lambda\in\mathbb R:\ N_h+\lambda J\succeq0.\quad} \tag{5}
\]

**Proof.** The real projective null cone of $J$ is the real Segre surface: reshape $z$ as a $2\times2$ matrix and require rank at most one. The chart ((1,x,y,xy)) is dense in it, and is exactly the two-phase half-angle chart. Thus the phase inequality is equivalent to $z^TN_hz\ge0$ on the null cone. Apply (4). Continuity includes phases with an infinite half-angle coordinate.

At a stationary origin with $c=0$, the first diagonal entry of $N_h+\lambda J$ is zero. Positivity forces its entire first row to vanish, hence $\lambda=0$. Consequently (5) reduces precisely to $M\preceq0$, the prior whole-torus criterion.

At a stationary origin, $f_1=f_2=0$, use $T=\operatorname{diag}(0,M)$ from (2). If $c>0$, taking the Schur complement of the first entry in (5) shows that the whole-torus bound is equivalent to the existence of $\lambda\in\mathbb R$ satisfying

\[
cI_3-M-\lambda(E_{12}+E_{21})-\frac{\lambda^2}{c}E_{33}\succeq0. \tag{6}
\]

Here the three coordinates are $x,y,xy$, and the $E$-indices run from one to three.

## 4. An actual MOC example requiring a nonzero multiplier

Let $A=B=\operatorname{diag}(1,-1)$, $u=(1,1)/\sqrt2$, $v=(1,-1)/\sqrt2$, and $\eta=1$. Direct calculation gives

\[
f=-2-2\cos(\theta_1-\theta_2),\qquad f_0=-4,
\qquad h=\max\{-4,0\}=0.
\]

Here $c=4$, $\Delta=0$, and

\[
M=\begin{pmatrix}4&-4&0\\-4&4&0\\0&0&0\end{pmatrix},\qquad
N_h=\begin{pmatrix}4&0&0&0\\0&0&4&0\\0&4&0&0\\0&0&0&4\end{pmatrix}.
\]

$N_h$ is indefinite. The unique feasible multiplier is $\lambda=4$, and

\[
z^T(N_h+4J)z=4(z_0+z_3)^2.
\]

Indeed the two zero diagonal entries in the $x,y$ block force $4-\lambda=0$. This establishes that the multiplier in the exact criterion cannot in general be set to zero.

## 5. A closed-form test when the cubic derivatives vanish

Assume stationarity and $f_{112}=f_{122}=0$. After permuting coordinates, (5) is the positivity of the two blocks

\[
\begin{pmatrix}c&\lambda\\\lambda&c-\Delta\end{pmatrix},\qquad
\begin{pmatrix}c-2f_{11}&-2f_{12}-\lambda\\-2f_{12}-\lambda&c-2f_{22}\end{pmatrix}.
\]

It follows that the whole torus is bounded by $h$ exactly when the four diagonal quantities are nonnegative and

\[
\boxed{2|f_{12}|\le
\sqrt{c(c-\Delta)}+
\sqrt{(c-2f_{11})(c-2f_{22})}.} \tag{7}
\]

This follows by intersecting the two permitted intervals for $\lambda$. It is an exact condition, not a relaxation. Vanishing of the cubic derivatives follows, for example, from phase reversal symmetry on that torus. At $h=f_0$, (7) is precisely negative semidefiniteness of the two-dimensional Hessian together with the opposite-corner bound.

## Status

These results replace infinitely many phase evaluations by a single explicit matrix pencil. They do not prove that the MOC permutation support height makes the pencil feasible. The full $U(2)$ version and the actual spectral budget are developed in `continuous_full_rank_two_geometry.md` and `continuous_spectral_rank_two_budget.md`.

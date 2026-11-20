# Reciprocal MOC pencils as polynomials of a normal compression

## Scope

The identities and completion theorem in this note are proved. They do not supply the universal MOC support budget. No historical novelty is asserted.

## 1. A single compressed normal matrix generates both pencils

Fix β∈C⁴ and a real unit vector v. Put H=v⊥ and let P be its orthogonal projection. The original pencils are

\[
B=T_\beta|_H,\quad N=p_\beta T_{1/\beta}|_H,
\quad T_\beta=(1+v^TD_\beta v)D_\beta-(D_\beta v)(D_\beta v)^T.
\]

Temporarily assume β_j≠−1 and all intermediate inverses exist. Define

\[
\gamma_j=(1+\beta_j)^{-1},\quad Q=\prod_j(1+\beta_j),
\quad E=P D_\gamma P|_H.
\]

In v⊕H write D_β=[[m,wᵀ],[w,C]] and s=1+m. The lower-right block of (I+D_β)^{-1} is E, so block inversion gives

\[
E^{-1}=I+C-ww^T/s=I+B/s.
\]

Moreover det E=s/Q. The reciprocal version gives det(I−E)=t/Q, where

\[
t=p_\beta+\sum_jv_j^2\prod_{k\ne j}\beta_k.
\]

Using BN=stI, or applying the same Schur inversion twice, gives

\[
\boxed{
B=Q(\operatorname{adj}E-\det E\,I),\qquad
N=Q(\operatorname{adj}(I-E)-\det(I-E)\,I).
}
\tag{1}
\]

The formulas have removable singularities wherever their polynomial original expressions are defined. A β_j=−1 requires a different Möbius chart or a limit; it must not be inserted into γ_j directly.

Write e_k=e_k(E). The 3×3 adjugate polynomial gives

\[
B/Q=E^2-e_1E+(e_2-e_3)I,
\]

\[
N/Q=E^2+(1-e_1)E+e_3I.
\tag{2}
\]

In particular,

\[
\boxed{(N-B)/Q=E+(2e_3-e_2)I.}
\tag{3}
\]

Thus the affine-normalized difference of the two actual pencils has a normal completion with one additional dimension.

## 2. The two pencils share one complex rank-one correction

Write D_γ=[[z,uᵀ],[u,E]] in v⊕H. Then

\[
E^2=P D_{\gamma^2}P|_H-uu^T.
\]

Consequently

\[
\boxed{B/Q=P D_{\gamma^2-e_1\gamma+e_2-e_3}P|_H-uu^T,}
\]

\[
\boxed{N/Q=P D_{\gamma^2+(1-e_1)\gamma+e_3}P|_H-uu^T.}
\tag{4}
\]

This differs from the original pair of separate corrections built from D_βv and D_{1/β}v. Here their real and imaginary parts occupy the same real plane.

The characteristic polynomial coefficients of E are affine in the anchor probabilities p_j=v_j²:

\[
\det(xI-E)=\sum_jp_j\prod_{k\ne j}(x-\gamma_k).
\tag{5}
\]

Thus e_k(E)=Σ_jp_je_k(γ_{j^c}). The common correction is exactly what separates the compression of a quadratic polynomial from the same polynomial of the compression.

## 3. Every complex symmetric 3×3 matrix has a symmetric normal 4×4 completion

**Theorem.** For every E=X+iY with X,Y real symmetric 3×3 matrices, there exist u∈C³ and z∈C such that

\[
\mathcal A=\begin{pmatrix}z&u^T\\u&E\end{pmatrix}
\]

is normal. If E is nonnormal, a completion can be chosen with uᵀu=0. Among symmetric normal completions, this choice minimizes ||u||².

**Proof.** If [X,Y]=0, take u=0 and any z. Otherwise write

\[
[X,Y]=[j]_\times,\qquad g=\|j\|>0,
\]

where [j]_×x=j×x. Let n=j/g and choose real orthonormal e,f spanning n⊥, with e×f=n. Put

\[
r=\cos\theta\,e+\sin\theta\,f,\qquad
q=-\sin\theta\,e+\cos\theta\,f.
\]

The scalar condition

\[
n^TXq=n^TYr
\tag{6}
\]

is A cosθ+B sinθ=0 for two real constants, and always has a solution. Set

\[
a=\sqrt g\,r,\quad b=\sqrt g\,q,\quad u=a+ib,
\]

\[
c=q^TXq-q^TYr,\qquad d=r^TYr-r^TXq,\qquad z=c+id.
\]

The vector Xq−Yr has no component along n by (6). Its r and q components show directly that

\[
Xb-Ya-cb+da=0.
\]

Also a×b=j, so abᵀ−baᵀ+[X,Y]=0. These are exactly the lower-left and lower-right blocks in the commutator of Re A and Im A; the upper-left block vanishes automatically. Therefore A is normal.

The vectors a,b are perpendicular and both have squared norm g. Hence uᵀu=0 and ||u||²=2g.

For any symmetric normal completion, its real and imaginary off-diagonal vectors must satisfy a×b=j. Thus

\[
\|u\|^2=\|a\|^2+\|b\|^2\ge2\|a\|\|b\|
\ge2\|a\times b\|=2g.
\]

The constructed completion attains the lower bound. This proves all assertions.

If the two constants in (6) are not both zero, the minimizing rotation is unique up to θ↦θ+π, which changes u to −u and leaves z unchanged. When both constants vanish, a circle of minimizing rotations remains.

**Consequence.** Mere existence of a one-dimensional normal completion imposes no restriction on a complex symmetric 3×3 matrix. The eigenvalues of the actual completion are indispensable in MOC.

## 4. The corresponding higher-dimensional obstruction is explicit

Let E=X+iY be complex symmetric k×k with [X,Y] of rank two. Its range is a real plane W. A symmetric normal completion by one dimension exists exactly when one can find a,b∈W such that

\[
ab^T-ba^T=-[X,Y],\qquad
P_{W^\perp}(Xb-Ya)=0.
\tag{7}
\]

Indeed, the first equation forces independent a,b spanning W. The second says Xb−Ya lies in that plane, where unique real c,d solve Xb−Ya−cb+da=0. These conditions are necessary and sufficient for the same block commutator calculation.

Choosing a plane basis turns the first condition into one signed-area equation and the second into k−2 homogeneous linear equations in the four coordinates of a,b. For k=3 there is only one linear equation, and the equal-length orthogonal construction always solves it. In larger dimensions the restricted signed-area quadratic can lose the required sign. The k=3 theorem therefore does not justify an arbitrary-dimensional normal-completion claim.

## 5. Exact classification of the nonsingular normal-pencil branch

Assume Q,s,t≠0. Since N=stB^{-1}, equation (3) expresses E as a rational function of B. Equations (2) express B as a polynomial in E. Therefore

\[
B\text{ normal}\quad\Longleftrightarrow\quad E\text{ normal}.
\]

Write u=a+ib in the actual normal completion D_γ. The normal-completion identity gives

\[
[\Re E,\Im E]=ba^T-ab^T.
\]

Thus E is normal iff a,b are linearly dependent. In original coordinates,

\[
a=P D_{\Re\gamma}v,\qquad b=P D_{\Im\gamma}v.
\]

Dependence means precisely that all γ_j with v_j≠0 lie on one real affine line in C. Under γ=1/(1+β), this is equivalent to the supported β_j lying on a generalized circle through −1, with the usual limiting interpretation for a line. This includes sparse support of at most two labels.

This equivalence is asserted under the displayed nonsingularity assumptions. Polynomial identities remain valid on singular strata, but the rational-function argument must not be silently applied there.

There is also a quantitative formula. Let p_j=v_j² and let C_γ be the 2×2 real covariance matrix of the planar points γ_j under p. Then

\[
\|[\Re E,\Im E]\|_F^2=2\det C_\gamma
=2\sum_{i<j<k}p_ip_jp_k
\det\begin{pmatrix}
\Re(\gamma_j-\gamma_i)&\Re(\gamma_k-\gamma_i)\\
\Im(\gamma_j-\gamma_i)&\Im(\gamma_k-\gamma_i)
\end{pmatrix}^{\!2}.
\tag{8}
\]

The second equality is the 2D covariance Cauchy–Binet identity. Noncommutativity measures the weighted oriented areas of actual spectral triangles.

## 6. An explicit shared rank-one repair, and its limitation

Write u=a+ib and R=[a,b]. For κ∈C set

\[
L_\kappa=\begin{pmatrix}\Re\kappa&-\Im\kappa\\-\Im\kappa&-\Re\kappa\end{pmatrix},
\quad \Re(\kappa uu^T)=R L_\kappa R^T.
\]

For independent a,b, a common vector y repairing two corrections must lie in range R. Put y=tRw, ||w||=1. The exact 2×2 determinant criterion is

\[
L_{\kappa_i}+t^2ww^T\succeq0
\iff t^2w^TL_{\kappa_i}w\le-|\kappa_i|^2.
\tag{9}
\]

Let κ_i=r_i e^{iφ_i} with principal phase separation δ∈(−π,π). Choose w=(cosθ,sinθ) with 2θ+(φ_0+φ_1)/2=π. Then

\[
w^TL_{\kappa_i}w=-r_i\cos(\delta/2).
\]

Taking t²=max(r_0,r_1)/cos(δ/2) repairs both corrections. Opposite nonzero phases give L_{κ_0} as a negative multiple of L_{κ_1}, so simultaneous rank-one repair is impossible. A zero correction is omitted.

This construction does not prove the support budget. If A_B,A_N denote the compressed diagonal terms in (4), it gives the sufficient bound

\[
f(\Re(\kappa_1B/Q),\Re(\kappa_0N/Q))
\le\lambda_{\max}\Re(\kappa_1A_B)
+\lambda_{\max}\Re(\kappa_0A_N)+\|y\|^2.
\tag{10}
\]

No universal permutation-height bound is asserted for this sufficient estimate.

## 7. An exact family of alternative completions

Take

\[
E=\begin{pmatrix}0&i&0\\i&1&0\\0&0&i\end{pmatrix}.
\]

For any r>0,

\[
\mathcal A_r=\begin{pmatrix}
1-r^2&r&i/r&0\\
r&0&i&0\\
i/r&i&1&0\\
0&0&0&i
\end{pmatrix}
\]

is normal, with spectrum

\[
\gamma(r)=\left(-r^2,\ 1+i\sqrt{1+r^{-2}},\
1-i\sqrt{1+r^{-2}},\ i\right).
\tag{11}
\]

To verify normality, the real part has eigenvalue −r² on the vector (−r,1,0,0), where the imaginary part vanishes. On its orthogonal complement in the first three coordinates, the real part is I and the imaginary part has eigenvalues ±√(1+r^{-2}). The fourth coordinate is decoupled.

All members have the same E. The minimum leakage norm occurs at r=1. At r=3/4 the spectrum is rational complex:

\[
\gamma(3/4)=(-9/16,\ 1+5i/3,\ 1-5i/3,\ i).
\]

For a completion with eigenvalues γ, the Q-normalized CH vertices are

\[
w_{ikjl}=((1-\gamma_i)(1-\gamma_l)\gamma_k,
\ (1-\gamma_i)\gamma_k\gamma_l).
\tag{12}
\]

## 8. An exact orthogonal-frame maximum

For the same E and the r=1 completion, direct evaluation gives

\[
B/Q=\begin{pmatrix}0&1&0\\1&-i&0\\0&0&1-i\end{pmatrix},\qquad
N/Q=\begin{pmatrix}-1+i&1+i&0\\1+i&0&0\\0&0&i\end{pmatrix}.
\]

The actual frame maximum is (1+√5)/2, strictly below h_1. Indeed, the original first support matrix has largest eigenvalue 1, attained on the isolated third coordinate. The original second support matrix has largest eigenvalue (√5−1)/2, attained in the first two coordinates. These maximizing vectors are orthogonal, so the sum of the separate largest-eigenvalue bounds is attained. No general assertion that a block-diagonal pair has a block-preserving optimal frame is used.

## Remaining obligation

The actual support question is still the bound on the exact shared rank-one dual. The representation (1) reduces its complex algebra to a single normal compression and two complementary adjugate polynomials. The normal-completion theorem explains why that reformulation alone cannot certify the required vertex height. The local-to-open theorem in the companion note uses equality rigidity instead, and proves a genuine neighborhood while leaving global continuation unresolved.

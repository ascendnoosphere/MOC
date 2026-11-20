# Rank-one duals and quartic certificates for the remaining real MOC4 problem

## Scope

This note proves an exact optimization theorem for two real symmetric3×3 matrices. Combined with the proved U(4)-to-SO(4) minor-profile convexification, it reduces MOC4 to an actual-spectral rank-one dual construction. The universal spectral construction is not supplied here, so this is not a proof of MOC4.

## 1. The exact frame optimization

For real symmetric M,N, let

\[
f(M,N)=\max_{\substack{\|r\|=\|s\|=1\\r^Ts=0}}
(r^TMr+s^TNs).
\]

The real three-effect decomposition lemma proves that this equals

\[
\max \{\operatorname{tr}(ME_1)+\operatorname{tr}(NE_2):
E_i\succeq0,\ \operatorname{tr}E_i=1,\ \sum_{i=1}^3E_i=I_3\}.
\]

For completeness, the lemma follows from a support-dimension argument: if all ranks are at least2, supported symmetric perturbations have at least9 dimensions and the trace/sum constraints impose at most8 independent equations. Thus every extreme feasible triple has a rank-one effect. The other two effects then lie on its2D complement and commute, so the tuple is a mixture of orthogonal projection frames.

The SDP dual, after fixing the third scalar multiplier at0, is

\[
f(M,N)=
\min\{\operatorname{tr}Y+\alpha+\beta:
Y\succeq0,\ Y+\alpha I_3\succeq M,\ Y+\beta I_3\succeq N\}.
\tag{1}
\]

The primal point E_i=I₃/3 is strictly feasible. The finite optimum is attained on both sides.

## 2. Every optimal shared dual correction can be reduced to rank one

**Theorem.** An optimum in(1) exists with rankY≤1.

**Proof.** Choose an optimal orthonormal frame(r,s,t), which exists by the frame-decomposition lemma, and an optimal dual(Y,α,β). Complementary slackness with the third effectttᵀ gives Yt=0. Therefore rankY≤2.

If rankY≤1 there is nothing to prove. Otherwise let τ>0 be the smaller eigenvalue of Y on t⊥ and put

\[
Y'=Y-\tau(I_3-tt^T),\quad
\alpha'=\alpha+\tau,\quad\beta'=\beta+\tau.
\]

The matrixY' remainsPSD and has rank1. Each other dual slack gains the PSD matrixτttᵀ:

\[
Y'+\alpha'I_3-M=Y+\alpha I_3-M+\tau tt^T\succeq0,
\]

and similarly forN. The objective changes by−2τ+τ+τ=0. This proves the theorem.

The argument was independently audited in the final research batch.

**Corollary.** The exact, attained variational formula is

\[
\boxed{
f(M,N)=\min_{y\in\mathbb R^3}
\left\{\|y\|^2+
\lambda_{\max}(M-yy^T)+
\lambda_{\max}(N-yy^T)\right\}.}
\tag{2}
\]

Indeed, write the rank-one optimumY=yyᵀ and choose the least feasible scalar multipliers, which are the two displayed largest eigenvalues. The reverse inequality follows from dual feasibility for everyy.

## 3. A Lorentz-geometric interpretation

For a real symmetricM with eigenvaluesμ₁>μ₂≥μ₃, take α∈(μ₂,μ₁). ThenA=αI−M has one negative and two positive eigenvalues. A rank-one correction satisfies

\[
A+yy^T\succeq0
\quad\Longleftrightarrow\quad
y^TA^{-1}y\le-1.
\tag{3}
\]

The rank-one update can remove at most one negative eigenvalue. Since detA<0, the determinant identity det(A+yyᵀ)=detA(1+yᵀA⁻¹y) gives exactly the condition for its removal; boundary equality gives the PSD rank-deficient case.

In an eigenbasis, (3) is

\[
\frac{y_1^2}{\mu_1-\alpha}
-\frac{y_2^2}{\alpha-\mu_2}
-\frac{y_3^2}{\alpha-\mu_3}\ge1.
\]

Thus the two dual inequalities ask for a common vector on suitable two-sheeted quadratic regions, subject to the norm budget \(\|y\|^2\le h-\alpha-\beta\). Singular eigenvalue endpoints follow by limits or direct PSD conditions. They must not be removed from a universal proof.

## 4. The exact two-dimensional plane condition

Fix the unused frame vectort. On its orthogonal plane, the maximum over r,s is

\[
\operatorname{tr}(N|_{t^\perp})
+\lambda_{\max}\bigl((M-N)|_{t^\perp}\bigr).
\]

WritingD=M−N andS=M+N, this is

\[
\frac12\left[
\operatorname{tr}S-t^TSt+
\sqrt{(\operatorname{tr}D-t^TDt)^2
-4t^T\operatorname{adj}(D)t}
\right],
\quad\|t\|=1.
\tag{4}
\]

The adjugate term is the determinant of the2×2 compression ofD. Formula(4) is valid even whenD is singular or the two compressed eigenvalues coincide.

Define homogeneous forms

\[
L_h(t)=(2h-\operatorname{tr}(M+N))\|t\|^2+t^T(M+N)t,
\tag{5}
\]

\[
P_h(t)=
\bigl((h-\operatorname{tr}M)\|t\|^2+t^TMt\bigr)
\bigl((h-\operatorname{tr}N)\|t\|^2+t^TNt\bigr)
+\|t\|^2t^T\operatorname{adj}(M-N)t.
\tag{6}
\]

Squaring(4), while retaining the sign condition, gives the exact equivalence

\[
\boxed{f(M,N)\le h
\iff L_h(t)\ge0\text{ and }P_h(t)\ge0
\text{ for every }t\in\mathbb R^3.}
\tag{7}
\]

The sign conditionL_h≥0 is indispensable.

## 5. An explicit quartic sum-of-squares identity from a rank-one dual

Suppose a dual certificate is given with

\[
Y=yy^T,\quad
S_0=Y+\alpha I-M\succeq0,\quad
T_0=Y+\beta I-N\succeq0,
\]

and let \(h=\alpha+\beta+\|y\|^2\). Then

\[
L_h(t)=
t^T\bigl((\operatorname{tr}S_0+\operatorname{tr}T_0)I
-S_0-T_0+2yy^T\bigr)t\ge0.
\tag{8}
\]

More strongly, the exact identity

\[
\boxed{\begin{aligned}
P_h(t)={}&\|t\|^2t^T(\operatorname{adj}S_0+\operatorname{adj}T_0)t\\
&+\left\|S_0^{1/2}
(\|t\|^2I-tt^T)T_0^{1/2}\right\|_F^2\\
&+(y^Tt)^2t^T\bigl((\operatorname{tr}S_0+\operatorname{tr}T_0)I
-S_0-T_0\bigr)t\\
&+(y^Tt)^4
\end{aligned}}
\tag{9}
\]

is a sum-of-squares certificate for the ternary quartic.

To derive it, first set\(\|t\|=1\). Scalar shiftsα,β cancel in(6). On the2D planet⊥, use

\[
\det(T_0-S_0)=
\det T_0+\det S_0
-\operatorname{tr}T_0\,\operatorname{tr}S_0
+\operatorname{tr}(T_0S_0),
\]

where the matrices in this line are the2D compressions. The trace-product cancellation yields(9) on the unit sphere; homogenization yields the displayed identity everywhere.

Every term is nonnegative: adjugates of PSD3×3 matrices arePSD, and \((\operatorname{tr}S_0)I-S_0\succeq0\). Square roots are permitted even for singular slacks. This identity does not assume an unproved general SOS theorem.

If a certificate has objective strictly below a proposedh, first certify its actual objective and then add the positive constant support slack; formula(7) gives the desired larger bound.

## 6. The actual-spectral reciprocal pair

Fix a real unit rowv ofU∈U(4), and putH=v⊥,P=I−vvᵀ. Write

\[
C=P D_\beta P|_H,\qquad
G=P D_{1/\beta}P|_H,\qquad
p=\prod_j\beta_j.
\]

If

\[
D_\beta=
\begin{pmatrix}m&w^T\\w&C\end{pmatrix},
\qquad
D_\beta^{-1}=
\begin{pmatrix}n&z^T\\z&G\end{pmatrix}
\]

in v⊕H, block inversion gives

\[
\det C=pn,\quad\det G=m/p,\quad
CG=I-wz^T,\quad Cz=-nw,\quad Gw=-mz.
\tag{10}
\]

The adjugate identities are

\[
p\operatorname{adj}G=mC-ww^T,\qquad
\operatorname{adj}C=p(nG-zz^T).
\tag{11}
\]

Consequently the two coefficient-hull matrices are

\[
T_\beta|_H=C+p\operatorname{adj}G,\qquad
pT_{1/\beta}|_H=pG+\operatorname{adj}C.
\tag{12}
\]

For a support functionalRe(λ₀D₀+λ₁D₁),

\[
M=\Re\bigl(\lambda_1(C+p\operatorname{adj}G)\bigr),\qquad
N=\Re\bigl(\lambda_0(pG+\operatorname{adj}C)\bigr).
\tag{13}
\]

Zeroβ entries follow from the polynomial canceled expressions, rather than by dividing by zero.

**Remaining theorem needed for MOC4.** For every actual coefficient-hull facet with heighth and for every real unitv, constructy,α,β satisfying

\[
yy^T+\alpha I_H\succeq M,\quad
yy^T+\beta I_H\succeq N,\quad
\|y\|^2+\alpha+\beta\le h.
\tag{14}
\]

This rank-one certificate exists exactly when that fixed-row support inequality is true. The note proves the reduction and proof template, not the universal construction.


# Standalone T55 reduces to five positive-height boundaries

This is a paper reduction, not a proof of standalone T55. Use the
lexicographic row-to-column labels of [Zheng, Appendices E and G](https://doi.org/10.13140/RG.2.2.36790.25923).
The starting contacts are \(1,2,3,6,11,12\). Zero height is already covered
in [ZhengT55ZeroHeight.md](ZhengT55ZeroHeight.md).
Strictly negative upper height is covered by [Drury's external-vertices theorem](https://doi.org/10.13001/1081-3810.1131).
The extra contact 20 is covered by [T55+20](ZhengT55PositiveOverlap.md).
The extra contacts 4 and 0 are proved below. The remaining exact
additional contacts are \(7,9,18,21,23\), whose support inequalities
are not established in this note.

## Signed comparison

Write \(G_j=H-\Re(\eta P_j)\) and let \(A=01,B=02,C=03\)
be two-element sets. In order, use eight indicators \(a,b,c,d,e,f,g,z\),
where \(I\to J\) denotes \(\sigma(I)=J\):
\[
 A\to C,\quad A\to C^c,\quad A\to A^c,\quad B\to B,\quad
 B\to B^c,\quad B\to A^c,\quad C\to C^c,\quad \{0\}\to\{3\}.
\]
Use the same letters for their scalar coefficients. The indicators are
independent: labels \(4,8,17,0,10,20\) isolate \(a,b,c,d,g,z\);
label 7 gives \(e+g\), and label 21 gives \(f+z\).
They vanish on the six initial labels. A projected matching profile and its
gaps lie in the span of all subset-image markers. The zero-height note
bounds that span by dimension 14; six independent contact evaluations
are isolated there. Thus the exact coefficients are
\[
 (a,b,c,d,e,f,g,z)=
 (G_4,G_8,G_{17},G_0,G_7-G_{10},G_{21}-G_{20},G_{10},G_{20}).
\]
By the [Merikoski–Virtanen minor identity](https://doi.org/10.1016/0024-3795(89)90709-X),
the determinant gap \(L\) is obtained by evaluating indicators as squared minors.

Put \(n=(\{2\}\to\{0\})\). Exact indicator identity:
\(z+b+g-f=e+n\). Indeed \(b+g+(B\to12)\) is the event
\(\sigma(0)\in\{1,2\}\), and \((B\to12)+e+f\) is the event
\(0\notin\sigma(B)\). Subtract and use disjointness of singleton images.
If \(f<0\), eliminate it; the new coefficients of \(b,g,z,e,n\) are
\(b+f,g+f,z+f,e-f,-f\). The first three are \(G_{15},G_{13},G_{21}\).
Thus \(L<0\) forces \(e<0\) and, if \(f<0\), also \(e<f\).

For reference, the remaining gap evaluations are
\[
\begin{array}{c|rrrrrrrrrr}
j&5&9&13&14&15&16&18&19&22&23\\
G_j&a+d&b+e&f+g&b+d&b+f&c+d+g&a+e+z&a+f+z&c+z&c+e+z.
\end{array}
\]
At positive height on simple nonzero-factor data, the two activated
disjoint rectangles force \(c,G_{13}>0\), as below.
If \(L<0\), \(G_7,G_9\ge0\) force \(b,g>0\), and \(G_{15}>0\)
follows either from \(f\ge0\), or from \(G_9\ge0\) and \(e<f\).
So any additional active gap requires one of
\(G_0,G_4,G_7,G_9,G_{18},G_{20},G_{21},G_{23}=0\).
For example, gap 5 requires gap 0, and gap 19 requires gaps 4 and 21.

### The extra contact 4 is impossible in a strict witness

Put \(D_e=-e>0\) and \(\Delta=D_e-z\). If \(z\ge D_e\), then \(b,g\ge D_e\)
and the identity \(z+b+g-e=f+n\) on indicators absorbs the negative
coefficient \(-D_e\) of \(e\): subtract \(D_e\) times each of the
three indicators on the left with positive signs and replace the
whole term by \(D_e(f+n)\). The resulting coefficients are
nonnegative: \(f+D_e\ge0\) because if \(f<0\) a strict witness requires
\(e<f\). This contradicts \(L<0\). Hence \(\Delta>0\), and
\(G_{18}=a-\Delta\ge0\) shows \(G_4=a>0\). This exclusion of contact 4
is independent of the height and uses no spectral relation.

In fact this gives a single signed star for every strict witness.
Let \(K=M_a+M_b+M_c+M_g-M_e\), where \(M\) denotes evaluation as a
squared minor. Apply the same identity with coefficient \(z\) to get
\[
 L=\Delta K+G_{18}M_a+G_9M_b+G_{23}M_c+G_7M_g+G_0M_d
    +G_{21}M_f+G_{20}M_n .
\]
All seven ordinary coefficients are actual gaps, and \(K\) is exactly
the T55+20 signed star. The extra ordinary term is \(G_{20}M_n\);
one cannot apply the T55+20 theorem by simply discarding it, since the
remaining coefficients need not belong to a collision profile.

## Holomorphic contact curve without the collision

Repeated spectral values or a vanishing pair factor are excluded by
[FourCoincidence.lean](MOC/FourCoincidence.lean).
Use the projective chart of the T55+20 proof with signed spectra
\((\infty,t,0,1)\) and \((x,y,z_{\rm spec},w)\). Use \(1\) for the common
bracket at infinity and absorb the projective scale into \(\eta\).
Put \(\alpha=(w-1)/w,\ \gamma=(z_{\rm spec}-1)/z_{\rm spec}\) and
\(D=P_3-P_2\ne0\) (single swap). Let \(\eta D=i\delta\); freeze the
real ratios
\[
 \lambda=(P_6-P_1)/D,\quad l=(P_{12}-P_6)/D,\quad
 k=(P_{12}-P_2)/D,\quad r=(P_{11}-P_6)/(P_1-P_3).
\]
Single-swap differences also give \(r,l,m\ne0\), where
\(m=l+\lambda-k+1=(P_3-P_1)/D\).
Set \(u=P_6/D,\ v=u+l,\ \tau=v-k,\ h=-rm\).
The normalized contact products at \(1,2,3,6,11,12\) are
\(u-\lambda,\tau,\tau+1,u,u+h,v\). The two rectangles give
\[
 P_{17}/D=(u+h)(u+l)/u,\quad P_{13}/D=(\tau+1)v/\tau,\quad
 G_{17}=\frac{Hhl}{|u|^2},\quad G_{13}=\frac{Hk}{|\tau|^2}.
\]
Feasibility at positive height gives \(hl,k>0\), since neither is zero.
The checked signed_gap_relation in
[ZhengT55Identities.lean](MOC/ZhengT55Identities.lean)
gives \(G_{20}=-(\lambda/m)G_{17}\). If \(\lambda=0\), T55+20 applies.
Otherwise \(\lambda/m<0\). Substituting the contact ratios and \(P_{17}/D\)
in that same complex identity gives \(P_{20}/D=(u-\lambda)(1-rl/u)\).

Set \(\rho=r\gamma\). The chart formulas are
\[
 X=1+\rho=x/t,\quad Y=X\tau/v=y/t,\quad
 \alpha=\frac{(Y-1)u}{r(u-\lambda)},\quad
 t=\frac{1-r\gamma v/(Xu)}{1-\gamma}.
\]
Indeed the defining ratio for \(r\) is
\((x-t)z_{\rm spec}/[t(z_{\rm spec}-1)]\), and \(P_2/P_{12}=y/x\).
The formula for \(\alpha\) follows from \(P_1/P_6\), and the formula for
\(t\) from \(P_{12}/P_6\). Finally
\(D=y(1-t)z_{\rm spec}w(\gamma-\alpha)\), so \(P_6/D=u\) is equivalent to
\[
 r\alpha X(1-\gamma)=Y(rv-Xu)(\gamma-\alpha).
\]
After clearing denominators and canceling \(X\), this becomes
\[
 F(u,\rho)=uv(\rho\tau-k)(r-\rho)
 -\tau(rv-u-u\rho)\big[(uk-\lambda v)\rho+uk\big]=0.
\]
These steps reverse at any regular point and recover the genuine contact
products with direction \(i\delta/D\) and height \(H=-\delta\Im u\).
On the compact normalization of an irreducible component through the
initial profile, \(u\) is nonconstant: the coefficient of \(\rho^2\) is
\(u\tau[uk-(\lambda+1)v]\), nonzero at a nonreal \(u\) under \(k>0,l\ne0\).
Chart denominators, spectral degeneracies and function poles remove only
finitely many points, since none is identically exceptional there.

## Pole control

The single possible negative coefficient in the selected basis has
absolute value at most \(c+z\), by \(G_{23}\ge0\) and \(e-f>e\) when
\(f<0\). Therefore the negative part is bounded away from \(u=0\)
and tends to zero at infinity. For \(u=0\) use complex counterparts
of \(e,f\), before taking \(\delta\Im\):
\[
 E_c=-r(u-\lambda)+\frac{r(u-\lambda)v\rho\tau}{u(\rho\tau-k)},
 \qquad
 F_c=\frac{ku}{v}+\frac{k}{\tau}+\rho\left(\frac{ku}{v}-\lambda-1\right).
\]
Indeed \((P_7-P_{10})/D=u[1-y(1-\gamma)]/\alpha\).
Use \(1-y(1-\gamma)=1-Y+Y(1-t+t\gamma)\) and then the chart formulas.
Also \((P_{21}-P_{20})/D=(x-1)(y-t)/[y(1-t)]\).
Using the equation before clearing denominators gives
\(r(u-\lambda)(\gamma-\alpha)-r\gamma+k/\tau\), which is \(F_c\).
The new star coefficient has the particularly simple form
\[
 E_c+(P_{20}-P_6)/D=k/\alpha-\lambda,\qquad
 \Delta=k\delta\Im\alpha/|\alpha|^2 .
\]
This follows by writing \(\rho\tau/(\rho\tau-k)=1+k/(\rho\tau-k)\)
and using \(r\alpha=u(\rho\tau-k)/[(u-\lambda)v]\).

* If \(l\ne k\), the linear coefficient of \(F\) at \(u=0\) is
  \(\lambda l^2r(l-k)\ne0\); the constant one is zero. By the implicit
  function theorem there is a finite branch \(\rho=O(u)\) and a
  meromorphic infinite branch (apply the theorem to \(1/\rho\)).
  On the finite branch both \(E_c,F_c\) are bounded.
  On the infinite branch the leading term of \(\rho\) is
  \(\lambda lr/[(\lambda+1)u]\) if \(\lambda\ne-1\), and
  \(l^2r/(ku^2)\) if \(\lambda=-1\), by the quadratic coefficient.
  In either case \(E_c,F_c\) have the same residue \(-r\lambda l\)
  and at most simple poles. Since \(\delta\Im(1/u)>0\) at positive
  height, nonnegative residue is harmless. Otherwise \(e-f\) is
  bounded, so choose the alternative basis when \(f<0\); if \(f\ge0\),
  boundedness of \(e-f\) already bounds \(e\) below.
* If \(l=k\), then \(m=\lambda+1,\ \lambda\in(-1,0),r<0\) by the sign
  conditions. Divide \(F\) by its factor \(u\). Its new linear coefficient
  is \(k(\lambda kr-\lambda+k)>0\) at zero, giving a finite and an
  unramified infinite branch. On the finite branch \(E_c\) is bounded,
  \(F_c\) has residue \(k>0\). On the infinite branch the leading
  term of \(\rho\) is \((\lambda kr-\lambda+k)/[(\lambda+1)u]\);
  thus \(F_c\) has residue \(\lambda(1-kr)\).
  The residue for \(z\) is \(\lambda kr\), so \(G_{21}=f+z\) has
  residue \(\lambda<0\). The regular remainder has real Taylor
  coefficients, so its imaginary part is \(O(|\Im u|)\).
  Since \(\Im(1/u)=-\Im u/|u|^2\), feasibility is impossible sufficiently
  near this pole on the positive-height side.

## Extra contact 0 closes by secant compensation

Use the column transposition \((23)\) and the T85 overlap conventions
of [ZhengT85ArmBounds.md](ZhengT85ArmBounds.md).
The extra singleton \(n\) is unchanged. Its bracket lift \(\nu\) has
coordinates \(-1,1\) at positions 10 and 12 and zero elsewhere:
take \(a=(0,0,1,0), b=(0,1,1,1)\), so the matching product is the
indicator of \(2\to0\), and substitute \((a,-b)\) in the bracket basis.
Apply the T85 lift by linearity to the star part. Contact 0 fixes
\(\alpha_7=0\); always \(\alpha_5=0\). Normalize the star to one, and put
\(T=\alpha_1,\ p=\alpha_2,\ r=\alpha_3,\ A=\alpha_4,\ s=\alpha_6\).
The lower-projecting pivot height is \(h\), and the lift is
\[
 (-A,A+p+1,-1,-p,0,r+s+1,T-p-r-s-1,-r,A,
  p+r-T,-r-1-z,-p-A-1,A+1+z,T+1+h).
\]
Here \(r\) again denotes an ordinary gap. The cubic \(C=C_0+hQ\) has
\(C_0=-(p+1)(s+1)(z+r+1)\), \(Q=A(p-T)-(p+1)(r+s+1)\).
Thus \(Q\ne0\) on the cubic. Let \(J\) be the Hessian in the bracket basis.
At \(h=-C_0/Q\),
\[
 Q^2\det J=-4\big[(T+1)(p+1)(s+1)^2(z+r+1)^2F\big]^2,\qquad
 F=(p-T)A^2-(p+1)(T-z-1)A+(p+1)(z+1).
\]
For a symbolic reproduction, use the four pivots
\((6,12),(11,6),(9,10),(9,9)\) with values \(1,1,-1,-1\) in
the successive residual matrices. Use the determinant recurrence of
[the center-and-split proof](ZhengT40PositiveOverlap.md).
The residual height degree is three. If its successive coefficients
are \(D_0,D_1,D_2,D_3\), collecting gives the polynomial identity
\[
 Q^3D_0-C_0Q^2D_1+C_0^2QD_2-C_0^3D_3
 =-4Q[(T+1)(p+1)(s+1)^2(z+r+1)^2F]^2 .
\]
The elementary Hessian-kernel condition (or the
[Howard–Millson–Snowden–Vakil secant bound](https://doi.org/10.1112/plms/pds016))
forces \(F=0\). Rearranging,
\[
 (AT-1)(A+p+1)=pA^2+((p+1)(z+1)-1)A+(p+1)z\ge0 .
\]
This scalar sign is checked by boundary0_compensation in
[ZhengT55SignedStar.lean](MOC/ZhengT55SignedStar.lean).
Thus \(AT\ge1\), and the checked cofactor comparison of the T55+20
case applies. The extra ordinary term \(zM_n\) cannot reduce the gap.
The Hessian factor and interpretation of the indicators are paper arguments.

## Reduction

Assume all five indicated positive-height boundaries satisfy the
support inequality. A strict witness with none of the seven additional
contacts gives a nonempty open component on the curve with positive
height, all additional gaps positive, and \(L<0\).
At every regular finite boundary point the limit of \(L\) is nonnegative
by a boundary comparison (including the two proved above),
the known T55+20 case, or the zero-height case.
Define a function to be \(-L\) in that component and zero outside.
Subharmonic pasting applies at all regular boundaries. The function is
bounded above at the finitely many punctures by pole control, so extends
subharmonically across each. On a compact connected Riemann surface it is
constant, and the constant is zero because it vanishes above \(u=\infty\).
This contradicts the witness. The converse, from standalone T55 to its
boundaries, is immediate.

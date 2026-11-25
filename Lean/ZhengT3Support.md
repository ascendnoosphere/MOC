# The T3 support comparison

This proves Zheng's T3 case without a facet classification or numerical
certificate. It uses the lexicographic assignments of [Zheng, Appendix G,
preprint DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923)
and the paired-cofactor inequality from the [T15 proof](ZhengT15Support.md).
Repeated points and zero cross factors have the same common-weight exception
as in T15. We assume eight distinct marked points below.

Write \(g_i\) for nonnegative real upper-support gaps with T3 contacts
\(0,1,2,3,7,8\). Define
$$
 H=g_{19},\ G=g_{22},\ A=g_{14},\ B=g_{13},\
 C=g_4,\ F=g_{10},\ W=g_6,\ D_9=g_9,\ R=B+C-H.
$$
The same individual three-label alternation identities as in the
[T2 proof](ZhengT2MinorCone.md), applied with the new contact set, give
$$
 g_{16}=R+G,\quad g_{18}=A+C-R,\quad g_{20}=A+F-R,\quad
 g_{21}=B+F-R+D_9 .
$$
The remaining fiber equations are \(g_5=C\), \(g_{11}=F+W+D_9\),
\(g_{12}=A+W\), \(g_{15}=B+D_9\), \(g_{17}=R+G+W+D_9\), and
\(g_{23}=G+D_9\). Thus the eight chosen coordinates determine the
whole profile. For \(g_{21}\ge g_9\) they imply
$$
 \max(0,R)\le R+G,\qquad
 \max(0,R)\le\min(A,B)+\min(C,F).
$$
Choose \(a,c\ge0\) with \(a+c=\max(0,R)\),
\(a\le\min(A,B)\), \(c\le\min(C,F)\).
Use ten ordinary markers (written as row set \(\to\) column set):
$$
\begin{array}{c|l}
0\to2&a\\
0\to3&a+c-R\\
1\to3&c\\
3\to0&D_9\\
01\to03&C-c\\
01\to13&F-c\\
01\to23&G-(a+c-R)\\
02\to12&W\\
02\to23&B-a\\
03\to23&A-a
\end{array}
$$
They all vanish on T3 and satisfy three-label alternation. The eight
chosen coordinates of the resulting combination agree with the
prescribed gaps, hence so does the whole profile. This proves the
minor bound for every mixer when \(g_{21}\ge g_9\).

## Chart and comparisons

Normalize \(A_1=\infty,C_2=0,C_1=1\). The ratio of the same row swap
on contact pairs \(0,1\) and \(2,3\) is real, so \(C_3=t\) is real.
With \(A_2=z\) and \(l=(P_0-P_1)/(P_0-P_2)\),
\(k=(P_1-P_7)/(P_0-P_2)\), \(m=(P_2-P_8)/(P_0-P_2)\), the bracket
differences give
$$
 A_3=\frac{t(l-z)}{l-t},\quad x=A_0=z-r(z-l),\quad
 C_0=\frac{z-l-kx}{z-l-k},\qquad r=m/k .
$$
All \(t,l,k,m\) are real and nonzero; also \(t\ne1\), \(l\ne t\).
The first three formulas follow by taking the ratios of
\(t(x-C_0)(A_3-z)\), \((1-C_0)(z-t)A_3\), and
\((C_0-1)(x-z)(A_3-t)\) to \((x-C_0)(A_3-t)\).
A zero at an original denominator would give a marked coincidence:
\(z=t\) for \(l=t\), \(A_3=0\) for \(z=l\), or \(x=1\) for
\(z=l+k\). In homogeneous columns \((t(l-z),l-t)\) for \(A_3\)
and \((z-l-kx,z-l-k)\) for \(C_0\), the normalizer is
$$
 D=P_0-P_2=(x-1)(z-l)t(t-z)\ne0.
$$
Thus \(z\) is away from all normalizing roots at the given input.
Write
\(Q_i=(P_0-P_i)/(P_0-P_2)\). One has the rational identities modulo
real constants
$$
 Q_{21}-Q_9=Q_{13}+\frac{t}{t-1}Q_{22},\qquad
 Q_{21}-Q_9=Q_{19}-\frac{kr}{t-1}Q_4.
$$
For the first identity, the cleared numerator after subtracting the
right-hand side and multiplying by \(t-1\), then dividing by the
normalizer, equals
$$
 -[kr t^2+k t^2-kt+2l t^2-3lt+l+2t^2-t]/t .
$$
The second follows from \(g_{21}-g_9=g_{10}-g_4+g_{19}\) and the
nonconstant parts of \(Q_{10}\) and \(Q_4\), respectively
\((t-l)(kr-t+1)/(z-t)\) and \((l-t)(t-1)/(z-t)\).
They give the same identities for the real gaps.

The first identity closes \(t<0\) and \(t>1\). In a strict witness,
\(z\) is nonreal, since if \(z\) is real then all products in
the real-coefficient chart project to zero gap. The single-pole
selectors \(Q_6,Q_9,Q_4\) have real residues \(kl,\ kl(l-t)/t,\
(l-t)(t-1)\) at \(l,l,t\), respectively. Their gaps must be positive:
a nonzero real residue \(u/(z-z_0)\) projects with a sign independent
of the real pole \(z_0\) up to the sign of \(u\). Thus \(l/t>1\)
and \(k(t-1)>0\). The second identity then closes \(r\le0\).
It remains to treat \(0<t<1,r>0\).

## The large-\(l\) chamber

Suppose \(l>1\), and set \(L=l-t,\ P=1-t,\ K=-k>0\). From \(g_{10}\ge0\),
its one-pole residue \(-L(P-Kr)\) and the sign of the nonzero \(g_4\)
give \(S=P-Kr\ge0\).
In this chamber \(g_{14}\) likewise forces \(J=K(1-r)-(l-1)\ge0\).
The exact ratio is
$$
 Q_{14}=z-\frac{x(z-1-kr)}{x-1}=\frac{(1+kr)x-z}{x-1}.
$$
The real fractional-linear coefficients give
\(\Im Q_{14}=rJ\,\Im z/|x-1|^2\), including \(r=1\).
Writing the rotated difference \(\eta D=-i\omega\) with \(\omega\) real, the residue \(-LP<0\)
of \(Q_4\) gives \(\omega\Im z<0\). Thus
\(g_{14}=-\omega\Im Q_{14}\ge0\) gives \(J\ge0\). Since \(l>1,K>0\),
this also gives \(r<1\).

Put \(U=1-t-r(l-t)\). The exact bracket comparison is
$$
 U g_{20}=-r(l-t)g_{10}-(l-1)(1-t)g_{14}.                 \tag{1}
$$
It does not divide by \(U\) or distinguish simple from coalesced poles.
At the complex product level, multiplying the corresponding
combination of normalized ratios by \(D\) gives the constant
\(-l(t-1)(kr+1)\) times \(D\). This is a polynomial identity by
substituting the displayed homogeneous columns, and projects to (1). The cleared identity and its sign conclusion are checked in [ZhengT3Compensation.lean](MOC/ZhengT3Compensation.lean).
Since \(U=(1-r)S+rJ\ge0\), (1) forces \(g_{14}=0\).
The fiber identity
$$
 g_{21}-g_9=g_{20}+g_{13}-g_{14}
$$
is nonnegative. The ordinary decomposition applies, including if \(U=0\).

## The residual chamber and the mixed compensation

Assume \(l\le1\), and suppose \(\beta=g_9-g_{21}>0\); otherwise use
the ordinary decomposition. Let \(h=h_{17,+}\), exactly the mixed marker
of the T15 proof, with center permutation \((2,3,1,0)\). Explicitly the T15 proof uses
\(h=S_{02}+S_{30}+M(01\to03)-M(02\to23)\), and one may
take this formula as its definition here; facet extremality is not needed.
Its evaluations at
the eight independent coordinates
\((g_6,g_9,g_4,g_{10},g_{14},g_{13},g_{22},g_{19})\)
are \((0,1,1,0,1,0,0,0)\) by its four marker incidences.
It vanishes on the given six contacts. The signed minor evaluations are those of [Merikoski–Virtanen, DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X). Like its constituent entry
and subset markers, it obeys all three-label alternating identities.

The exact gap profile is the following signed-marker combination:
$$
\begin{aligned}
 \beta h
 &+g_{13}S_{02}+g_{10}S_{13}+g_{21}S_{30}
 +g_{19}M(01\to03)\\
 &+g_{22}M(01\to23)+g_6M(02\to12)+g_{20}M(03\to23).
\end{aligned}
$$
This agrees on the eight coordinates and therefore on the full
profile by the fiber table. In particular the coefficient of
\(M(03\to23)\) is \(g_{14}-g_{13}-\beta=g_{20}\),
so every listed ordinary coefficient is nonnegative.

By the chart identities, \(t g_9=(l-t)g_6\) and
\((1-t)(g_{13}+\beta)=t g_{22}\). Consequently
$$
 t\beta\le(l-t)g_6\le(1-t)g_6,\qquad
 (1-t)\beta\le t g_{22},
$$
and multiplication gives \(\beta^2\le g_6g_{22}\), as checked in the same Lean module.
Apply the [T15 paired-cofactor inequality](ZhengT15Support.md#the-paired-cofactor-inequality)
to \(\beta h+g_6M(02\to12)+g_{22}M(01\to23)\).
The remaining ordinary terms are nonnegative by the signed
squared-minor evaluation ([Merikoski and Virtanen,
DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X)).
The [two-orthogonal minor-table theorem](MOC/FourMinorTransport.lean)
extends this real-orthogonal comparison to complex unitary mixers. This completes T3.

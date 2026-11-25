# A direct proof for \(T_7\)

This proves the \(T_7\) support inequality of
[Zheng, Appendix G](https://doi.org/10.13140/RG.2.2.36790.25923)
without a facet list or case enumeration. Write
\(P_i=\prod_j(a_j+b_{\pi_i(j)})\), with the paper's zero-based
lexicographic row-to-column labels, and use lower gaps
\(g_i=\operatorname{Re}(\eta P_i)-h\ge0\).
Thus \(h=-H\) for upper height \(H\) after replacing \(\eta\) by \(-\eta\).
The contacts of \(T_7\) are \(0,1,2,4,7,8\).
The case \(\eta=0\) is trivial, and repeated entries or a zero cross-sum
are covered by [Zheng, Proposition 1.4 and Appendix B](https://doi.org/10.13140/RG.2.2.36790.25923).
Assume throughout that the eight signed spectral points are distinct.

If \(h=0\), the row-zero-to-column-zero three-label fiber has contacts
0 and 4 in even parity and 1 and 2 in odd parity. Its two parity classes
have equal sums and equal products of the matching values. The unknown
pair therefore has the same real part \(r\), and the product relation
has the form \(s z=t w\) with nonzero real \(s,t\). If \(r\ne0\), then
\(s=t\), so \(z=w\), contradicting the nonzero difference of matching
values related by a single transposition in that fiber. Thus the whole
fiber is active. Contact 7 is outside the fiber, so the
[checked fixed-assignment fibre comparison](ZhengT1Stabilizer.md) applies
([Zheng, Appendix G](https://doi.org/10.13140/RG.2.2.36790.25923)).

## Linear minor comparison

Use gaps \((A,B,C,D,E,F,G,J)=(g_3,g_6,g_9,g_{10},g_{12},g_{13},g_{16},g_{18})\)
and put \(X=A-C,\ Y=E-B-J\). Linear matching identities give
\[
g_{14}=E-B,\quad g_{15}=F-X,\quad g_{19}=F-Y,\quad
g_{22}=G-Y,\quad g_{23}=G-X-Y .
\]
Write \(I\to J'\) for the marker of \(\pi(I)=J'\).
Set \(x=\max(0,Y)\), \(y=\max(0,X)\). The ten markers
\[
(0\to2,\ 0\to3,\ 3\to0,\ 3\to1,\ 01\to13,\ 01\to23,\
02\to12,\ 02\to23,\ 03\to01,\ 03\to23)
\]
have coefficients
\[
(x,\ J-E+B+x,\ C-A+y,\ y,\ D,\ G-x-y,\
 B,\ F-x-y,\ A-y,\ E-B-x).
\]
This combination vanishes on the six contacts and has the eight
specified gap coordinates. The corresponding fourteen bracket
evaluation rows determine the profile, by linear elimination in
Eq. (4.5) of [Zheng](https://doi.org/10.13140/RG.2.2.36790.25923).
The five displayed gap formulas follow from the same equations.
All coefficients are nonnegative provided \(F,G\ge x+y\).
By the five gaps above it remains only to prove
\[
G\ge X\quad(X>0,\ Y<0),\qquad F\ge X+Y\quad(X>0,\ Y>0).
\tag{1}
\]
If \(Y=0\), the two comparisons follow from \(g_{15},g_{23}\ge0\).
The signed-weight minor identity of
[Merikoski and Virtanen](https://doi.org/10.1016/0024-3795(89)90709-X)
evaluates each marker at any unitary mixer as a squared minor. Thus (1)
suffices for the support inequality.

## Explicit rational chart

Assume \(h\ne0\). Use a common projective map on the signed spectra
to set the second signed list to \((\infty,0,s,t)\) and the first
list to \((1,y,z,w)\). Such a map sends the three distinct points
\(c_0,c_1,a_0\) to \(\infty,0,1\). All other points remain finite
and distinct. Use homogeneous coordinates \((v,1)\) and \((1,0)\),
with the infinity bracket taken as \(+1\) after a common sign change.
The determinant identity in
[Drury’s fractional-linear transport, DOI 10.13001/1081-3810.1239](https://doi.org/10.13001/1081-3810.1239)
preserves all matching values and the signed-weight objective after
absorbing the common nonzero scale into the support multiplier.

Write
\[
-i\eta(P_0,P_1,P_2,P_4,P_7,P_8)=(u,u+a,u+b,u+c,u+d,u+e),
\]
where the five offsets \(a,b,c,d,e\) are real. In this equation we
absorb the projective scale as just described, so \(h=-\operatorname{Im}u\).
The differences \(a,b,a-c,b-c,a-d,b-e\) are nonzero: each compares
one-transposition neighbors among the six contacts. The ratios
\(P_7/P_1=1/y\) and \(P_8/P_2=1/z\) give
\(y=(u+a)/(u+d)\) and \(z=(u+b)/(u+e)\).
Next
\[
P_2/P_0=\frac{z(y-s)}{y(z-s)},\qquad
P_4/P_1=\frac{z(y-t)}{y(z-t)}
\]
give the formulas for \(s,t\) below. Finally
\((P_1/P_0)(z-s)(w-t)=(z-t)(w-s)\) gives \(w\);
its coefficient cannot vanish, because then the original equation
with \(z-t\ne0\) would imply \(t=s\).
Writing
\[
S=ae+(a-d+e)u,\quad T=bd-ce+(b-c+d-e)u,\quad
\ell=a+b-c,
\]
the resulting chart is
\[
s=\frac{b(a+u)}S,\qquad t=\frac{(a-c)(b+u)}T,\qquad
w=\frac{(a+u)(b+u)\ell}{W},
\]
\[
W=abd+abe-ace+(2ab-ac+ad+be-ce)u+\ell u^2 .
\]
The displayed denominators are nonzero at a regular chart point.
Indeed the denominators in \(s,t\) come from solving linear equations
whose numerators are nonzero (simple spectra and nonzero matching
values). The same argument for \(w\) applies to the original
linear equation above. In fact its coefficient factors as
\(L_D W/[(u+e)ST]\), with \(L_D=ae-bd+(a-b-d+e)u\)
nonzero by \(y\ne z\). In particular chart substitution never
requires a genericity hypothesis on this regular input.

## Gap identities, including exceptional offset values

For all labels write \(f_i=-i\eta(P_i-P_0)\), so
\(g_i=-\operatorname{Im}f_i\). In the chart one computes
\[
f_i=u\left(\frac{p_i}{y(z-s)(w-t)}-1\right),\qquad
p_i=\prod_{\pi_i(j)\ne0}\bigl(A_j-C_{\pi_i(j)}\bigr),
\quad A=(1,y,z,w),\ C_1=0,\ C_2=s,\ C_3=t .
\tag{2}
\]
Put
\[
L_C=ab+\ell u,\qquad L_D=ae-bd+(a-b-d+e)u,\qquad
M=ab-ae-bd+ce .
\]
The following is the complete set of projected identities used:
\[
\begin{aligned}
g_6&=\frac{a(a-d)\operatorname{Im}u}{|u+a|^2},&
g_{10}&=\frac{(b-c)(b-e)\operatorname{Im}u}{|u+b|^2},\\
A&=\frac{ab(a-c)(b-c)\operatorname{Im}u}{|L_C|^2},&
g_{14}&=\frac{-b(a-d)(b-e)(d-e)\operatorname{Im}u}{|L_D|^2},\\
C&=-\frac{M}{b(a-c)}A,&
J&=-\frac{a-c}{b}\,g_{14}.
\end{aligned}
\tag{3}
\]
Define \(K=a(ab-e\ell)-b(ab-d\ell)\) and
\(N=(a-c)(c-e)+(b-c)(d-c)\). Then the additional identities are
\[
\begin{aligned}
K(G-X)&=(b-c)M X+bN Y,\\
K(F-X-Y)&=-aM X+(a-c)(ae-bd)Y .
\end{aligned}
\tag{4}
\]

Here are details to reproduce (3)–(4) as rational identities, with
no specializations of the spectrum. In (2) the pivot denominator
is nonzero at the given chart point. The four dedicated functions are
\[
\begin{aligned}
f_6 &= (d-a)u/(u+a),\\
f_{10} &= ((c+e-b)u+ce)/(u+b),\\
f_3 &= \big[ab\ell+(a^2+ab+b^2-c(a+b))u\big]/L_C,\\
f_{14} &= (e-b)S/L_D .
\end{aligned}
\]
Thus (3) follows by the rule
\[
-\operatorname{Im}\frac{m u+n}{k u+l}
=(kn-ml)\operatorname{Im}u/|ku+l|^2
\]
for real coefficients. For the last two entries of (3), the only
possible affine denominators for \(f_9,f_{18}\) are \(L_C,L_D\)
respectively. Their numerators as obtained from (2) are
\[
\begin{aligned}
L_C f_9 &= abd+abe-ace+(ab-ac+ad+be-ce)u,\\
L_D f_{18} &= abd-bcd-bd^2+cde+
  (ab+ad-ae-bc-bd+ce-d^2+de)u .
\end{aligned}
\]
The factors \(L_C,L_D\) cannot vanish at a regular nonreal \(u\):
\(L_C\) has constant term \(ab\ne0\), and vanishing \(L_D\)
would give \(y=z\).

For (4), the following partial-fraction coefficients of \(X_f=f_3-f_9\),
\(Y_f=f_{12}-f_6-f_{18}\), \(G_f-X_f=f_{16}-X_f\) and
\(F_f-X_f-Y_f=f_{13}-X_f-Y_f\) give a short verification. The entries
are stated as multiples of the coefficients in the first two rows
to avoid repeated large products:
\[
\begin{array}{c|cc}
 &1/L_C&1/L_D\\ \hline
X_f &ab(a-c)(b-c)/\ell+a(b-c)M/\ell&0\\
Y_f &0&-(a-d)(b-e)(d-e)\ell/(a-b-d+e)\\
K(G_f-X_f)&(b-c)M[X_f]_C&bN[Y_f]_D\\
K(F_f-X_f-Y_f)&-aM[X_f]_C&(a-c)(ae-bd)[Y_f]_D
\end{array}
\]
Here is why no other poles or polynomial parts are needed.
In the generic rational calculation, the pivot product factors as
\[
y(z-s)(w-t)=
-\frac{u(u+a)(u+b)L_C L_D^2}{(u+d)(u+e)STW}.
\]
Each product \(p_i\) has denominator dividing the denominator on the
right: each row and column occurs only once. Thus after canceling \(u\)
in (2), the only possible poles are \(u=-a,-b\) and the zeros of
\(L_C,L_D\). At the \(L_D\) zero the rows \(y,z,w\) and columns
\(s,t\) coincide, so every product has a vanishing factor there
by the pigeonhole principle. This cancels at least one factor of
\(L_D\), leaving at most a simple pole. At \(-a\) and \(-b\),
the nonzero residues are multiples of the markers \(13\to03\)
and \(23\to02\), respectively, by the coincidences
\(y=w=C_1=C_2=0\) at \(-a\) and \(z=w=C_1=C_3=0\) at \(-b\).
Their contributions to the four expressions in the table cancel.
For a direct check of the table, multiply (2) by the affine factor,
insert its zero using the chart formulas, and use the listed products.
At infinity the rows \(1,y,z,w\) approach 1, and the two finite
moving columns have finite limits distinct from 1 for generic
parameters. The difference of any two matching products is
\(O(1/u)\) relative to the pivot, so all four expressions in the table
are bounded at infinity.
The resulting identity is between rational functions with real
coefficients, up to real constants. Taking imaginary parts gives
(4). Equivalently, it can be checked by clearing denominators and
inserting the matching products at labels 3, 6, 9, 12, 13, 16, 18.
The rational identity, with \(K\) multiplied through as in (4),
extends to coincident pole locations or a zero leading coefficient
of \(L_C,L_D\); one can subtract its conjugate and clear denominators.
The regular spectral point, \(u+a,u+b,L_C,L_D\), and the original
chart denominators are all nonzero there. No genericity assumption
on the witness is used.

## Signs

If \(d=e\), (3) gives \(g_{14}=J=0\) and \(Y=0\). The linear
comparison already applies. Otherwise all first four numerators
in (3) are nonzero and each gap is strictly positive. By complex
conjugation we can assume \(b>0\): conjugating the rotated matching
values replaces \(u\) by \(-\bar u\) and negates all five offsets,
without changing gaps or \(\operatorname{Im}u\). From \(J\ge0\)
we obtain \(c>a\), and from \(C\ge0\) we obtain \(M\ge0\).
Put \(\epsilon=\operatorname{sgn}\operatorname{Im}u\). The first
four strict sign relations in (3) give
\[
\operatorname{sgn}(a-d)=\epsilon\operatorname{sgn}a,\quad
\operatorname{sgn}(b-c)=-\epsilon\operatorname{sgn}a,\quad
\operatorname{sgn}(b-e)=-\operatorname{sgn}a,\quad d>e .
\tag{5}
\]

If \(\epsilon=-1\) and \(a>0\), then \(b>c>a>0\) and \(d>e>b\).
It follows that
\(M=b(a-d)+(c-a)e<ab-\ell e<0\), since \(\ell>a>0\).
If \(\epsilon=-1\) and \(a<0\), then \(c>b>0\) and \(e<d<a<0\).
Since \(c-a>b\), we have \(M<b(a-d)+bd=ab<0\).
Both contradict \(M\ge0\). In particular the nontrivial chart cannot
be a negative-upper-height witness.

Now \(\epsilon=1\). If \(a>0\), (5) gives \(b<e<d<a<c\).
Then
\(M+b(a-c)=b(a-d)+(c-a)(e-b)>0\),
so (3) gives \(X=A[M+b(a-c)]/[b(a-c)]<0\).
No inequality in (1) remains. If \(a<0\), then \(c<b,\ e<b,\ d>a\).
The inequality \(M\ge0\) forces \(e>0\); also
\(d\le a+(c-a)e/b<c\). We have proved
\[
a<0<e<d<c<b .
\]
In this chain \(K>0\). Indeed \(ab-e\ell,ab-d\ell\) are negative
when \(\ell\ge0\); when \(\ell<0\), use \(\ell>a\) and \(e,d<b\)
to reach the same conclusion. Also \(N<0\) and
\((a-c)(ae-bd)>0\).
For \(X>0,Y<0\) both terms of \(K(G-X)\) in (4) are nonnegative.
For \(X,Y>0\) both terms of \(K(F-X-Y)\) are nonnegative.
This proves (1) and the desired unconditional \(T_7\) comparison.

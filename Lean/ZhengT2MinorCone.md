# T2: chart identity and constructive minor decomposition

This proves the full T2 support inequality of [Zheng, Appendices E and G](https://doi.org/10.13140/RG.2.2.36790.25923), without a facet classification.

## The needed chart

Use signed spectra \(A,C=-b\) and lexicographic row-to-column
matching products \(P_j\). Put \(g_j=\operatorname{Re}(\eta P_j)-h\ge0\)\nwith \(h\) the common lower support. In a support direction the six labels
\(0,1,2,3,6,8\) are contacts. Repeated entries and zero cross-sums
are covered by the checked order-four coincidence theorems.
In the distinct case, each one-swap difference is nonzero. The
ratio of any two such contact differences is real.

Compare the swaps \(0\leftrightarrow1\) and \(2\leftrightarrow3\)
of permutation labels: both swap positions 2 and 3. The quotient
after cancelling matching factors is the cross ratio of
\(A_1,C_1,C_2,C_3\), up to sign. Comparing
\(P_0-P_6\) with \(P_2-P_8\) uses the same two swapped column values
and gives the cross ratio of \(A_0,A_1,A_2,C_2\).
These are real, so each quartet is on a generalized circle.
Send \(A_1,C_2,C_1\) to \(\infty,0,1\). Write
\(A_0=z,A_2=sz,C_3=t\), with \(s,t\) real and neither zero nor one.

Let \(l=(P_0-P_1)/(P_0-P_2)\), \(k=(P_0-P_6)/(P_0-P_2)\).
They are real. Using infinity bracket \(+1\) (a common sign),
and writing \(x=A_3,y=C_0\), the three differences are
\[
P_0-P_2=(z-y)(x-t),\quad P_0-P_1=t(z-y)(x-sz),\quad
P_0-P_6=sz(1-y)(x-t).
\]
Thus \(x=t(l-sz)/(l-t)\) and \(y=z(s-k)/(sz-k)\),
and the denominators are nonzero at distinct marked points.
Use the corresponding homogeneous coordinates for \(x,y\).
Then \(D=P_0-P_2=stz(z-1)(t-sz)\) and
\[
 (P_7-P_9)/D=-(l-t)(s-k)/(st).
\]
The cleared equality is checked in
[ZhengStageOneCharts.lean](MOC/ZhengStageOneCharts.lean).
Since \(\eta D\) is purely imaginary, the projected gaps
satisfy \(g_7=g_9\). No other gap is assumed strict.
The projective normalization simply multiplies every matching
product and the signed evaluation by a common nonzero factor.

## Constructive minor decomposition

Put
\[
 A=g_{12},\ B=g_{13},\ C=g_4,\ E=g_7,\ F=g_{10},\ G=g_{22},\
 H=g_{19},\quad R=B+C-H .
\]
For any one prescribed assignment of a row to a column, the signed
alternating sum of gaps in that fiber is zero. For matching products this
is the fixed cross bracket times the \(3\times3\) determinant of the
remaining rank-at-most-two kernel. For gaps it persists by real
projection and subtraction of a constant in a fiber with three even
and three odd terms. Using these identities gives
\[
\begin{array}{c|l}
\text{fixed assignment} & \text{result after earlier identities}\\\hline
0\mapsto0 & g_5=C\\
0\mapsto1 & g_{11}=F\\
3\mapsto3 & g_{14}=A\\
2\mapsto3 & g_{15}=B\\
3\mapsto1 & g_{16}=R+G\\
1\mapsto3 & g_{17}=R+G\\
1\mapsto0 & g_{18}=A+C+E-R\\
2\mapsto0 & g_{20}=A+F-R\\
2\mapsto2 & g_{21}=B+F-R\\
1\mapsto2 & g_{23}=G+E .
\end{array}
\]
Every equality uses just its single six-term fiber relation and the
previously specified contacts and equalities.

We build weights on the following ordinary entry and subset markers;
for example the row for \(e\) is the indicator
\(\mathbf1_{\sigma(\{0,1\})=\{0,3\}}\).
\[
\begin{array}{c|ccccccccccc}
\text{weight}&a&b&c&d&e&f&j'&h&i&j&k\\\hline
I&0&0&1&3&01&01&01&02&02&03&03\\
J&2&3&3&0&03&13&23&13&23&12&23
\end{array}
\]
All these markers vanish at the six specified contacts. Each marker
also satisfies every three-label alternating fiber relation: if two
choices remain for two free rows of the same membership class in \(I\),
the transposition exchanges the terms with opposite signs. Among the
three free rows, at least two belong to the same class, so swapping
those rows gives this involution. At 7 and 9 the weighted values are
\(h+j\) and \(h+d\) respectively; require \(j=d\). Thus by the preceding
fiber identities it suffices to match the seven coordinates above.
Their values in the proposed nonnegative combination are
\[
 A=a+k,\quad B=a+i+j,\quad C=c+e,\quad E=h+j,\quad F=c+f+j,\quad
 G=b+j',\quad H=b+e+i .
\]

Here is a direct allocation. Let \(T=\max(0,R)\). By nonnegativity of
\(G,H,g_{16},g_{18},g_{20},g_{21}\), and of \(A,B,C,E,F\), we have
\[
 T \le R+G,\quad
 T\le A+C+E,\quad T\le B+C,\quad T\le A+F,\quad T\le B+F.
\]
Take \(a,c,d\) nonnegative with
\(a+c+d=T,\ a\le A,\ c\le C,\ d\le E,\ a+d\le B,\ c+d\le F\)
as follows. If \(T>A+C\), take \(a=A,c=C,d=T-A-C\);
the first three relevant upper bounds on \(T\) give the requirements.
Otherwise take \(a=\min(A,B,T),c=T-a,d=0\).
Then \(c\le\min(C,F)\): if the minimum defining \(a\) is \(T\),
this is immediate, and if it is \(A\) or \(B\), it follows respectively
from the two bounds on \(T\) using that term (and \(T\le A+C\) in this
case).

Set
\[
 b=T-R,\ e=C-c,\ f=F-c-d,\ j'=G-b,\ h=E-d,\ i=B-a-d,\ j=d,\ k=A-a.
\]
All are nonnegative. Substitution gives the seven target values,
including \(b+e+i=B+C-R=H\). Hence the whole matching gap vector is an
ordinary nonnegative minor combination. Applying the standard squared-minor
evaluation of these indicators proves the support bound for every mixer.
No assumption about the full facet list or its incidence with T2 is used.

[ZhengT2MinorCone.lean](MOC/ZhengT2MinorCone.lean) checks the constructive allocation and the seven gap coordinates. The marker evaluation is the signed minor law of [Merikoski–Virtanen, DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X).

# Direct certificates for Zheng's Group IV

This proves the support inequality for all three Group IV contact sets
\(T_{21},T_{22},T_{23}\) of [Zheng, Appendix G](https://doi.org/10.13140/RG.2.2.36790.25923).
It does not use facet completeness, a list of maximal supports, or any
numerical spectra. All indices below are zero-based, with permutation
labels in lexicographic row-to-column order.

## Common inputs

Write \(P_\sigma=\prod_i(a_i+b_{\sigma(i)})\) and use lower gaps
\(G_\sigma=\operatorname{Re}(\eta P_\sigma)-H\ge0\), where
\(H=\min_\sigma\operatorname{Re}(\eta P_\sigma)\). Changing the sign of
\(\eta\) handles upper support. The zero multiplier is trivial. For
repeated spectra or a vanishing cross-sum, the coincidence cases apply
([Zheng, Proposition 1.4 and Appendix B](https://doi.org/10.13140/RG.2.2.36790.25923)).
In the remaining case distinct permutations related by one transposition
give distinct products: their difference factors into two within-spectrum
differences and the two remaining cross-sums.

At \(T_{21}\) and \(T_{23}\), labels \(3,5,9,11\) form a contact
rectangle: at label 3 the disjoint position swaps \((1,2),(0,3)\)
give 5 and 9, and together give 11. At \(T_{22}\), the swaps
\((0,2),(1,3)\) at label 2 give labels 8 and 4 and together give 10.
A disjoint-swap rectangle satisfies \(P_{00}P_{11}=P_{01}P_{10}\).
If all four values are \(H+i v_{ij}\) after rotation with \(H\ne0\),
their product relation equates both the sum and the product of the two
diagonal pairs of \(v\)'s. The pairs are equal as multisets, so an
adjacent pair coincides. This contradiction gives \(H=0\).
At \(H=0\), three known nonzero purely imaginary products on a rectangle
force the fourth to be purely imaginary as well. In \(T_{22},T_{23}\),
labels 2, 3 and 12 then force 13 by swaps \((0,1),(2,3)\) at 2.

Use the bracket basis of [Zheng, Appendix A](https://doi.org/10.13140/RG.2.2.36790.25923).
Since \(H=0\), the gap function is the image of the projected matching
point \(m\) under the evaluation map of Eq. (4.5). The matching cubic
\(C(m)\) vanishes by bracket polarization
([FourMatchingPolarization.lean](MOC/FourMatchingPolarization.lean)).
Write \(I\to J\) for the indicator of \(\sigma(I)=J\).
Its evaluation for a fixed unitary mixer is the nonnegative squared
modulus of the corresponding minor, by the signed-weight identity of
[Merikoski and Virtanen](https://doi.org/10.1016/0024-3795(89)90709-X).
It suffices to express \(G\) as a nonnegative sum of these indicators.

## T22

The closure contacts are \(2,3,4,8,10,12,13\). Put
\((a,b,c,d,e,f,g)=(G_0,G_1,G_6,G_7,G_9,G_{16},G_{18})\).
The linear lift is
\[
m=(a-b-c+d,-a+b+c-d,-g,-b+d,b-d,-a+b+c-d,d+f,-c+d,c-d,
    a-d-f,-b+d,-c+d,-e,-a+b+c-d+e+f+g).
\]
Set \(A=a-b-c+d,\ B=f-a+b+c\). Then
\(C=(ad-bc)(e+g+B-d)-aeg\). The other gaps needed are
\[
\begin{array}{c|rrrrrrrr}
j&5&14&11&15&17&19&20&22\\ \hline
G_j&a-b&a-c&c-d+e&b-d+e&B-d+e&c-d+g&b-d+g&B-d+g .
\end{array}
\]
If \(A<0\), then \(a>0\) (otherwise \(b=c=0\)) and
\(ad-bc=aA-(a-b)(a-c)<0\); also \(e+g+B-d=e+g+f-A>0\).
Hence \(C<0\). If \(B<0\), then \(a>0\) and \(e,g\ge d-B>d\)
by gaps 17 and 22. The factor multiplying \(ad-bc\) is positive,
so \(ad-bc\le ad\) gives \(C\le a[dB-(e-d)(g-d)]<0\).
Cubic vanishing thus implies \(A,B\ge0\).

Choose \(s\) in the interval
\[
[\max(0,b+c-a,d-e,d-g),\ \min(b,c,d,B)].
\]
Every lower bound is at most every upper bound by the displayed
gap inequalities, \(A,B\ge0\), and \(a,b,c,d,e,f,g\ge0\).
For the markers
\[
(0\to3,\ 1\to1,\ 2\to2,\ 3\to0,\ 01\to01,\ 01\to23,\ 02\to02,\ 02\to13)
\]
take the nonnegative coefficients
\((g-d+s,b-s,c-s,e-d+s,s,B-s,a-b-c+s,d-s)\).

## T23

The closure contacts are \(2,3,5,9,11,12,13\). Put
\((a,b,c,d,e,f,g)=(G_0,G_1,G_6,G_7,G_8,G_{16},G_{18})\).
Here
\[
m=(a-b-c+d,-a+b+c-d,-a+b-g,-b+d,b-d,0,c-e+f,0,c-d,
    a-c+e-f,-a+c-e,-c+d,e,c-d-e+f+g).
\]
Set \(A=b+c-a-d,\ B=f-e+c,\ D=c-d+f+g\).
Then \(C=(ad-bc)D+be(c+g-d)\), and
\[
\begin{array}{c|rrrrrrrr}
j&4&10&14&15&17&19&21&23\\ \hline
G_j&b-a&-c+d+e&a-c+e&b-d&B-a+b-d&c-d+g&a-d+g&B+g-d .
\end{array}
\]
If \(A<0\), then \(b>0\) and \(ad-bc=(b-a)(b-d)-bA>0\).
Also \(D=G_{19}+f>0\): equality would give \(G_{19}=f=0\);
then \(G_{23}\ge0\) forces \(e=0\), and \(G_{17}=A\ge0\) is a
contradiction. Both terms of \(C\) are nonnegative and the first
is positive. If \(B<0\), gap 17 gives \(b>a+d\), gap 23 gives
\(g-d\ge-B>0\), and \(e>c\). Since \(D\ge0\),
\[
C\ge b[-cB+(e-c)(g-d)]>0.
\]
Cubic vanishing therefore implies \(A,B\ge0\).

Choose \(s\) in the interval
\[
[\max(0,c-e,a+d-b,d-g),\ \min(a,c,d,B)].
\]
Its bounds follow from the displayed gaps and \(A,B\ge0\).
For the markers
\[
(0\to3,\ 1\to1,\ 2\to0,\ 3\to2,\ 01\to01,\ 01\to23,\ 03\to02,\ 03\to13)
\]
take the nonnegative coefficients
\((g-d+s,a-s,e-c+s,d-s,s,B-s,b-a-d+s,c-s)\).

## T21

Put \((a,b,c,d,e,f,g,h)=(G_1,G_2,G_6,G_7,G_8,G_{13},G_{16},G_{18})\).
Then
\[
m=(-a-c+d,a+b+c-d+f,a-h,-a+d-f,a-d,0,c-e-f+g,0,c-d,
-b-c+e+f-g,b+c-e,-c+d-f,-b+e,b+c-d-e+g+h).
\]
Let \(v=e-b-c,\ k=v-g,\ x=a-d,\ y=h-d\). The restricted cubic is
\[
C=b[c(f+x)+x(f+y)]+c(d+x)(f+k)+v(d+x)(f+y).
\]
The gaps used are \(G_{14}=v,\ G_{15}=a-d+f,\ G_{17}=x-k,\
G_{21}=h-d+f,\ G_{23}=y-k\).
If \(k>0\), then \(v\ge k>0\) by \(g\ge0\), and \(x,y\ge k>0\).
The first two terms are nonnegative and the last is positive,
contradicting cubic vanishing. Thus \(k\le0\).

Choose \(s\) in
\[
[\max(0,d-f,d+v-g),\ \min(a,d,h)].
\]
All the comparisons are consequences of the stated gap inequalities or
\(k\le0\). For the markers
\[
(0\to3,\ 2\to0,\ 3\to2,\ 01\to23,\ 02\to01,\ 02\to23,\
 03\to02,\ 03\to12,\ 03\to13)
\]
take the nonnegative coefficients
\((h-s,v,s,g-v-d+s,b,f-d+s,a-s,d-s,c)\).

## Verification and Lean scope

The linear lifts are obtained from the bracket product evaluations
\(\prod_i(z_i-z_{4+\sigma(i)})\) in Eq. (4.5) of
[Zheng](https://doi.org/10.13140/RG.2.2.36790.25923).
The rows for the prescribed contacts and the chosen gap coordinates
give fourteen equations in fourteen bracket coordinates. Substitution
of each displayed lift gives the prescribed gaps; elimination of the
homogeneous equations gives zero, so these rows determine the lift.
The other rows used above give the displayed gap formulas. Each marker
combination has the required zeros and gap coordinates, so it is the
whole gap function by the same linear inverse. No other contact patterns
or mixer values are checked.

[ZhengGroupIV.lean](MOC/ZhengGroupIV.lean) verifies the factored cubics,
the sign implications from cubic vanishing, and the existence of the
nonnegative minor coefficients. The linear identification of the
actual spectral gap and its evaluation on the named minor markers
are the paper steps in this note.

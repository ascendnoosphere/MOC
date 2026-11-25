# T18, T19 and T20: direct cubic certificates

These three order-four support comparisons are in Group II of
[Denzel Zheng, Appendices E and G, DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923).
The proof uses the bracket cubic and direct nonnegative sums of squared
minors. It does not require classification of the contact cones.

Use zero-based row-to-column assignment labels and lower gaps
\(G_j=\operatorname{Re}(\eta P_j)-H\ge0\), with the common lower
height \(H\). Reversing the support direction gives the upper
version. Repeated eigenvalues and zero cross-sums are covered by the
[repeated-spectrum theorem](MOC/TwoExceptions.lean) and the
[opposite-entry theorem](MOC/FourCoincidence.lean), respectively.
In the other cases, a single swap changes the matching product.
The disjoint swaps \((01),(23)\) make \(0,1,6,7\) a rectangle
in each of the three contact sets. Its two diagonal products agree.
If the height were nonzero, equality of real and imaginary parts
would say that the two pairs of imaginary offsets have equal sum
and product. An adjacent matching product would then coincide.
Thus \(H=0\).

At zero height the gaps are the real projection of the matching point,
so \(C=0\) by [the bracket polarization theorem](MOC/FourMatchingPolarization.lean).
For \(T_{18}\) use
\[
(a,b,c,d,e,f,g,h)=(G_2,G_4,G_9,G_{10},G_{12},G_{13},G_{16},G_{18}).
\]
For \(T_{19},T_{20}\) replace only \(G_4\) by \(G_3\).
The exact matching lifts are written in
[ZhengEarlyRectangles.lean](MOC/ZhengEarlyRectangles.lean). They are
obtained by expressing the product of four matching brackets as
a linear form in the Appendix A basis: replace a crossing pair by
\([ik][jl]=[ij][kl]+[il][jk]\) for \(i<j<k<l\).
Set the six contact rows to zero and the eight gap-coordinate rows
to the displayed gaps and solve the linear equations. These lifts
are inverse to those rows. Thus reproducing the six zeros and the eight
coordinates suffices to identify a proposed minor sum. The Lean
module checks the factored cubics and the coefficient inequalities;
matching those scalar charts to the actual profile is the paper step.

Write \(I\to J\) for the indicator \(\sigma(I)=J\). Its evaluation
under a unitary is a squared minor, by
[Merikoski–Virtanen, DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X).
All three charts have nonnegative coordinates.

## T18

The extra contacts are \(3,8\). The cubic is
\(ach-adf-bce=0\). The gaps at \(5,14,19,20,21,22\)
give, respectively,
\[
a\le b,\quad a\le e,\quad e\le f+h,\quad b\le d+h,
\quad D\le c+d+f,\quad D\le g,\qquad D=b+e-a-h.
\]
We need \(h\ge a\) and \(D\le d+f\).
If \(a,c>0\), the cubic gives the nonnegative identity
\[
ac(-D)=adf+c(b-a)(e-a)\ge0.
\]
Then \(D\le0\) and \(h\ge b+e-a\ge a\).
If \(c=0\), gap 21 gives \(D\le d+f\); and if also \(a>0\),
then \(df=0\) by the cubic, so one of \(h\ge e-f\), \(h\ge b-d\)
gives \(h\ge a\).
If \(a=0<c\), then \(be=0\). According as \(b=0\) or \(e=0\),
gap 19 or 20 bounds \(D\) by \(f\) or \(d\).
This proves the required two inequalities including the zero cases.

Take \(s,t\ge0\) with \(s\le\min(e-a,f)\), \(t\le\min(b-a,d)\),
and \(s+t=\max(0,D)\). Such a split exists: the four pairwise
sums from the minima are at least \(D\) by \(h\ge a\),
gaps 19 and 20, and \(D\le d+f\). In particular \(s+t\le g\).
The ordinary markers and coefficients are
\[
\begin{array}{c|rrrrrrrrrr}
 &0\to2&0\to3&1\to3&2\to1&3\to0&01\to03&01\to13&01\to23&02\to23&03\to23\\ \hline
 &s&h-b-e+a+s+t&t&a&c&b-a-t&d-t&g-s-t&f-s&e-a-s .
\end{array}
\]
The coefficients reproduce \(a,b,c,d,e,f,g,h\) and the six contact zeros.

## T19

The extra contacts are \(4,8\). Here \(ach+d(be-af)=0\).
Gaps \(5,14,15,19\) give \(b,e\ge a,\ b\le c+f,\ e\le f+h\).
Put \(u=e-a-h\) and \(v=b-a-c\). Gaps \(17,22,23\)
give \(v,u,u+v\le g\). Gap 21 gives \(u+v\le f-a+d\).

We claim \(f\ge a\) and \(u+v\le f-a\). If \(a,d>0\), use
\[
ad\,[f-(b+e-a)]=ach+d(b-a)(e-a)\ge0.
\]
If \(d=0\), the bound on \(u+v\) is gap 21. If additionally \(a>0\),
the cubic forces \(ch=0\), so gap 15 or 19 gives \(f\ge a\).
If \(a=0<d\), the cubic forces \(be=0\), hence either \(v\le0\)
or \(u\le0\), and the other is at most \(f\) by gaps 15 and 19.
The claimed inequalities follow.

Set \(s=\max(0,u)\), \(t=\max(0,v)\).
Since \(u,v\le f-a\), \(u+v\le f-a\) and \(f-a\ge0\),
we have \(s+t\le f-a\). The same argument gives \(s+t\le g\).
Also \(s\le e-a\), \(t\le b-a\). The decomposition is
\[
\begin{array}{c|rrrrrrrrrr}
 &0\to2&0\to3&3\to0&3\to1&01\to02&01\to13&01\to23&02\to23&03\to01&03\to23\\ \hline
 &s&h-e+a+s&c-b+a+t&t&a&d&g-s-t&f-a-s-t&b-a-t&e-a-s .
\end{array}
\]
Again these are nonnegative and reproduce the six zeros and eight
gap coordinates.

## T20

The extra contacts are \(5,8\). The cubic is
\[
c[ah-(a-b)e]+d[be-af]=0.
\]
Gaps \(4,14,15,19,20,22\) give respectively \(a\ge b\),
\(e\ge a\), \(b\le c+f\), \(e\le f+h\), \(a-b\le d+h\),
and \(e-b-h\le g\).

We claim \(f\ge b\) and \(h\ge a-b\).
If \(c=d=0\), these are gaps 15 and 20.
Otherwise, if \(f<b\), then \(a>0\) and
\(be-af\ge a(b-f)>0\); also \(ah-(a-b)e\ge be-af\) by
\(f+h\ge e\). This makes the cubic positive.
If \(h<a-b\), then \(a>0\) and \(ah-(a-b)e<0\) by \(e\ge a\);
the same comparison says \(be-af\le ah-(a-b)e\).
The cubic would then be negative. This proves both bounds.

Put \(s=\max(0,e-b-h)\).
It satisfies \(s\le e-a,f-b,g\) by the new bounds and gaps 19 and 22.
Use the following ordinary decomposition:
\[
\begin{array}{c|rrrrrrrrr}
 &0\to2&0\to3&2\to1&3\to0&01\to02&01\to13&01\to23&02\to23&03\to23\\ \hline
 &s&h-e+b+s&a-b&c&b&d&g-s&f-b-s&e-a-s .
\end{array}
\]
This last sum is also nonnegative and agrees with the given gaps on
the determining rows. This completes all three support comparisons.

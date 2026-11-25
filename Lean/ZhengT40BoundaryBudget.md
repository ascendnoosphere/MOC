# Group V: T40 boundary calculations

## Checked T40 comparison and remaining boundaries

Use the normalized chart and labels from
[Zheng, DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923)
as specified in [the dependency analysis](ZhengT40AndT85Dependencies.md).
The six T40 contacts are `0,1,5,9,14,18` in row-to-column lexicographic order. For the positive mixed ray, normalize \(a-d=1\);
the other orientation is obtained by transposition. Set
\(c=b+1+C,\ f=1+F,\ t=1+D\), with \(b,C,s,F,d,e,D\ge0\).
A seventh contact means at least one of these seven margins is zero.
Conjugation by \((01)(23)\) exchanges \(b,e\) and \(d,F\), fixing \(C,D,s\).

* The \(s=0\) chart is the repaired [T85 overlap](ZhengT85Independent.md).
* For \(b=0\) or \(e=0\), the [standalone boundary calculation](ZhengT40Standalone.md) finds an exact square factor for the spectral Hessian determinant. It forces \(CD\ge1\); the sign implication and rotation comparison are checked in Lean. The symbolic Hessian-factor identity itself is a paper calculation, not a checked Lean theorem.
* `rotation_bound_sharp` in `MOC/ZhengT40RotationBound.lean` sharpens a separate sufficient bound to \(T\ge(5+1/m)/4\). The previous theorem is retained as a wrapper. This does not close more contact charts.
* The remaining chart types are \(C=0\), \(D=0\), and \(d=0\) or its conjugate \(F=0\). None is closed here.

## Reciprocal budget on the C=0 chart (paper calculation)

Write
\[
W_0=(1+F)(1+b)(1+d)(1+e)-Fbde,
\qquad
W_s=1+F+b+d+e+Fb+Fd+be+de.
\]
The symbolic elimination on this chart proposes the following Hessian-factor equation
\[
(1+D)(W_0+sW_s-4Fbdes)+D^2sW_0=0.
\]
The full factor identity is not verified here. The following budget is proved conditional on the displayed equation, and is not asserted as a checked spectral restriction. Since \(W_0>0\), every such solution has \(F,b,d,e,s>0\). Dropping the last nonnegative term yields
\[
\left(\frac1F+\frac1e\right)\left(\frac1d+\frac1b\right)
+\frac{1+F+b+d+e}{Fbde}+\frac{W_0}{sFbde}\le4 .
\]
This gives a necessary joint lower budget on the five remaining arms. No sufficient weighted rotation inequality follows here.

## Quaternion identity for the mixed term (paper)

Move the anchor \(\pi_{22}=(3,2,0,1)\) to the identity. In target-row Hodge indices the four arms \(d,F,b,e\) are the plus/minus pairs on entries \(20,01\), and \(s\) is the minus arm on entry \(12\). With the usual unit-quaternion convention, let \(L=L(q)\) and \(R=R(r)\). The mixed term is
\[
4h=(L_{00}+R_{00})^2+(L_{22}+R_{22})^2
+2(L_{20}^2+R_{20}^2)-(L_{11}-R_{11})^2
=8\sum_i q_i^2r_i^2-16\left(\prod_iq_i+\prod_i r_i\right).
\]
For example, the rotation-entry formulas give
\(L_{11}^2-L_{20}^2=2\sum_iq_i^4-1+8\prod_i q_i\) and
\(\sum_iL_{ii}^2=4\sum_iq_i^4-1\). Consequently the pure \(L\) terms are \(1-16\prod_i q_i\). Likewise for \(R\), and the cross terms are \(2\sum_i L_{ii}R_{ii}=8\sum_i q_i^2r_i^2-2\). This identity is not a sign comparison.

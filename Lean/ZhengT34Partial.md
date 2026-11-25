# T34: a closed rectangle branch and a boundary threshold

Use Zheng's lexicographic row-to-column labels and bracket basis
([preprint DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923),
Appendices A, D and E). The mixed term for T34 is $d f_{70}$; the seven
ordinary coefficients $(p,r,a,b,c,q,s)$ multiply
$(f_0,f_1,f_2,f_{12},f_{39},f_{67},f_{72})$ in this chart.
The following proves this contact chart directly, without a list of
all facets. The support conclusions below do not close all of T34.

## The T34 minor chart

Write \(n_{I,J}(\sigma)=\mathbf1_{\sigma(I)=J}\). Expanding the
matching products shows that their gap function belongs to the span of
these marker functions. Triple markers equal the singleton markers
for complements. The singleton span has dimension at most ten:
there are the constant and at most nine independent entries of the
four-by-four permutation table after the row and column sum relations.
For pair markers the difference
\(n_{I,J}-n_{I,J^c}=\sum_{i\in I,j\in J}n_{\{i\},\{j\}}-1\)
belongs to the singleton span. The sums \(n_{I,J}+n_{I,J^c}\)
are the markers of a three-by-three permutation of the unordered
pair partitions, whose span has dimension at most five by the same
row and column argument. The constant is shared. Thus the total
marker span has dimension at most fourteen.

The evaluations at labels \(2,3,5,9,10,12\) are independent. In
that order, markers uniquely equal to one on one of these six labels
are \(14\to14,\ 13\to14,\ 3\to3,\ 4\to1,\ 3\to1,\ 1\to3\).
Here \(14\) denotes the pair, whereas \(1\) denotes a singleton.
The ordinary rays in order \(p,r,a,b,c,q,s\) are the markers
\(1\to4,\ 12\to34,\ 13\to34,\ 14\to24,\ 14\to13,\ 2\to2,\ 12\to12\).
The eight ray functions listed above vanish at these six contacts;
for the seven ordinary ones this is the assignment test
\(\sigma(I)\ne J\), and for \(f_{70}=h_{4231,+}\) it follows
by inserting the six assignments in the fixed-point and pair parts
of the formula in Zheng §4.1. They are isolated, in the order
\(p,r,a,b,c,q,d,s\), at the assignments
\[
\begin{array}{c|rrrrrrrr}
\text{label} & 18 & 16 & 13 & 8 & 4 & 14 & 11 & 7\\
\text{assignment} & 4123 & 3412 & 3142 & 2314 & 1423 & 3214 & 2431 & 2143.
\end{array}
\]
That is, evaluating the eight rays at any assignment in the row
gives one on its own ray and zero on the others. This verifies eight
independent generators in the at-most-eight-dimensional contact
subspace, so they form a basis. Its coefficients are the actual gaps
at the isolated assignments and are nonnegative, without assuming
Zheng's general polytope certificate. If \(d>0\), any additional
contact must be a zero of \(h_{4231,+}\). By its relative-permutation
formula there are nine derangements and four of the eight oriented
three-cycles in the zero set. The original six and the seven marked
ordinary-ray assignments already give thirteen distinct zeros.
Consequently any seventh contact forces at least one of
\(p,r,a,b,c,q,s\) to be zero.

## Lift of the marker chart to the fourteen bracket coordinates

This is the lower-support convention: the projected products equal
the gap plus their common supporting value \(h\); for an upper
support apply the same formulas with the negated projection.
For any equal-size \(I,J\), put \(a_i=\mathbf1_{i\in I}\) and
\(e_j=1-\mathbf1_{j\in J}\) in signed-spectrum notation. Then
\(\prod_i(a_i-e_{\sigma(i)})\) is zero unless \(\sigma(I)=J\);
in that event it has the same sign \((-1)^{4-|I|}\) for every
assignment. The signed bracket lift of this degenerate choice is
therefore a lift of \(n_{I,J}\). In the bracket basis, the lift's
coordinates are exactly
\[
  (-1)^{4-|I|}\prod_{(u,v)\in B_k}(z_u-z_v),\qquad
  z=(a_1,a_2,a_3,a_4,e_1,e_2,e_3,e_4).
\]
This describes each coordinate as an oriented crossing between the
two color classes. The constant profile comes from \(I=J=\varnothing\)
and lifts to the last coordinate only. The mixed ray is obtained by
the half-sum of the singleton and signed pair markers in Zheng §4.1.
Summing these lifts gives
\[
(-b-c-d,\ a+b+c+d,\ c-p,\ -a-c-d-q,\ c+d+q,\ d,\ -a+r+s,\
 -d,\ b+d,\ a+d+q-r,\ -d-q,\ -a-b-d,\ b,\ d+p+r+h),
\]
the \(\texttt{t34HeightLift}\) in FourContactCertificate.
The bracket-coordinate projection is injective: its range contains
the complete marker span by the color construction. The contact
rank and the eight independent generators above force that span
to have dimension fourteen, equal to the source dimension. Thus
these are indeed the coordinates of the actual projected profile.
This does not use a precomputed permutation matrix determinant.

## Zero height and extra contact 13

Take the six T34 contacts $\{2,3,5,9,10,12\}$.
At label 2 (one-line $1324$, one-based), the two disjoint slot swaps
$(3\,4)$ and $(1\,2)$ give labels 3 and 12, and doing both gives label 13.
If that fourth label is also active, distinct spectra and nonzero
matching products imply the support height is zero: the four rotated
products have common real part and obey the multiplicative rectangle
identity. The two single-swap differences do not vanish, so the real
and imaginary parts of that identity force zero height.

At label 3 ($1342$), the disjoint slot swaps $(2\,3)$ and $(1\,4)$
give labels 5 and 9, and doing both gives label 11. At zero height,
the nonzero rotated products at 3, 5 and 9 are purely imaginary.
The rectangle identity makes the rotated product at 11 purely
imaginary too. Thus 11 is active. These implications are checked in
[ZhengT34Contact.lean](MOC/ZhengT34Contact.lean).

At the assignment $2431$ (label 11), each of the seven ordinary
profiles in the displayed chart evaluates to zero, whereas $f_{70}$
evaluates to one by the profile formula in Zheng §4.1. Thus contact
11 implies $d=0$. In this chart the other terms evaluate to squared
minors by the [Merikoski–Virtanen formula](https://doi.org/10.1016/0024-3795(89)90709-X).
This proves the supported gap is nonnegative in the zero-height
branch and in the branch with additional label 13. The usual
repeated-eigenvalue and vanishing-pair-sum cases already deal with
the excluded nonsimple or zero-product spectra.

## Exact radial threshold on the wall $b=0$

For a positive mixed coefficient, scale $d=1$. Retain
$t34HeightLift$ from [FourContactCertificate.lean](MOC/FourContactCertificate.lean).
Let $C_0=t34RadialC$ and $Q=t34RadialQ$ at $b=0,d=1$. For an actual
projected profile, $C_0+hQ=0$ and $Q\ne0$; the latter implication is
checked in FourContactCertificate. The exact Hessian determinant
calculation on the cubic gives
\[
 Q^2\det\operatorname{Hess}C
 =-4(p+r+1)^4(cs+c+q+s+1)^2 F(a)^2.
\]
Here $U=q+s+1$, $V=s+1$, and the grouped polynomial is
\[
 D=(p+1)(q+1)U+cV[p(q+1)+1],\qquad
 F(a)=cUa^2+[D-cq(q+s)]a+D+cq(qs+s+1).
\]
To reproduce the factorization, take the Hessian of the cubic
formula in FourContactCertificate before inserting $t34HeightLift$.
Use successive zero-based Schur pivots $(1,13,-1)$, $(3,11,1)$,
$(9,4,1)$ and $(10,1,-1)$, with each triple giving current row,
column, and pivot value. The signed product of the pivots is one.
Expand the ten-by-ten determinant by height to degree three, then
insert $h=-C_0/Q$ and clear a factor $Q^3$; the polynomial on the
right is $-4Q(p+r+1)^4(cs+c+q+s+1)^2F(a)^2$. This is a symbolic
factorization, without specialization to any numerical spectrum
or mixer.

Thus singularity of the Hessian forces $F(a)=0$. The elementary kernel
vector behind this step is checked in
[FourMatchingHessianKernel.lean](MOC/FourMatchingHessianKernel.lean);
for a nonreal profile it is the imaginary part, and for a real profile
it follows by homogeneity of the vanishing gradient. This suffices
without the stronger rank theorem of
[Howard–Millson–Snowden–Vakil](https://doi.org/10.1112/plms/pds016).
A nonnegative root
requires $c,q>0$; otherwise all terms are nonnegative and the constant
term is positive. Set $A=1/c+1/q$ and
$D_0=(q+1)U+cV$. For the Bernstein comparison on $0\le a\le A$,
the constant control is positive. The middle control is nonnegative
because
\[
cq(q+s)A=c(q+s)+q(q+s),\quad D\ge D_0,\quad
(q+1)U-q(q+s)\ge0,\quad V+2q(qs+s+1)-(q+s)\ge0.
\]
The endpoint admits the identity
\[
cq^2 F(A)=cq^2(D-D_0)(A+1)
+c^2(q+1)^2\bigl[s((q-\tfrac12)^2+\tfrac34)+1\bigr]
+3cq(q+1)U+q^2(q+2)U.
\]
Therefore $a\ge1/c+1/q$ by the analytic Bernstein argument.
The scalar threshold from $F(a)=0$ is checked in ZhengT34Contact.
The Hessian factorization above is on paper. A proof that this
threshold implies the required minor comparison, and the analysis
of the other positive-mixed walls, are not supplied by this note.

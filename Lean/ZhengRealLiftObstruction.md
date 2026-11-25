# Real spectral lifts and the limits of the Hessian relaxation

Status: exact algebraic obstruction and exact relaxed stationary example.
Neither is a counterexample to the order-four Marcus–de Oliveira
conjecture, and neither settles Zheng's Group V.

## The real-lift equations

Use the fourteen bracket coordinates of [Zheng's preprint, Appendix A
(DOI 10.13140/RG.2.2.36790.25923)](https://doi.org/10.13140/RG.2.2.36790.25923).
Write \(B(z)\) for the coordinate vector (each entry is a product of
four differences), \(C\) for the matching cubic, \(G=\nabla C\), and \(H\)
for its Hessian. The basis and the gradient are written out in
[FourMatchingPolarization.lean](MOC/FourMatchingPolarization.lean).
For the underlying eight-point invariant variety and its cubic, see
[Howard–Millson–Snowden–Vakil, Theorem 3.4 (DOI 10.1112/plms/pds016)](https://doi.org/10.1112/plms/pds016)
([open version, DOI 10.48550/arXiv.1103.5255](https://doi.org/10.48550/arXiv.1103.5255)).

For a spectral profile \(u+iv=\eta B(z)\), the quadratic gradient
vanishes. Expanding it into real and imaginary parts gives
\[
G(v)=G(u),\qquad H(u)v=0.
\tag{1}
\]
Conversely (1) is exactly \(G(u+iv)=0\). Identifying this complex
gradient-zero cone with the affine complex spectral cone uses
Zheng's equation (3.1) and Appendix A; the necessary direction used
below only requires the bracket gradient identity checked in Lean.
This distinction matters: solving the two scalar equations
\(C(u)=\det H(u)=0\) is not a real-lift test.

For fixed \(u\), let \(K=\ker H(u)\). Polarizing the quadratic \(G|_K\)
defines a linear map \(L:\operatorname{Sym}^2 K\to\mathbb R^{14}\)
with \(L(vv^{\mathsf T})=G(v)\). Thus (1) is equivalent to the
intersection of \(L(S)=G(u)\) with positive semidefinite matrices of
rank at most one. In particular, a linear functional \(\ell\) for which
\(\ell(G(v))\le 0\) on \(K\) and \(\ell(G(u))>0\) excludes all real lifts.
[FourMatchingHessianKernel.lean](MOC/FourMatchingHessianKernel.lean)
checks the existence of a nonzero Hessian kernel vector on all actual
real bracket projections. It does not assert that the kernel condition
alone is sufficient.

## A seven-contact obstruction with an exact sign certificate

Set
\[
x=B(0,0,1,1,2,2,3,3),\qquad
y=B(0,1,2,3,3,0,1,2),\qquad u=x-y.
\]
In the zero-based coordinate order of
[FourMatchingPolarization.lean](MOC/FourMatchingPolarization.lean),
\[
u=(3,1,0,0,0,9,4,0,0,3,-12,-4,0,9).
\]
The gradients at \(x,y\) vanish. Since \(G\) is quadratic, its mixed
polarization gives \(H(x-y)(x+y)=0\), with \(x+y\ne 0\).
The cubic polarization similarly gives \(C(x-y)=0\): in the expansion
of \(C(sx+ty)\), the coefficients of all four terms vanish by
\(G(x)=G(y)=0\) and Euler's identity.

Put \(E_j=(H(u)v)_j\). Differentiating the displayed coordinate
gradient in the cited Lean source gives the following linear identities:
\[
\begin{aligned}
E_6&=9v_0+3v_{13},\\
36(v_2-v_{12})&=-E_1+18E_2+3E_3-12E_4-9E_5-6E_6\\
&\hspace{1em}+9E_7-12E_8-18E_9+12E_{10}+10E_{11}.
\end{aligned}
\]
They imply that on \(K\), \(v_0=-v_{13}/3\) and \(v_2=v_{12}\).
The sixth gradient coordinate separates:
\[
G_6(v)=v_0v_{13}-v_2v_{12}=-v_{13}^2/3-v_{12}^2\le0,
qquad G_6(u)=27.
\]
This excludes (1) even though both scalar equations hold. These two
linear identities for the witness are exact algebra, not a Lean claim.

To display seven lower-support contacts, use labels \((0,1,4,5)\) for
the rows and \((2,3,6,7)\) for the columns. For a matching, multiply
the four differences oriented from row to column. Relabeling the
points acts invertibly and over \(\mathbb R\) on the bracket coordinates
by the bracket relations, so it preserves the lift obstruction. In
\(x\), the row points are \((0,0,2,2)\) and the column points are
\((1,1,3,3)\). The possible products are \(1,-3,9\), with minimum
\(-3\) when the first two rows get a mixed pair of columns.
In \(y\), the row points are \((0,1,3,0)\) and the column points are
\((2,3,1,2)\). All matching products are nonpositive, and the product
is zero precisely if row label \(1\) gets column label \(6\) or row
label \(4\) gets column label \(3\). Each condition holds for four of
the mixed assignments, and their intersection has one assignment.
Consequently \(x-y\) has minimum \(-3\) at exactly seven matchings.

This example does **not** violate the determinant support inequality:
each real spectral component obeys [Fiedler’s Hermitian bound
(DOI 10.1090/S0002-9939-1971-0286814-1)](https://doi.org/10.1090/S0002-9939-1971-0286814-1),
formalized in [Hermitian.lean](MOC/Hermitian.lean), giving
\(D_x\ge-3\) and \(D_y\le0\), hence \(D_x-D_y\ge-3\).
It shows that seven contacts do not restore the spectral information
lost by replacing (1) with the scalar cubic and Hessian equations.

## Independent obstruction to using contacts and stationarity alone

The mixed facet on the canonical order-four minor coordinates in
[MixedBound.lean](MOC/MixedBound.lean) vanishes on 13 permutation
profiles and is nonnegative at every permutation. It can nevertheless
have a strictly negative minimum on real orthogonal mixers. This is
an exact obstruction in the real-linear minor-functional relaxation.

For the zero count, write its permutation value as
\(1_A+1_B+1_C-1_D\), where \(A\) is \(\sigma(1)=2\), \(B\) is
\(\sigma(2)=1\), \(C\) is \(\sigma(\{2,3\})=\{2,3\}\), and \(D\) is
\(\sigma(\{1,3\})=\{0,2\}\). The sets \(A,B\) have size six and intersect
in two assignments; \(C\) has size four and is disjoint from both.
Also \(D\) has size four and is contained in \(A\cup B\cup C\).
Exactly one member of \(D\) satisfies both \(A\) and \(B\).
Thus subtracting \(1_D\) turns three of the fourteen positive
assignments into zeros and creates no negative values.

Use real unit quaternion coordinates \(q,r\). Choose \(0<t<1\),
\(b=t/\sqrt{1+t^2}\), \(q_3=r_0=r_3=0\), \(r_1=r_2=1/\sqrt{2}\),
and
\[
q_0^2=t,quad q_1^2=(1-t)(1-b)/2,quad q_2^2=(1-t)(1+b)/2,
qquad q_1<0<q_2.
\]
By the quaternion coordinate identities of
[MixedBound.lean](MOC/MixedBound.lean), the sum of the two squared
entries contributing to the facet is
\[
2(q_1r_2+q_2r_1)^2=(1-t)(1-\sqrt{1-b^2}).
\]
The two signed minor squares contribute \(-t(1-t)b\), since their
unsquared values are \(t/2-(1-t)b/2\) and \(-t/2-(1-t)b/2\),
respectively. The resulting facet value is
\[
(1-t)(1-\sqrt{1-b^2}-tb)
  =(1-t)(1-\sqrt{1+t^2})<0.
\]
A minimum exists on the compact orthogonal group and is stationary.
Thus stationarity and many contacts do not prove the desired bound for
arbitrary real-linear minor objectives. This is a statement about
the relaxation, not about the existence of a spectral profile for
this facet.

## Remaining stationary-pivot target

Seven-contact transfer and stationary pivot reduction can be applied
in sequence: transfer a hypothetical strict violation to new spectra
with at least seven contacts, and then maximize over the mixer for
those new spectra. Contacts are unchanged because they depend on the
spectra and support direction, not the mixer. The open step is to
exclude a strict support violation in the dense bad-pivot chamber
while retaining the exact real-lift constraint (1), or using a
different condition that supplies the same missing spectral
information. The two examples above concern different relaxations;
neither solves this open step.

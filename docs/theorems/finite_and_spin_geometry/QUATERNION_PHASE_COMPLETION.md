# Quaternion geometry of phase completion

## The exact identity

Let \(q,r\in\mathbb R^4\) be unit quaternions. Use the standard left and
right multiplication matrices

\[
L(q)=\begin{pmatrix}
q_0&-q_1&-q_2&-q_3\\
q_1&q_0&-q_3&q_2\\
q_2&q_3&q_0&-q_1\\
q_3&-q_2&q_1&q_0
\end{pmatrix},\qquad
R(r)=\begin{pmatrix}
r_0&-r_1&-r_2&-r_3\\
r_1&r_0&r_3&-r_2\\
r_2&-r_3&r_0&r_1\\
r_3&r_2&-r_1&r_0
\end{pmatrix}.
\]

Every \(O\in SO(4)\) has a representation \(O=L(q)R(r)\). In the
phase-completion chart (see `categorical_global_completion_criterion.md`), put

\[
a=-O_{43},\quad b=-\det O[23,24],\quad
c=-\det O[13,14],\quad d=O_{34}.
\]

The complementary-minor identity identifies \(a\) with the needed
three-by-three minor, since \(\det O=1\). The chart discriminant is

\[
\Delta=4(ab-cd)^2-(a^2+b^2-c^2-d^2)^2.
\]

Then

\[
\boxed{\Delta=-16\prod_{i=0}^3(q_i^2-r_i^2).}
\tag{1}
\]

This is an exact identity on \(S^3\times S^3\), not a numerical fit.

## Proof

Direct quaternion multiplication and the two-minor formulas give

\[
\begin{aligned}
a+d&=2(q_0r_1-q_1r_0),&
a-d&=2(q_2r_3+q_3r_2),\\
b+c&=2(q_0q_1-r_0r_1),&
b-c&=2(q_2q_3+r_2r_3).
\end{aligned}
\]

For example, before imposing unit norms, the polynomial identity for \(b\)
is

\[
-\det O[23,24]
=(q_0q_1+q_2q_3)\|r\|^2
 +(-r_0r_1+r_2r_3)\|q\|^2.
\]

Thus the four factors in the real discriminant factorization become

\[
\begin{aligned}
a+b+c+d&=2(q_0-r_0)(q_1+r_1),\\
a+b-c-d&=2(q_2+r_2)(q_3+r_3),\\
a-b+c-d&=-2(q_2-r_2)(q_3-r_3),\\
a-b-c+d&=-2(q_0+r_0)(q_1-r_1).
\end{aligned}
\]

Their product is \(16\prod_i(q_i^2-r_i^2)\), and its negative is \(\Delta\).

The accompanying code/theorems/finite_and_spin_geometry/root_quaternion_completion_exact.py verifies the quaternion
matrix and minor identities as integer polynomial identities in eight
independent variables, with the unit-norm substitutions kept explicit. It
also expands and verifies (1) without an external symbolic algebra package.

## Geometric interpretation

The vectors \(p=(q_i^2)_i\) and \(s=(r_i^2)_i\) are probability vectors.
Away from equal coordinates, their difference has zero sum. Therefore
\(\Delta>0\) means that one coordinate has one sign and the other three
have the opposite sign. The condition \(\Delta<0\) means that the signs
split two against two. Equality is the boundary where one squared
coordinate agrees.

For a generic completion chart, \(\Delta\geq0\) is exactly the condition
that its bilinear numerator has a zero on the two-dimensional unit torus.
The passage from a torus zero to rank-two diagonal completion, including singular charts, is proved in `categorical_global_completion_criterion.md`.

Independent row and column relabelings change the quaternion coordinates.
One cannot choose arbitrary independent rotations of \(q\) and \(r\):
only transformations corresponding to the permitted monomial operations
are relevant.

## The common-law facet in the same coordinates

The representative facet from COMMON_MINOR_POLYTOPE.md becomes

\[
\begin{aligned}
f(q,r)={}&(q_0r_0+q_1r_1-q_2r_2+q_3r_3)^2\\
&+(-q_0r_2-q_1r_3+q_2r_0-q_3r_1)^2\\
&+(-q_0q_3+q_1q_2+r_0r_3+r_1r_2)^2\\
&-(-q_0q_1+q_2q_3-r_0r_1-r_2r_3)^2.
\end{aligned}
\tag{2}
\]

The same integer polynomial program verifies all ingredients of (2).
It is a difference of one square from a sum of three squares. This makes
the proposed structural implication explicit:

\[
f(q,r)<0
\quad\Longrightarrow\quad
\text{some permitted monomial chart has }
\prod_i((q'_i)^2-(r'_i)^2)\leq0.
\tag{3}
\]

Equation (3) remains **unproved**. Neither its appearance as a Lorentz-type
quadratic expression nor the many numerical instances proves it. If it
holds with the required completion hypotheses, it establishes the
common-law-or-rank-two structural disjunction. A separate scalar
rank-two MOC theorem would still be needed to finish that route.


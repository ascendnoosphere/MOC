# Direct attack 026: sharp uniform spectral slices for the isoclinic budget

## Outcome

This investigation directly proves the stronger isoclinic support budget
for two entire genuinely complex spectral families. The proof retains
actual spectra and all support directions, and covers every monomial
translate of the isoclinic curve. The first family has the exact sharp
constant \(180/103\), substantially below the proposed universal constant
four. The second satisfies the convenient bound with constant two.

These fixed second spectra were deliberately taken from the examples
that defeat the finite 130-ray certificate cone and the combined
finite-plus-quadratic certificate cone. Thus the result is not obtained
by assuming those certificate systems capture the support gap.

This does not prove the budget for every second spectrum or for arbitrary
unitaries. It is one additional substantive direct investigation, number
026 in this reviewer's work, following review investigations 001–025.

## 1. The two uniform theorems

Put

\[
J=\begin{pmatrix}
0&-1&-1&-1\\
1&0&-1&1\\
1&1&0&-1\\
1&-1&1&0
\end{pmatrix},\qquad
U(r)=\frac{rI+J}{\sqrt{r^2+3}},\qquad r\in\mathbb R.
\]

Let

\[
a=(0,\tfrac12,1,z),\qquad z\in\mathbb C,
\]

and take any support direction \(\eta\in\mathbb C\). For an ordering
of the second spectrum, define

\[
c_\pi=\operatorname{Re}\left(\eta\prod_i(a_i+b_{\pi(i)})\right),
\quad h=\max_\pi c_\pi,\quad g_\pi=h-c_\pi.
\]

Write \(A=g_{\mathrm{id}}\), let \(T\) be the sum of the six
transposition gaps and \(D\) the sum of the nine derangement gaps, and put

\[
K=-\sum_{\text{three-cycles }\pi}\epsilon_\pi g_\pi,
\qquad
\epsilon_\pi=\prod_{\pi(i)\ne i}J_{i,\pi(i)}.
\]

### Theorem A

For the second spectrum

\[
b=\left(
\frac{-2+i}{3},\frac{-11+3i}{26},
\frac{-14-6i}{29},-\frac23
\right),
\tag{1}
\]

every \(z\), every \(\eta\), and every reordering of \(b\) satisfy

\[
\boxed{K^2\le\frac{180}{103}\,TD.}
\tag{2}
\]

The constant \(180/103\) is sharp for this entire family with all base
permutations included.

### Theorem B

For

\[
b=\left(
\frac{352}{3},
\frac{-19103+16810i}{51493},
\frac{-501033-262235i}{1603673},
\frac{-836163-439684i}{1331525}
\right),
\tag{3}
\]

the same quantifiers give

\[
\boxed{K^2\le2TD.}
\tag{4}
\]

The exact sharp constant obtained in this second family is

\[
\frac{
249627002094205665972028526110483540404731783015316914718252088225
}{
125364249675638625266437068582034185290986505857072473321591198747
}
\approx1.991213625416165<2.
\tag{5}
\]

For either second spectrum, complex MOC consequently holds for every
matrix of the form \(M_1U(r)M_2\), where \(M_1,M_2\) are arbitrary
monomial unitaries, and for all \(z\in\mathbb C\). Both support signs
and every support direction are included.

## 2. Eliminate the variable eigenvalue and support direction exactly

For each permutation, define the fixed complex numbers

\[
P_\pi=\prod_{i=1}^{3}(a_i+b_{\pi(i)}),
\qquad Q_\pi=b_{\pi(4)}P_\pi,
\]

where the first three \(a_i\) are \(0,1/2,1\). If \(w=\eta z\), then

\[
c_\pi=\operatorname{Re}(wP_\pi+\eta Q_\pi).
\tag{6}
\]

Thus all actual choices \((z,\eta)\) lie in one real four-dimensional
linear cost family. Conversely, every pair \((w,\eta)\) with
\(\eta\ne0\) comes from the actual finite eigenvalue \(z=w/\eta\).
The remaining pairs are harmless limits; the proof covers the larger
linear family directly.

Let

\[
v_\pi=(\operatorname{Re}P_\pi,-\operatorname{Im}P_\pi,
        \operatorname{Re}Q_\pi,-\operatorname{Im}Q_\pi),
\]

and \(x=(\operatorname{Re}w,\operatorname{Im}w,
\operatorname{Re}\eta,\operatorname{Im}\eta)\), so \(c_\pi=v_\pi\cdot x\).
The lifted support cone is

\[
\mathcal C_b={(x,h)\in\mathbb R^5:
h-v_\pi\cdot x\ge0\text{ for all }\pi\in S_4\}.
\tag{7}
\]

It is a polyhedral cone with 24 defining inequalities. The height is not
inflated in the actual application: the chosen point has
\(h=\max_\pi v_\pi\cdot x\).

For fixed \(C>0\), the desired budget is equivalent to

\[
\mathcal H_C(x,h)=
\begin{pmatrix} CT&K\\K&D\end{pmatrix}\succeq0.
\tag{8}
\]

Crucially, this matrix is linear in the five lifted coordinates. Its
positive-semidefinite locus is a convex cone. Therefore it is enough to
prove (8) on every extreme ray of \(\mathcal C_b\). This finite
verification is a complete proof for the whole infinite spectral family,
not sampling of eigenvalues or support directions.

## 3. Exhaustive exact extreme-ray construction

For both spectra, the 24 coefficient points have affine dimension four.
The verifier supplies an exact nonzero five-by-five determinant witnessing
this fact. Consequently \(\mathcal C_b\) is pointed. It is also full
dimensional, since \((0,1)\) satisfies every defining inequality strictly.

Every extreme ray of a full-dimensional pointed cone in dimension five
has at least four linearly independent active defining inequalities.
The verifier enumerates all

\[
\binom{24}{4}=10626
\]

quadruples. It clears a common denominator in the coefficient points,
computes each possible one-dimensional nullspace by exact integer
cofactors, and tests both orientations against all 24 inequalities.
Proportional feasible rays are normalized by their integer gcd and merged.
No floating-point convex-hull routine is used in this enumeration.

The resulting numbers of distinct extreme rays are:

| Second spectrum | Exact extreme rays |
|---|---:|
| (1), from the finite-cone obstruction | 37 |
| (3), from the combined-cone obstruction | 78 |

This enumeration is complete by the active-constraint argument. Every
point in \(\mathcal C_b\) is a nonnegative combination of these rays.

At each ray, and for each of the 24 reorderings of \(b\), the verifier
computes the exact integers \(T,D,K\). They have \(T,D\ge0\). If
\(TD=0\), it checks \(K=0\). Otherwise it computes \(K^2/(TD)\).
The largest ratio over all rays and all reorderings is exactly the
constant in (2) or (5), respectively.

For those constants, every ray matrix in (8) is positive semidefinite.
Linearity of (8) and conic decomposition prove it everywhere on
\(\mathcal C_b\), establishing Theorems A and B.

## 4. A finite exact equality model

For (1), take

\[
z=\frac{32-6i}{53},\qquad \eta=-417-161i,
\]

and exchange the second and fourth entries of \(b\). Direct product
evaluation gives

\[
h=5,\qquad A=10,\qquad T=40,\qquad D=\frac{206}{9},\qquad K=40.
\]

Hence

\[
\frac{K^2}{TD}
=\frac{1600}{40(206/9)}=\frac{180}{103}.
\]

This is an actual finite complex spectral instance, not a limiting ray
with \(\eta=0\). It proves that the uniform coefficient in Theorem A
cannot be decreased.

## 5. From the height matrix to the unitary curve

The independently established exact Leibniz identity for the isoclinic
curve is

\[
h-\operatorname{Re}\left(\eta\det(D_a+U(r)D_bU(r)^*)\right)
=\frac{Ar^4+Tr^2-Kr+D}{(r^2+3)^2}.
\tag{9}
\]

Theorems A and B both imply \(K^2\le4TD\). If \(T>0\), then

\[
Tr^2-Kr+D
=T\left(r-\frac{K}{2T}\right)^2+
D-\frac{K^2}{4T}\ge0.
\]

If \(T=0\), the budget gives \(K=0\), and the same conclusion follows
from \(D\ge0\). Since \(A\ge0\), (9) is nonnegative for every real
\(r\). This proves every scalar support inequality for this family,
hence its complex convex-hull inclusion.

Reordering \(b\) corresponds to right multiplication by a permutation
matrix. Left multiplication introduces a conjugation of the relative
permutation classes. The identity, transposition, and derangement classes
are unchanged. Even conjugation preserves the two oriented three-cycle
classes; odd conjugation swaps them, replacing \(K\) by \(-K\).
The verifier checks this class-sign identity explicitly. The budget uses
\(K^2\), and both signs of \(r\) are included, so arbitrary left and
right permutation translates are covered. Diagonal phases preserve all
squared minors and the determinant support value, giving the stated
monomial-unitary conclusion.

## 6. Scope and unproved extensions

The exact results above rely solely on the complete rational cone
enumerations for the two specified second spectra. They do not establish
a uniform classification of coefficient hulls as \(b\) varies. The
universal isoclinic budget, the positive-gap inequality on every complex
rank-two plane, and unrestricted complex MOC remain open in this work.

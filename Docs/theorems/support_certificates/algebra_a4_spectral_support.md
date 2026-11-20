## 1. The symmetry-fixed cost coordinates

Let \(c_\pi\) be a real cost in the fourteen-dimensional matching-product
cost space. Suppose \(c_{\sigma\pi\sigma^{-1}}=c_\pi\) for every
\(\sigma\in A_4\). The two classes of three-cycles have four elements each.
Fix their signs using

\[
J=\begin{pmatrix}
0&-1&-1&-1\\
1&0&-1&1\\
1&1&0&-1\\
1&-1&1&0
\end{pmatrix},\qquad
U(r)=\frac{rI+J}{\sqrt{r^2+3}}.
\]

For a three-cycle \(\pi\), its sign is
\(\operatorname{sgn}(\pi)\prod_{i:\pi(i)\ne i}J_{i,\pi(i)}\).
These are the conventions used in the [exact geometry verifier](../../../code/theorems/support_certificates/algebra_a4_fixed_geometry.py).
The normalized M8 cubic and its fourteen-coordinate basis are defined in Sections 2–4 of the retained [spectral-moduli companion](../finite_and_spin_geometry/categorical_spectral_moduli_final.md). The six class values necessarily
have the following four-parameter form:

| Class | Value |
|---|---:|
| Identity | \(h_0\) |
| Transpositions | \(h_0+x\) |
| Double transpositions | \(h_0+y\) |
| Four-cycles | \(h_0+x+y/2\) |
| Positive three-cycles | \(h_0+3x/2+k\) |
| Negative three-cycles | \(h_0+3x/2-k\) |

This follows either from the exact three-label and alternating relations,
or by the explicit fourteen-coordinate linear verification in the script.
Subtract \(h_0\), and write

\[
h=\max\{0,x,y,x+y/2,3x/2+|k|\}.
\tag{1}
\]

Thus \(h\) here is the permutation support height **relative to the identity
cost**, rather than the constant coordinate used in the cubic lift.

For the isoclinic curve, the four deficit coefficients are

\[
A=h,\qquad T=6(h-x),\qquad D=9h-6x-6y,
\qquad K=8k.
\tag{2}
\]

The exact determinant expansion gives

\[
\bigl(h-c(U(r))\bigr)(r^2+3)^2
=Ar^4+Tr^2-Kr+D.
\tag{3}
\]

## 2. The nonic splits into three explicit branches

Let \(F\) be the normalized M8 cubic, and use \(t\) for its constant-height
coordinate. On the symmetry-fixed space,

\[
F=tQ+C,
\quad Q=4k^2+\frac34(y-2x)^2,
\quad C=\frac{x}{2}(12k^2+5x^2-3xy).
\tag{4}
\]

Define

\[
R=4k^2+xy-x^2,\qquad L=3y-4x,
\qquad S=4x^2+t(4x-y).
\tag{5}
\]

The action of \(A_4\) decomposes the fourteen-dimensional real coordinate
space into mutually inequivalent isotypic blocks of dimensions \(4,4,6\).
The exact rational basis used in the certificate has determinant \(-1/144\).
Every cross-block Hessian entry vanishes identically. In this basis,

\[
\det H_2=S^2/36,
\qquad \det H_3=-R^3/256,
\tag{6}
\]

and the four-dimensional fixed block satisfies

\[
Q\det H_0\big|_{t=-C/Q}=QR L^2/144.
\tag{7}
\]

The remaining elimination identity is

\[
4x^2Q-C(4x-y)=xLR/2.
\tag{8}
\]

All four displayed identities are polynomial coefficient identities checked
over the rationals. Multiplying the blocks and accounting for the congruence
determinant gives, on \(Q\ne0\),

\[
Q^2\det H_F\big|_{t=-C/Q}
=-\frac{x^2L^4R^6}{256}.
\tag{9}
\]

The previously established global identity is \(N=-4P_9^2\), where \(P_9\)
is the projected secant nonic. Polynomial continuation therefore gives

\[
\boxed{
P_9\big|_{A_4\text{-fixed}}
=\pm\frac1{32}x(3y-4x)^2(4k^2+xy-x^2)^3.
}
\tag{10}
\]

The formula includes \(Q=0\); no real-lift assumption is required at that
singular locus. In particular, a real projected-secant cost with this symmetry
belongs to at least one of the three branches

\[
\boxed{x=0,\qquad y=4x/3,\qquad 4k^2=x(x-y).}
\tag{11}
\]

## 3. A stronger quadratic budget on all three branches

**Theorem.** For every real symmetry-fixed cost satisfying \(P_9=0\), the
quantities in (1)--(2) obey

\[
\boxed{K^2\le\frac{32}{9}TD.}
\tag{12}
\]

Since \(32/9<4\), this implies the sufficient isoclinic bound \(K^2\le4TD\),
and therefore proves (3) is nonnegative for all real \(r\).

**Proof.** Since \(T,D\ge0\), (12) is equivalent to

\[
\boxed{(h-x)(3h-2x-2y)\ge k^2.}
\tag{13}
\]

The factorization (10) reduces the proof to three cases.

### Branch 1: \(x=0\)

Equation (1) gives \(h\ge y\) and \(h\ge|k|\). Consequently

\[
h(3h-2y)\ge h^2\ge k^2.
\]

The factor \(32/9\) in (12) is attained on the algebraic branch at
\(x=0,y=|k|>0\). This is sharp for the stated projected-secant theorem; it
does not assert finite spectral realizability of these equality points.

### Branch 2: \(y=4x/3\)

Let \(s=|k|\). Since \(h\ge3x/2+s\), one has \(s\le h-3x/2\), with a
nonnegative right side. Hence the left side of (13) minus \(k^2\) is at least

\[
2h^2-\frac{14}{3}hx+\frac{29}{12}x^2.
\tag{14}
\]

If \(x\le0\), every term in (14) is nonnegative because \(h\ge0\). If
\(x>0\), the four-cycle value implies \(h\ge5x/3\). Writing
\(h=5x/3+v\), \(v\ge0\), turns (14) into

\[
2v^2+2xv+\frac7{36}x^2\ge0.
\tag{15}
\]

### Branch 3: \(4k^2=x(x-y)\)

The case \(x=0\) is already covered. First suppose \(x>0\), and put
\(s=|k|\). Then \(y=x-4s^2/x\), and the exact maximum in (1) is
\(h=3x/2+s\). Substitution gives the positive identity

\[
(h-x)(3h-2x-2y)-s^2
=\frac{x^2}{4}+2xs+6s^2+\frac{8s^3}{x}\ge0.
\tag{16}
\]

Now suppose \(x=-u<0\), \(u>0\). Then \(y=-u+4s^2/u\). Direct comparison
of the five entries in (1) shows

\[
h=\max\{0,4s^2/u-u\}.
\tag{17}
\]

Indeed, the double-transposition value exceeds the four-cycle value by
\(2s^2/u+u/2>0\), and exceeds \(3x/2+s\) by
\(4s^2/u-s+u/2>0\), whose discriminant is negative.

For \(s\le u/2\), equation (13)'s margin is

\[
4u^2-9s^2\ge\frac74u^2>0.
\tag{18}
\]

For \(s\ge u/2\), the margin is

\[
\frac{16s^4}{u^2}+3s^2>0.
\tag{19}
\]

This completes all branches. \(\square\)

## 4. What this proves for complex MOC

For fixed actual complex spectra and a fixed support direction, if the 24
real permutation products are invariant under simultaneous even conjugation,
then their determinant support obeys MOC on the entire curve \(U(r)\).
The statement holds also for the larger projected secant closure, so no
unproved real-form membership criterion is used in the inequality proof.

This gives a direct application of the spectral nonic beyond the previously
solved nine-derangement maximizing face: the coefficients \(A,D,K\) may all
be nonzero, the identity need not maximize, and the full problematic central
interval \(0<|r|<0.5961\ldots\) is included.

The isoclinic argument alone does not address arbitrary unitary matrices.
That extension for actual costs with the same symmetry is now proved in
algebra_a4_full_support_theorem.md. Neither argument proves the assertion
for the A4 average of an arbitrary actual spectral cost: the average
generally leaves the three branches (11).

## 5. The next exact metric: spectral height above a symmetric average

For an arbitrary actual cost, average over simultaneous \(A_4\) conjugation,
and extract \((x,y,k)\) relative to its unchanged identity value. Let
\(A=\max_\pi c_\pi-c_{\mathrm{id}}\). Then the full permutation maximum is
at least the maximum of the class averages, but the average need not satisfy
the nonic. The universal stronger isoclinic budget reduces exactly to

\[
A\ge A_*(x,y,k):=
\frac{5x+2y+\sqrt{(x-2y)^2+(32/3)k^2}}6.
\tag{20}
\]

Equivalently, the 2-by-2 real matrix

\[
L(x,y,k)=
\begin{pmatrix}
x&\sqrt{8/27}\,k\\
\sqrt{8/27}\,k&2(x+y)/3
\end{pmatrix}
\tag{21}
\]

would have largest eigenvalue at most \(A\). Equations (20)--(21), suggested
independently by the root agent during this batch, are exact reformulations,
not universal inequalities proved here. They isolate the needed coupling:
how much the nonsymmetric spectral component must raise the maximum above
its class averages.

The three-branch theorem proves the stronger coefficient \(1/3\), in place
of \(8/27\), in the off-diagonal square of (21) when the actual cost is
itself symmetry-fixed. General costs need an additional argument.


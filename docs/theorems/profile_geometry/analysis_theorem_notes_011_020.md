## Round 011 — An exact singular-value constraint on the 3-by-3 star of minors

### Attempted principle

Replace separate rowwise Plücker constraints by a collective matrix condition retaining common-unitary origin.

### Exact theorem

Partition a unitary U as

\[
U=\begin{pmatrix}u&r\\c&V\end{pmatrix},
\]

where u is scalar, and form the 3-by-3 matrix X of the minors with row pairs 1i and column pairs 1j:

\[
X=uV-cr.
\]

Then

\[
\boxed{XX^*=|u|^2I+cc^*.}
\]

Proof: \(VV^*=I-cc^*\), \(Vr^*=-\overline u c\), and \(rr^*=1-|u|^2\). Expand \((uV-cr)(uV-cr)^*\); the coefficient of \(cc^*\) is exactly one.

Thus X has singular values

\[
1,\quad |u|,\quad |u|.
\]

When \(u=0\), X is the explicit rank-one matrix \(-cr\). In particular

\[
|\det U[\{1,i\},\{1,j\}]|^2
=|u_{i1}|^2|u_{1j}|^2.
\]

Every anchor position gives an analogous theorem after relabeling.

### Consequence and scope

This gives simultaneous constraints on nine pair probabilities. They retain information that is invisible to separate Plücker triangles. At a zero anchor, their factorization is exact, not an approximation or a chosen phase.

The resulting matrix constraint is not automatically convex in the squared moduli. A universal spectral-support theorem using it remains open.

## Round 012 — The complex-linear/antilinear form of the C=4 target

### Attempted principle

Expose orientation through the complex structure on R6, instead of treating m and h as unrelated scalar arrays.

Write a real orthogonal R on C3 as

\[
z\longmapsto Xz+Y\overline z.
\]

Its 2-by-2 real blocks obey

\[
m_{ij}=2(|X_{ij}|^2+|Y_{ij}|^2),
\qquad
h_{ij}=|X_{ij}|^2-|Y_{ij}|^2.
\]

Consequently, with forbidden positions (12),(23),(31),

\[
L+4D=
4\left[
2\sum_i|X_{ii}|^2-\sum_i|Y_{ii}|^2
+2\sum_{\rm forbidden}(|X_{ij}|^2+|Y_{ij}|^2)
\right].
\]

The global C=4 inequality is precisely the nonnegativity of this expression on the orthogonal Bogoliubov constraints.

### Actual structural work

Orthogonality implies

\[
XX^*+YY^*=I,\qquad XY^T+YX^T=0.
\]

On the dense part of SO6 where X is invertible, \(Z=X^{-1}Y\) is complex skew-symmetric. A 3-by-3 complex skew-symmetric matrix has singular values \((r,r,0)\). From

\[
X(I+ZZ^*)X^*=I
\]

one gets singular values of Y equal to \((s,s,0)\), and those of X equal to \((1,\sqrt{1-s^2},\sqrt{1-s^2})\). Continuity handles singular X.

This odd-dimensional rank defect is orientation-specific: the opposite component of O6 need not have it.

### Status

The target is now an explicit constrained norm inequality for two 3-by-3 complex matrices. Merely discarding their cross-relation \(XY^T+YX^T=0\) is unjustified. I did not prove the full inequality from these constraints.

## Round 013 — C=4 proved on the entire saturated nonnegative-diagonal stratum

### Geometry supplied by the root and used here

Suppose

\[
m_{ii}=1+s_i^2,\qquad h_{ii}=-s_i,\qquad s_i\ge0.
\]

Each diagonal block has singular values 1 and s_i. Independent orientation-preserving block gauges make it diag(-1,s_i). The saturated unit row/column norms then force all off-block first rows and first columns to vanish. Thus

\[
R\simeq(-I_3)\oplus Q,\qquad Q\in O(3),\quad\det Q=-1,
\quad\operatorname{diag}Q=(s_1,s_2,s_3).
\]

Put \(S=s_1+s_2+s_3\) and \(T=\sum s_i^2\). The improper Rodrigues/quaternion representation gives \(0\le S\le1\), and

\[
D=\frac{3-T}{2}
\ \pm\ \frac32\sqrt{(1-S)\prod_i(1+S-2s_i)}.
\]

The unfavorable sign is the minus sign.

### The completed inequality

Since \(L=3+T-6S\), it is enough to prove

\[
9-T-6S\ge
6\sqrt{(1-S)\prod_i(1+S-2s_i)}.
\tag{1}
\]

The left side is at least 2 because \(T\le S^2\) and \(0\le S\le1\).

Let \(p=\sum_{i<j}s_is_j\), \(q=s_1s_2s_3\), and \(A=9-6S-S^2\). Squaring (1) gives the gap

\[
F=A^2-36(1-S^2)^2+
(-108-24S+140S^2)p+4p^2+288(1-S)q.
\]

Schur's inequality supplies

\[
q\ge\max\left(0,\frac{4Sp-S^3}{9}\right).
\]

For \(p\le S^2/4\), the resulting lower bound has derivative in p at most

\[
-108-24S+142S^2.
\]

For \(0\le S\le24/25\), this is negative: the convex quadratic has negative values at both endpoints, with the right endpoint equal to \(-108/625\).

For \(p\ge S^2/4\), the derivative of the other branch is

\[
8p-12(1-S)(S+9)
\le\frac83S^2-12(1-S)(S+9)<0
\]

on the same S interval. The two branches agree at \(p=S^2/4\). Their minimum therefore occurs at \(p=S^2/3\), where the Schur bound gives \(q=S^3/27\).

This reduces to \(s_1=s_2=s_3=s=S/3\), and

\[
F=9(13s^4+44s^3+54s^2-36s+5).
\]

For the quartic g in parentheses,

\[
g(1/4)=29/256,\qquad g'(1/4)=1/16,\qquad
g''(s)=156s^2+264s+108\ge108
\]

for \(s\ge0\). Hence

\[
g(s)\ge54(s-1/4)^2+(s-1/4)/16+29/256
\ge29/256-1/55296>0.
\]

For the remaining range \(S\ge24/25\), AM–GM gives

\[
36(1-S)\prod_i(1+S-2s_i)
\le\frac{36}{25}(4/3)^3=\frac{256}{75}<4,
\]

whereas the squared left side of (1) is at least 4.

Thus L+4D is nonnegative, in fact strictly positive on this stated stratum. The independent reviewer checked both derivative branches and the high-S estimate.

### Scope

This covers unequal s_i throughout the classified saturated stratum. It does not prove that a global optimizer on SO6 must lie there.

## Round 014 — The obstruction forces a nontrivial penalty constant

### Attempted principle

Use the equal-diagonal family to identify what any global penalty proof must pay, and to test candidate constants before constructing certificates.

In the equal-s subfamily,

\[
L=3(1+s^2-6s),
\]

and the smaller cyclic mass is

\[
D=\frac34\left[(1+s)-\sqrt{(1+s)(1-3s)}\right]^2.
\]

At \(s=1/4\),

\[
-L/D=\frac{7(3+\sqrt5)}{10}.
\]

Therefore any universally valid L+CD>=0 must have

\[
C\ge\frac{7(3+\sqrt5)}{10}\approx3.66525.
\]

This is an exact lower bound, using an actual orthogonal matrix of determinant +1, not a relaxed moment point. Root numerical optimization of this family finds a slightly larger ratio near 3.6697926447; no optimality claim rests on that number.

### Outcome

The global constants 2, 3, and smaller proposed penalties are rigorously excluded. C=4 has room to hold, but the saturation reduction is still required for a universal proof.


## Round 018 — Exact one-fiber moment optimization for a determinant martingale

### Attempted principle

The independent reviewer showed that a continuous determinant martingale cannot escape a nonmonomial strict local support maximum. Instead of assuming a global diffusion, formulate exactly what a single two-coordinate randomized step can accomplish.

### Actual reduction

For a two-coordinate unitary fiber, the determinant is

\[
d(n)=\alpha+\beta\cdot n,\qquad n\in S^2.
\]

The off-diagonal energy of C is a constant minus the squared modulus of an affine-linear diagonal difference. On this fiber it can be written

\[
V(n)=v_0-\tfrac12|\gamma\cdot n|^2
\]

after absorbing the unchanged diagonal sum in v_0. Thus preserving the complex determinant in expectation and minimizing expected V depends only on the first and second moments

\[
u=\mathbb E n,\qquad M=\mathbb E nn^T.
\]

These moments have the exact description

\[
\begin{pmatrix}1&u^T\\u&M\end{pmatrix}\succeq0,
\qquad \operatorname{tr}M=1.
\]

To see sufficiency, the compact PSD set with fixed upper-left entry and trace has two affine constraints. Any extreme point of rank at least two has a nonzero supported symmetric perturbation preserving both constraints, and cannot be extreme. Its extreme points therefore have rank one, giving exactly \((1,n)(1,n)^T\) with |n|=1. Every feasible point is a convex combination of these sphere moments.

The extra determinant constraints are simply

\[
\operatorname{Re}\beta\cdot u=
\operatorname{Re}\beta\cdot n_0,\qquad
\operatorname{Im}\beta\cdot u=
\operatorname{Im}\beta\cdot n_0.
\]

Expected V is a linear objective in M. Therefore the best such one-fiber randomized improvement is an exact semidefinite program, with no sampled approximation of the sphere.

### Status

This gives a concrete local test for the martingale route. It does not show that a strict decrease exists at every nonmonomial unitary. Generic determinant values cannot be held fixed pointwise while descending to monomial matrices; the expectation condition is essential. The reviewer's local-maximum obstruction still applies to any globally continuous construction.

## Round 019 — An explicit common-minor law for a zero-diagonal unitary stratum

### Attempted principle

Exploit the exact rank-one star-minor identities from Round 011 at several anchors simultaneously, rather than treating zero entries as a perturbative nuisance.

### Completed theorem

Let U be a 4-by-4 unitary with

\[
u_{11}=u_{22}=u_{33}=u_{44}=0,
\]

and all twelve off-diagonal entries nonzero. Then there exist positive x,y,z with x+y+z=1 such that

\[
|U|^2=
\begin{pmatrix}
0&x&y&z\\
x&0&z&y\\
y&z&0&x\\
z&y&x&0
\end{pmatrix}.
\]

For example, row-1/row-2 and column-3/column-4 orthogonality give respectively

\[
p_{13}p_{23}=p_{14}p_{24},\qquad
p_{13}p_{14}=p_{23}p_{24}.
\]

Positivity permits division, giving p13=p24 and p14=p23. The other row/column pairs and normalization give the entire displayed pattern.

There is a spectrum-independent law reproducing every squared minor:

- weight x² on (12)(34);
- weight y² on (13)(24);
- weight z² on (14)(23);
- weight xy on each of the cycles (1243) and (1342);
- weight xz on each of (1234) and (1432);
- weight yz on each of (1324) and (1423).

The weights sum to \((x+y+z)^2=1\).

For a 2-by-2 minor with identical row and column sets, its value is the relevant x², y², or z² because the diagonal entries vanish. For disjoint row and column sets, the two remaining row restrictions are orthogonal and each has squared norm 1-w; their determinant squared is \((1-w)^2\). For row/column sets meeting in one index, the determinant is a single product because one entry is zero, so its squared modulus is the corresponding xy, xz, or yz. The listed law has exactly these same event probabilities.

Singletons follow directly from the weight list; complementary minors handle order three. Hence the determinant expansion agrees for all complex spectra.

### Scope

MOC follows for all complex spectra on this entire unitary stratum. The proof does not assume that every zero-diagonal unitary is a limit of this stratum: nonsymmetric permutation-support branches exist, so that density claim would be false.

Real skew-symmetric quaternion rotations with nonzero three parameters give an explicit nonempty family within the stratum.

## Round 020 — Honest open MOC regions around the zero-diagonal stratum

### Attempted principle

Turn the preceding exact restricted law into a nonempty open region of unrestricted complex-unitary instances, rather than leaving it only on a lower-dimensional set.

### Completed continuation theorem

Fix a unitary U from Round 019, and spectra a,b. Suppose the nine derangement products used by its law are not all collinear in C.

All nine weights are positive. Therefore the determinant is in the interior of the convex hull of those nine products and hence in the interior of the full spectral permutation hull.

There is an explicit margin. Choose three noncollinear products \(z_\alpha,z_\beta,z_\gamma\), let A_triangle be their Euclidean triangle area, let ell be their longest side, and let w be the smallest of their three law weights. Subtract weight w from those three vertices and retain the residual positive combination. Since the triangle centroid has distance \(2A_{\rm triangle}/(3\ell)\) from its nearest side, the full determinant has a contained disk of radius

\[
\rho=\frac{2wA_{\rm triangle}}{\ell}>0
\]

inside the permutation hull.

For fixed spectra, write \(M_0=\|A\|+\|B\|\). The determinant perturbation bound gives

\[
|\det(A+VBV^*)-\det(A+UBU^*)|
\le 8\|B\|M_0^3\|V-U\|
\]

for dimension four. Therefore every unitary V satisfying

\[
\|V-U\|<
\frac{\rho}{8\|B\|M_0^3}
\]

also satisfies MOC, with the harmless scalar or zero-norm degeneracies handled separately.

Small simultaneous spectral perturbations are also covered by continuity of the finitely many vertices and of the determinant; the displayed formula is the explicit fixed-spectra radius.

### Outcome

This is a genuine open set of complex-unitary MOC instances around each nondegenerate zero-diagonal point. It does not make those open sets dense or cover the remaining support strata. A universal proof still needs a global mechanism.


## Primary geometric input used in this batch

Howard, Millson, Snowden, Vakil, “The geometry of eight points in projective space: Representation theory, Lie theory, dualities,” arXiv:1103.5255:
https://arxiv.org/html/1103.5255v1

The established geometric facts used are: the degree-one invariant space of eight points on P¹ has dimension 14; the skew cubic has M8 as its scheme-theoretic singular locus; the secant variety has projective dimension 11 and degree 21; its gradient image has projective dimension 9; and the intersection of the cubic with its Hessian hypersurface has that secant variety as its reduced support. Relevant locations: §§1.2, 3.1–3.4, Theorem 3.4, Corollaries 3.9 and 3.12, Proposition 3.19.

The deductions below are supplied explicitly. The argument identifying our coordinates with this geometry is part of Round 011.

## Round 011 — Close the coordinate-identification gap

### Obligation

The conormal argument cannot be applied merely because a cubic resembles the HMSV cubic. Prove that the retained 49-term cubic is its scalar multiple under the actual matching coordinates.

### Proof

Represent the eight P¹ points by

\[
(a_i,1)\quad(1\le i\le4),\qquad
(-b_j,1)\quad(1\le j\le4).
\]

The bracket between the ith point and the (4+j)th point equals a_i+b_j. The 24 bipartite matching invariants are therefore exactly

\[
z_\pi=\prod_i(a_i+b_{\pi(i)}).
\]

The fourteen selected permutations are

\[
1234,1243,1324,1342,1423,2134,2143,
2314,2341,2413,3124,3142,3412,4123.
\]

Their polynomial coefficient matrix has a 14×14 minor of determinant −1. Here is the exact minor specification, so this independence check does not require an external certificate. Columns are the fourteen permutations in the displayed order. Write a_I=∏_{i∈I}a_i and b_J=∏_{j∈J}b_j, with empty products equal to 1. In order, select the coefficient rows a_I b_J indexed by

```text
(I,J) =
(∅,1234), (1,123), (1,124), (1,134),
(12,12), (12,13), (12,14), (12,23), (12,24),
(123,1), (123,2), (123,3), (13,12), (13,13).
```

A string denotes its set of one-based indices. The entry in row (I,J) and column π is 1 if π(Iᶜ)=J and 0 otherwise, directly by expansion of z_π=∏_i(a_i+b_{π(i)}). The resulting integer matrix has determinant −1. These are the exact feature rows of the original `algebra_matching_basis_certificate.json`, not a newly chosen witness. Thus these are fourteen independent degree-one invariants, hence a basis of the degree-one invariant space.

Let C be our explicit 49-term cubic. The retained exact polynomial identity ∇C(z(a,b))=0 shows it is singular along M8. Every secant line is contained in C: its restriction is a cubic with double zeros at the two endpoints, so vanishes identically. Hence C contains S=Sec(M8).

Let C_H be the geometric skew cubic. It also contains S. If C and C_H were different, their intersection would have degree 9. But S is irreducible of dimension 11 and degree 21, and would be a component of that proper intersection. This contradicts Bézout. The geometric cubic is irreducible: otherwise intersections of its factors would create a singular locus of dimension at least 11, whereas its singular locus M8 has dimension 5.

Therefore

\[
\boxed{C=\kappa C_H\quad\text{for a nonzero scalar }\kappa.}
\]

### Result

The external geometric theorems apply to the retained cubic in the retained coordinates. No guessed coordinate transformation or skew-symmetry assertion is needed.

## Round 012 — The entire spectral secant cone has Hessian rank at most twelve

### Obligation

Prove that the corank-two phenomenon is structural, rather than an accident of the exact samples.

Let \(\widehat S\subset\mathbb C^{14}\) be the affine spectral secant cone. It is irreducible of dimension 12. Write G=∇C and H=Hess C.

### Proof

The closure of G(\(\widehat S\)) has dimension 10, because the projective polar image has dimension 9 and the gradient is homogeneous.

At a generic smooth point c of \(\widehat S\),

\[
\operatorname{rank}
\left(H(c)|_{T_c\widehat S}\right)\le10.
\]

The tangent space has dimension 12 inside a 14-dimensional ambient space. Extending a basis of it by two vectors can increase the image rank by at most two. Therefore rank H(c)≤12 generically.

All 13×13 Hessian minors are polynomials. They vanish on a dense subset of the irreducible secant cone, hence vanish on the entire cone:

\[
\boxed{\operatorname{rank}H(c)\le12
\quad\text{for every }c\in\widehat S.}
\tag{12.1}
\]

An actual spectral example attaining rank 12 is given in Round 015.

### Result

The rank-twelve stratum is an open part of a globally rank-at-most-twelve variety. This is exactly the hypothesis needed to extend kernel vectors locally and differentiate them.

## Round 013 — Prove the universal rank-L bound

### General conormal lemma

Let V be a reduced affine algebraic variety in a real or complex vector space of dimension m. Suppose C is a homogeneous cubic and rank H(x)≤r throughout V. At a point c with rank H(c)=r, let N span ker H(c), and set

\[
L(T)_j=\tfrac12\operatorname{tr}
\left(N^TH(e_j)NT\right).
\]

Then

\[
\boxed{\operatorname{rank}L\le
\operatorname{codim}T_cV.}
\tag{13.1}
\]

### Proof, including singular points of V

A nonzero r×r Hessian minor remains nonzero in a neighborhood of c. Gaussian elimination therefore supplies local rational sections n(x) of the kernel bundle, taking any prescribed kernel vector n at c. These sections satisfy H(x)n(x)=0 on the localized reduced variety.

Differentiate along an arbitrary Zariski tangent vector v:

\[
H(v)n+H(c)\,D_vn=0.
\]

For another kernel vector n′, left multiplication yields

\[
(n')^TH(v)n=0.
\]

Symmetry of the third derivative identifies this scalar with a pairing of v with the polarized restricted gradient. In particular

\[
\nabla C(n)\cdot v
=\tfrac12n^TH(v)n=0.
\]

All restricted-gradient vectors, and hence their polarization span im L, lie in the conormal space \((T_cV)^\perp\). This proves (13.1). No smoothness assumption on c is needed.

### Application

Take V=\(\widehat S\). It has dimension 12, so every Zariski tangent space has dimension at least 12. At every point with rank H(c)=12,

\[
\boxed{\operatorname{rank}L\le2.}
\tag{13.2}
\]

### Result

This proves the priority conjectural lemma from Round 008 on the full corank-two spectral secant stratum. The independent reviewer checked the conormal argument and its localization at singular points.

## Round 014 — An exact 2×2 PSD test for the real spectral branch

### Claim

Let c be real, lie in the spectral secant cone, and satisfy rank H(c)=12. Let N be any real kernel basis. Then the following are equivalent:

1. \(c=x+\overline x\) for a singular point \(x\) of C.
2. There is a real d satisfying
   \[
   H(c)d=0,\qquad G(d)=G(c).
   \]
3. There is a symmetric \(T\succeq0\) with
   \[
   \boxed{L(T)=G(c).}
   \tag{14.1}
   \]

### Proof

The equivalence of the first two statements is cubic polarization:

\[
G((c+id)/2)
=\tfrac14\{G(c)-G(d)+iH(c)d\}.
\]

The second statement gives T=ttᵀ after writing d=Nt.

Conversely, Round 013 gives rank L≤2. The rank-reduction lemma of Round 008 moves a feasible positive definite T along a nonzero kernel direction of L until it becomes singular and PSD. A rank-at-most-one factorization T=ttᵀ then gives d=Nt.

By Round 011 and the singular-locus theorem, singular points of C are precisely the cone over M8. Thus this does not merely recover a point satisfying an accidental cubic equation: it recovers the spectral invariant variety.

For a regular matching point with all 24 reconstructed coordinates nonzero, the explicit toric construction from Round 002 recovers a rank-two matrix and then finite additive spectra. More generally, the projective invariant description supplies an eight-point configuration; a common projective coordinate change can avoid infinity for all eight points, producing additive spectra up to one common scalar.

### Result

The arbitrary-rank semidefinite relaxation is exact on this stratum. No higher-degree rank-one equation remains.

## Round 015 — The regular PSD branch suffices for the full conjecture by continuity

### Affine costs

For an affine spectral cost g=h e+c, use the identities

\[
C(g)=hQ(g),\qquad Q(g)=Q(c)
\]

when C(c)=0. If Q(g)≠0, reconstruct

\[
h=C(g)/Q(g),\qquad c=g-he.
\tag{15.1}
\]

The reduced support of C=0 and det H=0 is the secant cone. Therefore, if the resulting c has Hessian rank 12, its real spectral membership is exactly the PSD test (14.1). For a full 24-coordinate cost one must also check the ten linear matching relations; the fourteen chosen coordinates then determine the others.

### Density is certified

Take

\[
a=(0,1,i,2),\quad b=(1,2i,3,1+i),\quad\eta=1.
\]

The selected real spectral coordinates are

\[
c=(-4,-15,-12,-8,-15,-24,-40,
-32,-48,-30,-18,-12,-12,-30).
\]

Exact rational elimination gives

\[
Q(c)=20,\qquad \operatorname{rank}H(c)=12.
\]

Hence Q and a suitable 12×12 minor are nonzero real polynomials of the actual spectral parameters. Their simultaneous nonvanishing is dense. Every strict MOC violation, if one existed, would persist under sufficiently small spectral perturbations and would therefore yield a violation in this regular sector.

### Result and limit

To prove all MOC in dimension four, it is enough to prove the support inequality for the regular PSD-characterized costs. Corank-four and Q=0 cases need not be separately solved if the regular support inequality is proved uniformly and continuity is then applied.

This is a reduction of the full conjecture, not its proof.

## Round 016 — Solve the PSD branch with a scalar quadratic

### Obligation

Make the 2×2 PSD test explicit enough to substitute into a proof or spectral recovery.

Assume rank L=2. First solve the linear system L(T)=G(c). If consistent, its solution set is a line

\[
T=T_0+sZ,\qquad 0\ne Z\in\ker L.
\]

A real symmetric 2×2 matrix is PSD exactly when its trace and determinant are nonnegative. Therefore feasibility is equivalent to

\[
\operatorname{tr}T_0+s\operatorname{tr}Z\ge0,
\]
\[
\det T_0+s\,\operatorname{tr}(\operatorname{adj}T_0\,Z)
+s^2\det Z\ge0.
\tag{16.1}
\]

These are one linear and one quadratic inequality in one real parameter. Their intervals can be compared exactly using rational arithmetic and square roots.

When feasible, a PSD boundary point exists. It has determinant zero and gives T=ttᵀ explicitly. Then d=Nt and x=(c+id)/2 recover the conjugate spectral point.

### Dual form

A necessary dual condition is

\[
\alpha\cdot G(c)\ge0
\quad\text{whenever}\quad
L^*(\alpha)=\sum_j\alpha_jA_j\succeq0.
\]

The nontrivial dual space has dimension at most two. Its boundary is again determined by a quadratic determinant pencil. Dual inequalities alone can miss a nonclosed image of the PSD cone: for example, T maps to (T11,T12) with image {(a,b):a>0} together with {(0,0)}, whose closure is larger. The primal scalar interval test (16.1) remains exact, including this degenerate case.

### Result

On the regular stratum, the reality obstruction has reduced to an interval problem involving a conic. This is an exact branch test; a numerical PSD solver is unnecessary.

## Round 017 — The polar fiber is curved, and its second fundamental form is explicit

### Proposed mechanism

Try optimizing an MOC support functional along a fixed-gradient fiber G(x)=q. Its generic real dimension is two. The tangent space at a regular point is ker H(c).

### Derivation

Let a curve x(t) in a smooth fiber satisfy x(0)=c and x′(0)=n=Nt. Differentiating twice gives

\[
H(c)n=0,\qquad
H(c)x''(0)=-2G(n).
\tag{17.1}
\]

Choose a right inverse \(H(c)^\dagger\) on its image. A local fiber parametrization begins

\[
x=c+Nt-H(c)^\dagger G(Nt)+O(\|t\|^3).
\tag{17.2}
\]

The quadratic term is generally nonzero. Thus span(c,ker H(c)) is a tangent projective plane, not a flat fiber.

For a linear functional ℓ stationary on the fiber, meaning ℓN=0, the kernel ambiguity in x″ disappears. Its Hessian is

\[
\boxed{
D^2(\ell|_{\text{fiber}})[t,t]
=-2t^T L^*(H(c)^\dagger\ell)\,t.
}
\tag{17.3}
\]

### Result and qualification

This is an exact 2×2 curvature formula at smooth regular fiber points. It uses the same spectral PSD pencil but tests a support functional through actual curvature.

The polar fiber need not be compact, and the formula alone does not supply a global extremum or a rounding path.


## Round 020 — A concrete coupled spectral–unitary positivity cone

### Proposed mechanism

Use the newly proved spectral 2×2 PSD condition together with genuine unitary Gram matrices. Neither geometry alone is sufficient, but their tensor product preserves both.

Let

\[
T=\begin{pmatrix}a&b\\b&c\end{pmatrix}\succeq0
\]

be the spectral recovery matrix, and let a genuine unitary Gram block be

\[
G_U=\begin{pmatrix}r&z\\\overline z&s\end{pmatrix}\succeq0.
\]

Then

\[
\boxed{ar+cs-2b\,\operatorname{Re}z\ge0.}
\tag{20.1}
\]

Indeed diag(1,−1)Tdiag(1,−1) is PSD, and (20.1) is its trace pairing with G_U. Equivalently, for a>0 and G_U the Gram matrix of v,w,

\[
ar+cs-2b\operatorname{Re}z
=
\|\sqrt a\,v-(b/\sqrt a)w\|^2
+(c-b^2/a)\|w\|^2.
\tag{20.2}
\]

Boundary cases follow by continuity.

More generally T⊗G_U is PSD, providing coupled positive terms unavailable to a cone that uses only scalar spectral inequalities or only linear unitary moment inequalities.

### Direct proof template

A sufficient certificate for the actual MOC support deficit is an identity

\[
F_U(g)=
\sum_\pi\alpha_\pi g_\pi
+\sum_k\operatorname{tr}
\bigl(W_k(T\otimes G_{U,k})\bigr),
\tag{20.3}
\]


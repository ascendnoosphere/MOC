## 1. Exact spin lifts of the 24 column charts

Let \(e_0,e_1,e_2,e_3\) be the quaternion basis and use \(L,R\) from
QUATERNION_PHASE_COMPLETION.md. The sixteen matrices
\(L(e_i)R(e_j)\) are orthogonal for the Frobenius inner product, with
squared norm four. For an oriented signed permutation \(W\), the associate
matrix

\[
C_{ij}=\tfrac14\operatorname{tr}((L(e_i)R(e_j))^TW)
\]

has rank one: \(C=ab^T\) when \(W=L(a)R(b)\). Factoring this exact
integer-quarter matrix gives the lifts without choosing floating-point
quaternion angles.

For the orientation-corrected column permutations \(W_\pi\), the lifts
may be written

\[
W_\pi=\frac1{n_\pi}L(a_\pi)R(b_\pi),\qquad
\|a_\pi\|^2=\|b_\pi\|^2=n_\pi,
\]

where \(a_\pi,b_\pi\) have integer coordinates. There are four charts
with \(n_\pi=1\), twelve with \(n_\pi=2\), and eight with \(n_\pi=4\).
Since right multiplication reverses the order of right-multiplication
matrices,

\[
OW_\pi=L(q a_\pi/\sqrt{n_\pi})
         R(b_\pi r/\sqrt{n_\pi}).
\]

Thus the real linear coordinate maps are
\(q'=R(a_\pi)q/\sqrt{n_\pi}\) and
\(r'=L(b_\pi)r/\sqrt{n_\pi}\). Every lift is checked by exact integer
matrix multiplication in code/theorems/finite_and_spin_geometry/categorical_fourth_batch_exact.py.

## 2. The 192 hyperplanes lie on a split quadric

Every chart discriminant factors as

\[
\Delta_\pi=-\frac{16}{n_\pi^4}
\prod_{i=0}^3
\bigl((R(a_\pi)q)_i-(L(b_\pi)r)_i\bigr)
\bigl((R(a_\pi)q)_i+(L(b_\pi)r)_i\bigr).
\tag{1}
\]

Primitive integer normalization produces **192 distinct hyperplanes**:
32 normals have support two, 96 have support four, and 64 have support
eight. Each hyperplane occurs in exactly one of the 24 factorizations.
Consequently crossing one generic wall changes exactly one discriminant
sign.

Let \(J=\operatorname{diag}(I_4,-I_4)\). Every normal \(h=(a,b)\)
satisfies \(h^TJh=0\), because its two four-dimensional halves have equal
norm. The physical spin parameters lie on the split quadric
\(g(q,r)=\|q\|^2-\|r\|^2=0\), with a positive normalization imposed
afterward. The restriction of this quadratic form to the hyperplane
\(h\cdot(q,r)=0\) has a one-dimensional radical, spanned by \(Jh\),
and its quotient has signature \((3,3)\). This follows by completing the
null vector \(Jh\) to a hyperbolic pair in signature \((4,4)\).

This identifies the precise real geometry of the phase walls. The
individual four-dimensional directions are the axes, the pair sums
\((e_i\pm e_j)/\sqrt2\), and the half-sum directions
\((\pm e_0\pm e_1\pm e_2\pm e_3)/2\), modulo overall sign. These are
24 directions. The coupled eight-dimensional arrangement is specified by
(1); its exact enumeration, rather than a name for a root system, is what
is used in the proofs.

## 3. Six frames and the Klein-four comparison law

Group the four coordinate directions of \(R(a_\pi)\) up to signs and
row order. Exactly six orthonormal frames occur: the coordinate frame,
three pair-sum frames, and two Hadamard frames. The corresponding frame
for \(r\) is the same in the coordinate and pair-sum cases; the two
Hadamard frames are exchanged.

Within each frame pair, the four charts compare all sixteen pairs of
squared coordinates exactly once, using the four Latin matchings
\(i\mapsto i\mathbin{\mathrm{xor}}j\), up to fixed relabeling.
The chart indices below are zero-based indices in lexicographic order on
\(S_4\), as used in the certificates.

| Frame | Four chart indices |
|---|---|
| Coordinates | 0, 7, 16, 23 |
| Pair sums in the 01/23 split | 1, 6, 17, 22 |
| Pair sums in the 03/12 split | 2, 10, 13, 21 |
| First Hadamard frame / second Hadamard frame | 3, 11, 12, 20 |
| Second Hadamard frame / first Hadamard frame | 4, 8, 15, 19 |
| Pair sums in the 02/13 split | 5, 9, 14, 18 |

Suppose all four discriminants in one group are strictly negative.
For every matching, the four differences of squared coordinates sum to
zero and have positive product. They therefore have exactly two positive
and two negative entries. Summing over the four matchings shows that
exactly eight of the sixteen cross-comparisons satisfy \(q_i^2>r_j^2\).

Assume the eight squared amplitudes are all distinct and sort them in
increasing order, retaining only whether each came from \(q\) or \(r\).
The condition of eight positive cross-comparisons permits exactly the
following eight words. The second column counts the relative label orders
that make **all four** Latin matchings balanced, after the \(q\) labels
are fixed in sorted order.

| Sorted word | Allowed relative \(r\)-orders |
|---|---:|
| qqrrrrqq | 24 |
| qrqrrqrq | 8 |
| qrrqqrrq | 16 |
| qrrqrqqr | 8 |
| rqqrqrrq | 8 |
| rqqrrqqr | 16 |
| rqrqqrqr | 8 |
| rrqqqqrr | 24 |

This is a finite classification of 112 labeled possibilities, checked by
enumerating the 70 four-versus-four words and the 24 relative label orders.
The Latin-matching property is invariant under arbitrary relabeling of
one side after a compensating relabeling of the other, because the
Klein-four subgroup is normal in \(S_4\). Thus fixing the sorted \(q\)
labels loses no cases. Ties lie on arrangement walls and are handled by
the global completion criterion in the separate proof note.


## 5. A sparse facet identity

The Lorentz-type expression supplied by the root track also admits the
following exact rearrangement:

\[
\begin{aligned}
f(q,r)={}&(q_0^2-q_2^2)(q_3^2-q_1^2)
 +(r_0^2-r_2^2)(r_3^2-r_1^2)\\
&+(q_0r_0-q_2r_2)^2+(q_0r_2-q_2r_0)^2\\
&+(q_1r_1+q_3r_3)^2+(q_1r_3+q_3r_1)^2.
\end{aligned}
\tag{3}
\]

This is an integer polynomial identity in eight independent variables.
It isolates the only two potentially negative self-terms from four
positive cross terms. It does not by itself establish the sign implication
across all six frames.

## 6. A concrete simplicial no-completion chamber

Let \(y=(q_0,q_1,q_2,q_3,r_0,r_1,r_2,r_3)^T\) and define the eight wall
coordinates \(t=By\), where

\[
B=\begin{pmatrix}
0&-1&1&0&0&-1&1&0\\
-1&1&-1&-1&1&1&-1&-1\\
1&1&1&1&-1&1&1&1\\
1&0&-1&0&-1&0&-1&0\\
0&-1&1&0&1&0&0&1\\
-1&1&-1&-1&1&-1&-1&1\\
-1&-1&-1&1&1&1&1&1\\
-1&0&0&1&0&-1&-1&0
\end{pmatrix}.
\]

This matrix is invertible. The strict cone \(t_i>0\) is a whole chamber
of the 192-hyperplane arrangement and all 24 discriminants are negative
there. The exact proof is short to state and finite to inspect: orient
each of the 192 primitive normals according to this chamber, collecting
them in \(A\); the exact matrix \(AB^{-1}\) is entrywise nonnegative,
and each row has positive sum. The eight rows of \(B\) themselves belong
to \(A\). Hence \(Ay>0\) is equivalent to \(By>0\), and each listed
wall is an actual facet. The certificate stores all 1,536 nonnegative
rational entries of \(AB^{-1}\).

An exact pair of rational unit quaternions strictly inside the cone is
also stored. This verifies that the chamber meets the physical quadric,
not just the surrounding eight-dimensional space.

The inverse matrix has first column \((-7,-3,2,-5,-8,3,-1,3)^T\), and all
its columns are explicitly retained in the certificate. With \(y=B^{-1}t\),
the representative facet is a homogeneous quartic with all 330 possible
monomials present and positive. More sharply,

\[
f(B^{-1}t)-\tfrac14(t_0+\cdots+t_7)^4
\]

has nonnegative coefficients. On the physical normalization
\(\|q\|=\|r\|=1\), the largest squared norm of a column of the first
four rows of \(B^{-1}\) is 87. The triangle inequality therefore gives
\(\sum_i t_i\ge1/\sqrt{87}\), so

\[
\boxed{f(R(O))\ge\frac1{30276}}
\tag{4}
\]

throughout this closed physical cone. Equation (4) concerns this one
representative facet; its relabelings need separate certificates.

## 7. Forty-six facets are now proved on the whole first cone

For each of the 48 facet orbit representatives, substitute \(y=B^{-1}t\)
into its normalized homogeneous quartic. Forty-four have nonnegative
coefficients. The only four exceptions have the row/column chart indices

\[
[0,6],\quad[0,12],\quad[1,6],\quad[1,12].
\]

Here chart 0 is permutation 1234, chart 1 is 1243, chart 6 is 2134, and
chart 12 is 3124. These labels refer to facet relabelings, not to support
directions or spectra.

The root track has supplied a rational certificate for \([0,12]\):

\[
\frac{f_{0,12}(t)}{1031}
=b(t)^TQb(t)+g(t)h(t)+r(t),
\tag{5}
\]

where \(g(t)=\|q\|^2-\|r\|^2\), \(Q\) is a rational positive definite
26-by-26 matrix, and every coefficient of \(r\) is nonnegative. Its basis
consists of 25 quadratic monomials involving one of \(t_0,\ldots,t_3\),
excluding \(t_2t_4\), together with

\[
w=s+t_2t_4,\qquad
s=t_4t_7-\tfrac12(t_5t_6+t_6^2)+t_7^2.
\]

The certificate is code/theorems/finite_and_spin_geometry/root_spin_chamber_rational_certificate.py.
The categorical exact verifier independently reconstructs the target,
checks the full polynomial identity, proves positivity through 26 strictly
positive exact LDL pivots, and checks every remainder coefficient.

The following exact cone symmetry transfers this certificate to its row
variant. Define

\[
Tt=(t_1,2t_0,2t_3,t_2,t_5,2t_4,2t_7,t_6).
\]

It is induced by a spin transformation whose matrix satisfies
\(A^TA=2I\), and

\[
g(Tt)=2g(t),\qquad
f_{1,j}(t)=\tfrac14 f_{0,j}(Tt),\quad j\in\{6,12\}.
\tag{6}
\]

These are exact polynomial identities. Since \(T\) preserves the
nonnegative orthant, (5) and (6) prove both \([0,12]\) and \([1,12]\).
This gives **46 of 48 facets on the entire first cone**.

The still-unproved pair is \([0,6]\), \([1,6]\); by (6), proving either
one on the whole cone proves both. Root-track numerical Gram approximations
for this pair are not exact certificates. The first-cone common-law theorem
therefore remains incomplete.

## 8. Fixed-coordinate faces and exact two-ray sections

On the face \(t_0=t_1=t_2=t_3=0\), the inverse matrix gives

\[
r=\bar q.
\]

Hence \(O=L(q)R(\bar q)\) fixes the real quaternion coordinate and acts
on the imaginary quaternions by the three-dimensional rotation
\(v\mapsto qv\bar q\). Its kernel has a common permutation law: for a three-by-three unitary,
complementary minors identify every squared two-minor with the corresponding
squared entry. A Birkhoff decomposition of its entrywise squared-modulus
matrix therefore reproduces every exterior level, and extends across the
fixed coordinate. The restrictions of all four exceptional quartics are exactly
\(s^2\), with \(s\) as in Section 7. This explains the forced boundary
kernels in the Gram construction geometrically.

There is also an exact necessity statement for these kernels. The quadratic
form of \(s\) has rank four and determinant \(1/64\), so \(s\) is
irreducible. It has a smooth zero in the positive orthant at
\((t_4,t_5,t_6,t_7)=(1,3,1,1)\), since \(\partial s/\partial t_4=t_7=1\).
Suppose a quartic certificate restricts to

\[
s^2=\sum_k p_k^2+\sum_\alpha c_\alpha t^\alpha,
\qquad c_\alpha\ge0.
\]

At any positive zero of \(s\), each monomial is strictly positive and each
square is nonnegative. Thus every \(c_\alpha\) must vanish and every
\(p_k\) vanishes on the positive zero hypersurface of \(s\). Solving
\(s=0\) for \(t_4\) gives a rational parametrization in the other three
variables on an open positive set. Polynomial division therefore shows
that \(s\) divides each \(p_k\); since both have degree two,
\(p_k\) is a scalar multiple of \(s\). Consequently the ten-dimensional
quadratic-monomial face Gram block has rank exactly one. For a positive
semidefinite full Gram matrix, its nine face-kernel vectors also annihilate
every cross block: a vector with zero quadratic value lies in the kernel
of a positive semidefinite matrix. The reduction from 36 quadratic
monomials to 27 basis elements is therefore necessary for this certificate
class, not merely a numerical pattern.

More generally, the condition that \(O\) sends the quaternion basis
vector \(e_j\) to \(\pm e_i\) is the maximal isotropic linear plane

\[
r=\pm e_j^{-1}\bar q e_i.
\]

It is the spin-coordinate description of an entry of modulus one and a
fixed-coordinate reduction after row/column relabeling.

There is also an exact verification on **every null point of the first
cone with at most two nonzero wall coordinates**. There are six whole
null edges inside the fixed-coordinate face. The other nonnegative finite
root cases reduce to four quadratic roots, with discriminants 20, 41,
or 80 before square-factor simplification. The program evaluates all four
exceptional quartics in exact quadratic fields and proves every value
nonnegative; the other 44 facets already have coefficient proofs. Endpoints
at a single null ray lie in the fixed-coordinate face. Thus every such
two-ray profile has a complete common permutation law. This supplies exact
boundary cases, not an interpolation theorem for the eight-variable cone.

## 9. Finite symmetries and at least three chamber types

The arrangement is invariant under the spin maps induced by every
orientation-corrected row and column permutation. The projective group
generated by signed adjacent row and column swaps has exact order 18,432.
Adding simultaneous quaternion conjugation and exchange of the two
quaternions gives a projective group of order 73,728. These additional
operations correspond to matrix transpose and transpose combined with
signed row/column relabelings, so they preserve both completion and
common-law membership.

Exact group closure is verified with bounded integer matrices, modulo
common positive scaling and the global antipodal sign. The first chamber
has 9,216 antipodal images under the smaller group and 36,864 under the
extended group. A second independently retained chamber has respectively
18,432 and 36,864 images. The two extended orbits are exactly disjoint.
Thus at least 73,728 antipodal no-completion chambers are explicitly
certified. This is a lower bound, not a complete chamber count.

A third chamber was obtained by examining a point outside these two
orbits. It too has exactly eight walls, an exact nonnegative redundancy
certificate, and a rational unit-quaternion witness. The three chambers
have respectively 15, 16, and 17 orthogonal pairs among their eight wall
normals. This number is preserved by every orthogonal spin symmetry, so
the third chamber is inequivalent to both previous ones. Forty-four of
its facets have nonnegative coefficient expansions as well; no full
common-law certificate for this third cone is asserted.

The exact verifier code/theorems/finite_and_spin_geometry/categorical_fourth_batch_exact.py checks the three wall matrices, witnesses, rational redundancy rows, and 144 facet coefficient inventories.

## 10. The remaining global obligation

The separate proof categorical_global_completion_criterion.md establishes
that, for every real \(O\in SO(4)\), including all singular charts,

\[
\exists M\text{ monomial unitary},\ \operatorname{rank}(O-M)\le2
\quad\Longleftrightarrow\quad\max_\pi\Delta_\pi(O)\ge0.
\]

Together with the exact 48-facet classification, the full structural
bridge is precisely the assertion that the common-law facets are
nonnegative on every physical no-completion chamber. The present work
provides explicit chambers, symmetry reductions, and positive polynomial
certificates. A complete
chamber classification or another global argument is still missing.
Even that bridge would leave the scalar rank-two MOC theorem to prove.


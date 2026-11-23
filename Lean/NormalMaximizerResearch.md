# Normal support maximizers and the Frobenius tie-break

Status: mathematical research note; the results below are proved in ordinary
mathematical notation, not checked by Lean. No unrestricted MOC proof is claimed.

Let \(A,B\) be normal complex matrices, \(C(U)=A+UBU^*\),
\(f_\eta(U)=\operatorname{Re}(\eta\det C(U))\), and \(g(U)=\|C(U)\|_F^2\).
Write \(M_\eta=\max_U f_\eta(U)\) and
\(G_\eta=\max\{g(U):f_\eta(U)=M_\eta\}\).
Compactness gives both maxima (NormalOrbit.lean,
exists_support_frobenius_maximizer).

Three distinct statements are relevant:

* (N) Some global support maximizer has normal sum.
* (L) Some maximizer of the pair \((f_\eta,g)\) in lexicographic order has
  normal sum.
* (U) Every such lexicographic maximizer has normal sum.

(L) implies (N). (U) is false, even with simple spectra, nonzero support, and
nonconstant support on the unitary group. (N) in all finite orders is
equivalent to MOC by NormalSupportMaximum.lean,
mocIsTrue_iff_exists_normal_support_maximizer. (L) remains open in general.

## 1. Exact counterexamples to (U)

Take \(A=\operatorname{diag}(1,3)\), \(B=i\operatorname{diag}(1,2)\), and
\(\eta=1\). For any unitary \(U\), put \(UBU^*=iH\), so \(H\) is Hermitian
with eigenvalues 1 and 2. In order two,

\[
\operatorname{Re}\det(A+iH)=\det A-\det H=1,\qquad
g(U)=\operatorname{tr}(A^2+H^2)=15.
\]

Here the determinant equality follows by expanding the two-by-two determinant;
the norm equality follows by cyclicity of trace. Thus every unitary maximizes
both objectives. For

\[
U_0=2^{-1/2}\begin{pmatrix}1&1\\-1&1\end{pmatrix},\qquad
C(U_0)=\begin{pmatrix}1+3i/2&i/2\\i/2&3+3i/2\end{pmatrix},
\]

we have \(\det C(U_0)=1+6i\) and

\[
[C(U_0),C(U_0)^*]=
\begin{pmatrix}0&2i\\-2i&0\end{pmatrix}\ne0.
\]

The following order-three example removes the objection that the support is
constant on the entire orbit. Let \(A=\operatorname{diag}(1,3,0)\),
\(B=\operatorname{diag}(i,2i,1)\), \(\eta=1\), \(D=UBU^*\), and
\(x=|U_{13}|^2,\ y=|U_{23}|^2\), with indices starting at one. Since
\(\det D=-2\), the cofactor expansion gives

\[
\det(A+D)=\det D+\operatorname{adj}(D)_{11}
       +3\operatorname{adj}(D)_{22}+3D_{33}.
\]
\[
\operatorname{Re}D_{jj}=|U_{j3}|^2,\qquad
\operatorname{Re}\operatorname{adj}(D)_{jj}=-2|U_{j3}|^2.
\]

Indeed \(D^{-1}=U\operatorname{diag}(-i,-i/2,1)U^*\).
Consequently, for every unitary,

\[
f_1(U)=1-5x-9y,\qquad g(U)=16+2x+6y.
\]

The global support maximum is 1, attained exactly when \(x=y=0\).
On that set \(g=16\) identically. In particular \(U_0\oplus 1\) is
lexicographically maximal, has determinant \(1+6i\), and has nonnormal sum
(the same nonzero two-by-two commutator). The identity is a normal maximizer.
Both spectra are simple and all cross-sums are nonzero. No statement that
all Frobenius-maximal support sums are normal can hold in this setting.

## 2. Positive result: a common determinant law also represents Frobenius

Work in diagonal coordinates, with \(a=(a_i)\), \(b=(b_j)\).
Use the repository's permutation convention
\(p_\sigma=\prod_j(a_{\sigma(j)}+b_j)\).
Define \(q_\sigma=\sum_j|a_{\sigma(j)}+b_j|^2\).
Unitary invariance and trace expansion give

\[
g(U)=\sum_i|a_i|^2+\sum_j|b_j|^2
 +2\operatorname{Re}\sum_{ij}|U_{ij}|^2a_i\overline{b_j}.
\]

**Proposition.** Fix \(a,U\). Suppose a probability law \(w_\sigma\),
independent of \(b\), represents \(\det C(U)\) for every complex partner \(b\)
(HasCommonWeights in CommonWeights.lean). Then the same law satisfies

\[
(\det C(U),g(U))=\sum_\sigma w_\sigma(p_\sigma,q_\sigma)
\quad\text{for every }b.
\]

Proof: the determinant identity is a polynomial identity in independent
variables \(b_j\). In the basis of \(B\), it reads

\[
\det(U^*\operatorname{diag}(a)U+\operatorname{diag}(b))
=\sum_\sigma w_\sigma\prod_j(a_{\sigma(j)}+b_j).
\]

Compare the coefficient of \(\prod_{k\ne j}b_k\). On the left it is the
\(j\)-th diagonal entry of \(U^*\operatorname{diag}(a)U\), since the other
diagonal variables force the determinant permutation to fix every other
index. Thus

\[
\sum_\sigma w_\sigma a_{\sigma(j)}
=\sum_i |U_{ij}|^2a_i.
\]

Multiply by \(\overline{b_j}\), sum over \(j\), take real parts, and use
\(\sum_\sigma w_\sigma=1\). This gives the norm identity. The result is
symmetric in the two spectral sides, by simultaneous conjugation by \(U^*\).
For the empty index type the assertion holds trivially. QED.

**Corollary.** If every relative unitary has a common law for the fixed
first spectrum (or fixed second spectrum), (L) holds for every partner and
direction. More generally it suffices that the particular lexicographic
maximizer have such a law.

Proof: choose a lexicographic maximizer \(U\). All permutation matrices are
feasible. Thus \(\operatorname{Re}(\eta p_\sigma)\le M_\eta\).
The common law averages these numbers to \(M_\eta\); all its positive
weights must be on permutations with support exactly \(M_\eta\).
On those permutations \(q_\sigma\le G_\eta\), and their weighted mean is
\(G_\eta\). Hence every positively weighted permutation has both maxima.
Its sum is diagonal, and therefore normal. This proof includes singular
maxima and zero support. QED.

This strengthens the conclusion of the common-law route: it proves not only
MOC but existence of a normal Frobenius-maximal support sum. It does not
assert that the original maximizing unitary is normal.

### 2.1 Singleton and subset laws

For an indexed probability law matching all squared-minor marginals,
the singleton marginals are \(|U_{ij}|^2\), so the same conclusion follows
directly (FiniteMinorLaw.lean). More generally, a law with these singleton
marginals that represents the determinant for just the given pair is enough.

In particular, the Birkhoff law in Weights.lean, exists_singleton_weights,
proves (L) whenever the matching product has the expansion

\[
p_\sigma=c+\sum_j h_j(\sigma(j)).
\]

Indeed the signed determinant law has the same singleton marginals, and the
expansion then gives the determinant equality for the nonnegative Birkhoff
law. Its singleton marginals also give the norm equality. This applies to
orders at most three and the one-exception spectral cases, using the exact
expansions already in Weights.lean.

There is also a direct proof for a spectrum with at most two distinct values,
in arbitrary order. Suppose \(b_j=\beta_1\) on a set \(J\) of size \(r\), and
\(b_j=\beta_0\) otherwise. Write \(UBU^*=\beta_0 I+(\beta_1-\beta_0)Q\),
where \(Q=VV^*\) and \(V=U[:,J]\) has orthonormal columns.
For every \(r\)-element row subset \(I\), set

\[
w_I=|\det V[I,:]|^2,\quad
p_I=\prod_{i\in I}(a_i+\beta_1)\prod_{i\notin I}(a_i+\beta_0),\quad
q_I=\sum_{i\in I}|a_i+\beta_1|^2+\sum_{i\notin I}|a_i+\beta_0|^2.
\]

Cauchy–Binet gives \(\sum_I w_I=1\) and
\(\sum_{I\ni i}w_I=Q_{ii}\) (differentiate
\(\det(V^*\operatorname{diag}(t_i)V)=\sum_Iw_I\prod_{i\in I}t_i\)
at \(t_i=1\)). Grouping the signed determinant law by the image of \(J\)
(TwoValues.lean, sum_signedWeight_image_eq_subsetMinorSq) gives
\(\det C(U)=\sum_I w_I p_I\).
Expanding the Frobenius norm using \(Q^2=Q=Q^*\) gives
\(g(U)=\sum_I w_I q_I\). Each \(I\) is realized by a permutation, so the
lexicographic argument above proves (L), also when \(r=0\) or \(r=n\).

## 3. Exact rank-one phase conditions without a normal-sum hypothesis

Absorb the maximizing unitary into \(B\), so the identity maximizes
the pair of objectives. For \(n\ge2\), choose any unit vector \(x\) and
write blocks in the orthogonal decomposition \(\mathbb Cx\oplus x^\perp\):

\[
A=\begin{pmatrix}a&r_A\\s_A&A_1\end{pmatrix},\quad
B=\begin{pmatrix}b&r_B\\s_B&B_1\end{pmatrix},\quad D=A_1+B_1.
\]

Let \(R_z=zxx^*+I-xx^*\), \(|z|=1\).
The row and column of \(B\) change to \(zr_B\) and \(\bar z s_B\).
The bordered determinant identity, valid also when \(D\) is singular, gives

\[
\det(A+R_zBR_z^*)=(a+b)\det D
 -(r_A+zr_B)\operatorname{adj}(D)(s_A+\bar z s_B).
\]

Thus the determinant support on this circle has the form
\(f(z)=f_0+\operatorname{Re}(zL_x)\), where

\[
L_x=-\eta r_B\operatorname{adj}(D)s_A
     -\overline{\eta r_A\operatorname{adj}(D)s_B}.
\]

The Frobenius objective has the form
\(g(z)=g_0+2\operatorname{Re}(zT_x)\), where
\(T_x=r_Br_A^*+s_B^*s_A\). Here \(f_0,g_0\) are constants independent of \(z\).

Since \(z=1\) is a global support maximum,

\[
L_x\in[0,\infty)\quad\text{for every unit }x.
\]

If \(L_x=0\), the entire phase circle is a primary tie. A lexicographic
maximizer must then satisfy \(T_x\in[0,\infty)\). Conversely, if \(L_x>0\),
no other point on this circle is a primary tie. The implication
\(L_x=0\Rightarrow T_x\in[0,\infty)\) is exact; one cannot assert
\(T_x\in[0,\infty)\) unconditionally.

There is a further useful constraint when \(x\) is a right eigenvector of
\(C=A+B\). Then \(s_A=-s_B\). Normality of the individual summands gives
\(\|r_A\|=\|s_A\|=\|s_B\|=\|r_B\|\). Hence

\[
\operatorname{Re}T_x=-\tfrac12\|r_A-r_B\|^2.
\]

At a lexicographic maximizer, a flat primary phase at such a vector forces
\(r_A=r_B\) and \(T_x=0\). If the two rows differ, the primary phase must
instead have \(L_x>0\). The adjoint argument gives the analogous constraint
for left eigenvectors. For a reducing eigenvector of \(C\), \(r_A=-r_B\)
as well; flatness then forces both rows and columns to vanish. This is
consistent with the phase argument already implemented in PhaseMove.lean
and Jacobi.lean for normal sums. For a nonnormal sum, a right eigenvector
need not reduce \(C\), and flatness alone does not give reduction.

## 4. Exact residual target and the generic-direction reduction

Let \(m_\eta=\max_\sigma\operatorname{Re}(\eta p_\sigma)\) and
\(q_\eta=\max\{q_\sigma:\operatorname{Re}(\eta p_\sigma)=m_\eta\}\).
A simultaneous permutation maximizer exists if and only if

\[
M_\eta=m_\eta,\qquad G_\eta=q_\eta.
\]

The inequalities \(M_\eta\ge m_\eta\) and (when equality holds)
\(G_\eta\ge q_\eta\) are immediate from feasibility of permutations.
When \(M_\eta\ne0\), (L) is equivalent to these equalities: a normal
lexicographic maximizer is nonsingular and
NormalOrbit.lean, joint_diagonalization_of_normal_support_frobenius_maximum,
gives a common eigenbasis, hence a matching permutation; the converse
is immediate. Do not extend this equivalence to singular normal sums
without a separate argument.

If the determinant hull inclusion is already known for a pair and \(\eta\)
exposes a unique nonzero matching-product value \(p\), then every support
maximizer commutes. In fact the hull condition forces its determinant to be
\(p\). Finiteness of the matching products and the strict gap to every
different product imply that the same \(p\) maximizes every sufficiently
nearby direction. Pick two noncollinear such directions. The nonsingular
two-direction stationarity theorem in Variational.lean,
commute_of_two_support_maxima, gives commutation. The sum is normal, and
this includes all Frobenius ties.

This also gives a useful generic reduction: it suffices, for proving (N)
in all orders, to prove normality of some maximizer on the dense set of
spectral data and directions with distinct nonzero matching products and
a unique maximizing matching product. For orders with more than one
permutation the products of distinct permutations are different
polynomials (compare the coefficient of \(\prod_{k\ne j}b_k\) for a
column on which they differ). Their equality sets and the zero-product
sets have empty interior. For such spectra only finitely many unit
directions have a tie or zero support. Approximate arbitrary spectral
data and direction by this dense set, take a convergent subsequence
of the chosen unitaries, and pass the global support inequalities and
normality to the limit by continuity. This proves (N) on the limiting
data. The same limit argument does *not* prove (L): a limiting support
face can gain new ties of larger Frobenius norm.

Therefore generic universal normality, unlike unrestricted (U), is a
consistent target. By NormalSupportMaximum.lean it is still equivalent
in all orders to MOC (with the generic restrictions just specified).
The unresolved step is to exclude an orbit whose support exceeds every
matching product, or to prove an appropriate joint determinant/norm
representation on the primary maximizing face. The exact rank-one
conditions in Section 3 do not by themselves establish that step.

## 5. Lean integration targets

The following are proposed formalization tasks, not declarations of
existing checked theorems:

1. General trace expansion of frobeniusSq in diagonal spectral coordinates.
2. Derive the first spectral moments from HasCommonWeights by comparing
   the coefficient of the product of all partner variables except one.
3. Derive the joint determinant/Frobenius law and lexicographic permutation
   realization, including the singleton-law and two-value corollaries.
4. Formalize the exact order-three counterexample to universal normality.
5. Derive the bordered phase identities and flat-phase implication without
   a normal-sum hypothesis.

No new axiom, sorry, or unchecked theorem has been added to the Lean build.

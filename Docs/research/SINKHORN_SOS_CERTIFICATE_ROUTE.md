# A complete polynomial-SOS basis for the global Sinkhorn chart

**Research status:** unrestricted complex MOC4 is NOT proved here. The stated
fixed-\(b\), all-\(z\), full-\(U(4)\) family is now exactly certified by 68
rational Gram certificates and independently reviewed. See
`sinkhorn_spectral_family_exact_verification.json` and
`spectral_family_independent_review.md`. Floating SDP success alone is not proof.
The verifier is read-only by default; use `--report PATH` for optional output.

## 1. Global chart and polynomial gap

Use the Hadamard matrix and global reduction proved in
`SINKHORN_GLOBAL_REDUCTION.md`. Put

\[
H=\frac12\begin{pmatrix}1&1&1&1\\1&-1&1&-1\\1&1&-1&-1\\1&-1&-1&1\end{pmatrix},
\quad W=H\operatorname{diag}(1,V)H^T,
\quad V=(I+iT)(I-iT)^{-1},\ T=T^*\in M_3.
\]

For actual complex spectra and a support phase \(\eta\), write
\(F(W)=\det(A+WBW^*)\),
\(h=\max_\pi\Re(\eta z_\pi)\), and

\[
G(T)=\det(I+T^2)[h-\Re(\eta F(W))].
\]

The previous reduction establishes that \(G\) is a real polynomial in nine real
coordinates, of degree at most six. With
\(R_0=\tfrac12\mathbf1\mathbf1^T-I\),

\[
G_6(T)=[h-\Re(\eta F(R_0))]\det(T)^2=g_{R_0}\det(T)^2,
\qquad g_{R_0}\ge0.
\]

No assumption that the identity pairing supports is necessary in this section.
If it does support, \(G(0)=0\); otherwise \(G(0)\ge0\). In either case \(G_1=0\).

### Rank-one restriction

For every rank-one Hermitian \(L\), the restriction \(G(tL)\) has degree at most
two. Indeed the corresponding \(W-I\) is a rank-one update. Every minor of \(W\)
has a numerator affine in \(t\), with common Cayley denominator affine in \(t\).
The spectral Cauchy–Binet expansion is therefore a sum of squared moduli of
affine numerators; multiplying by \(\det(I+t^2L^2)\) leaves degree at most two.
This is an algebraic identity, not a support or positivity assertion.

## 2. Complete SOS basis — not a nonnegativity-to-SOS theorem

Define the 20 real polynomials

\[
q(T)=(1,\operatorname{vec}_{\mathbb R}T,
\operatorname{vec}_{\mathbb R}\operatorname{adj}T,\det T),
\]

where real vectorization lists the three diagonal entries and real/imaginary
parts of entries 12, 13, 23. Then

> **SOS-basis lemma.** If \(G\) is a polynomial sum of real squares, it has a
> representation \(G=q^TXq\) with a constant real symmetric \(X\succeq0\).
> Conversely such a matrix gives a polynomial sum of squares. If \(G(0)=0\),
> the constant coordinate can be deleted, leaving a 19-by-19 Gram matrix.

**Proof.** In any \(G=\sum f_j^2\), the summands have degree at most three:
otherwise their highest homogeneous parts would give a nonzero sum of squares
above degree six. On every rank-two Hermitian \(T\), the equality
\(G_6=\sum f_{j,3}^2=g_{R_0}\det(T)^2=0\) makes each cubic part vanish.
Consequently \(f_{j,3}=c_j\det T\). To justify divisibility, the real rank-two
Hermitian locus is Zariski dense in the determinant hypersurface: on an
invertible principal 2-by-2 block it has the Schur parametrization
\(t_{33}=v^*T_{[12]}^{-1}v\), with eight free real coordinates. The determinant
polynomial is irreducible; after complexifying the nine Hermitian coordinates
it is the generic 3-by-3 determinant. The rank-at-most-two variety is
irreducible by the factorization \(M=XY\), and the determinant is squarefree
at \(\operatorname{diag}(1,1,0)\). Degree three now forces the scalar quotient.

Restrict next to rank-one \(L\). Since all cubic parts vanish there and
\(G(tL)\) has degree at most two, its degree-four coefficient is
\(\sum f_{j,2}(L)^2=0\). Every quadratic part therefore vanishes on rank-one
Hermitian matrices. These quadratics are precisely the real span of the nine
2-by-2 cofactors, i.e. the real coordinates of \(\operatorname{adj}T\).
One can see this either from the rank-one determinantal ideal, or by substituting
\(T=zz^*\) in a general real quadratic: its 45 coefficients satisfy 36
independent linear conditions, with the nine cofactors forming the kernel.
Thus each \(f_j\) is a real linear combination of the 20 displayed polynomials.
If \(G(0)=0\), every summand has zero constant. This proves the lemma. \(\square\)

**Essential limitation:** a nonnegative sextic need not be SOS. This lemma only
makes the SOS search complete *within polynomial SOS*. Neither the lemma nor
an infeasible numerical SDP settles MOC4.

## 3. Linear compound numerators

Put \(C=\operatorname{adj}T\), \(\tau=\operatorname{tr}T\),
\(e_2=\operatorname{tr}C\), \(d=\det T\). Then

\[
\delta_-=\det(I-iT)=1-e_2+i(d-\tau),\qquad
N_+=(1+e_2-id)I-2C+i(2T-\tau I).
\]

Direct multiplication using \(TC=dI\) gives
\(V=N_+/\delta_-\). Also
\(\det V=\overline{\delta_-}/\delta_-\). In the ordered wedge-pair basis
\((12,13,23)\), put

\[
J=\begin{pmatrix}0&0&1\\0&-1&0\\1&0&0\end{pmatrix},\qquad
N_2=J\overline{N_+}J.
\]

Then \(\wedge^2V=N_2/\delta_-\). All compound numerators of
\(\operatorname{diag}(1,V)\), for orders zero through four, are respectively

\[
\delta_-,\quad
\operatorname{diag}(\delta_-,N_+),\quad
\operatorname{diag}(N_+,N_2),\quad
\operatorname{diag}(N_2,\overline{\delta_-}),\quad
\overline{\delta_-}.
\]

Conjugation by \(\wedge^kH\) gives the compound numerators of \(W\). They are
linear in the 20 coordinates. Furthermore
\(\det(I+T^2)=|\delta_-|^2\).
For \(|I|=|J|=k\), the actual determinant expansion is

\[
F(W)=\sum_{k,I,J}\Bigl(\prod_{i\notin I}a_i\Bigr)
\Bigl(\prod_{j\in J}b_j\Bigr)|\det W[I,J]|^2.
\]

Thus \(G=q^TQq\) for an explicitly constructed rational/real symmetric matrix
\(Q\). It is *not* necessary that this canonical \(Q\) be PSD; polynomial
relations between coordinates allow a different PSD Gram representation.

## 4. One explicit spectral family: complete support fan

The running experiment uses

\[
a=(0,\tfrac12,1,z),\qquad b=(i,-i,1+i,-1+2i),\qquad z\in\mathbb C.
\]

Retain actual spectral products by using
\(w=\eta z\) and real coordinates
\(\theta=(\Re w,\Im w,\Re\eta,\Im\eta)\).
Each permutation support is linear in these four variables. The convex hull of
the 24 doubled coefficient vectors is full-dimensional. Exact enumeration of
all \(\binom{24}{4}=10626\) quadruples yields **68 distinct outward facet normals**.
Every support-cone extreme ray is one of these normals.

A PSD Gram certificate for each of these 68 rays therefore establishes the
support inequality for *all* \(z,\eta\), and hence MOC for every unitary in this
one spectral family. The argument is not limited to identity-support directions:
all cones and all possible maximizing permutations are covered. On each normal
cone, \(h\), \(G\), and the candidate Gram may be combined linearly from the
certificates at its generating rays.

The preliminary 14-ray experiment covered only the identity-support cone. That
experiment alone would NOT establish the all-directions family theorem.


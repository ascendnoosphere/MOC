## Structural setup for the retained matching-law results

Let X=[x_1,x_2,x_3] and Y=[y_1,...,y_n] be complex two-row coisometries: XX*=YY*=I_2. Define q^X_{ik}=|det[x_i,x_k]|², q^Y_{jl}=|det[y_j,y_l]|², and F_{ij}=|det[x_i,y_j]|². A size-two matching has edges {(i,j),(k,l)}, with i≠k and j≠l. Its associated spectral product is (a_i+b_l)(a_k+b_j): this crossing convention makes its mixed terms correspond to the matching edges. The common law reproduces q^X, q^Y and F simultaneously, independently of the complex spectra a,b. Consequently it reproduces det(X diag(a)X*+Y diag(b)Y*). The complete retained proof is [the three-color common matching theorem](geometry_three_color_theorem.md), especially Sections 1, 4–6. These are the structural results of original Rounds 063–065.

For the subset cuts, put q=q^Y, d_j=Σ_{l≠j}q_{jl}=||y_j||², q(S)=Σ_{j<l; j,l∈S}q_{jl}, inc_q(S)=Σ_{j∈S}d_j−q(S), and F_i(S)=Σ_{j∈S}F_{ij}. More generally, for any number of colors, nonnegative q and F with Σq=1 and Σ_iF_{ij}=d_j admit an allocation of each right edge to two distinct endpoint colors exactly when F_i(S)≤inc_q(S) for every i,S. See Sections 1–3 of the linked theorem. This is the allocation result used in Round 080; it does not prescribe an additional left-pair marginal for four or more left parents.

For actual coisometries, K=Σ_{j∈S}y_jy_j* satisfies 0≤K≤I, q(S)=det K and inc_q(S)=tr K−det K. In coordinates with x_i=√λ e_1, where 0≤λ=||x_i||²≤1, write K=[[a,z],[conj(z),b]]. Then F_i(S)=λb and the cut slack is a(1−b)+(1−λ)b+|z|². This supplies the a,b used in Round 068; see Section 4 of the linked theorem.

With three left labels, the omitted-label identity is q^X_{ik}=1−Σ_jF_{rj} when {i,k,r}={1,2,3}. Thus, in coordinates (q^Y,F), the complete matching-polytope description consists of q^Y≥0, Σq^Y=1, F≥0, Σ_iF_{ij}=d_j, left degrees Σ_jF_{ij}≤1, and the subset cuts above. Only cuts with 2≤|S|≤n−2 are needed in addition to these elementary constraints. This is the analytic H-description in original Round 067; its completeness follows from the allocation theorem and the omitted-label identity, without a separate finite enumeration certificate.

## Round 068 — Generic frames admit a law positive on every matching

**Mechanism.** Suppose every left-pair, right-pair, and mixed determinant is
nonzero. For a nontrivial subset cut with |S|,|S^c|≥2, nonzero right-pair
determinants imply 0<K<I. In Round 064, a>0 and 1−b>0, so the cut is strict.
The elementary coordinate and omission inequalities are strict as well.
Thus the actual coefficient point is in the relative interior of the
matching polytope.

The uniform law on N=6C(n,2) matchings has
q^X=1/3, q^Y=1/C(n,2), and F_{ij}=2/(3n). For a subset of size k its cut
slack is

\[
 \frac{k(4n-3k-1)}{3n(n-1)}.
\]

Choose ε>0 smaller than every ratio of an actual nontrivial defining
slack to the corresponding uniform slack, and smaller than one. Subtract
ε times the uniform coefficient point and divide by 1−ε; the remainder
still satisfies the complete H-description. Its matching law, combined
with ε times the uniform law, gives every matching weight at least ε/N.

**Status: proved.** This supplies an explicit positive-weight margin and
supports finite perturbation arguments without selecting a discontinuous
extreme LP solution.

## Round 069 — The all-n theorem gives an exact Bell-local class

**Mechanism.** For rank-one qubit POVMs E_i=x_ix_i* and G_j=y_jy_j*, the
singlet probabilities are q^X_{ik}/2 in the XX context, q^Y_{jl}/2 in YY,
and F_{ij}/2 in XY. Choose a matching {(i,j),(k,l)} with the common law.
Assign deterministic outputs

\[
 (A_X,A_Y;B_X,B_Y)=(i,l;k,j),
\]

and exchange the parties with probability 1/2. The XX and YY contexts
then have the required unordered-pair laws, and XY has the two matching
edges with their required incidence probabilities.

**Status: proved.** Two identical setting choices on both parties are
Bell local whenever one setting is a three-outcome rank-one qubit POVM
and the other is any finite-outcome rank-one qubit POVM. Arbitrary local
output postprocessing preserves the supplied local model. This statement
does not assert locality when the parties use unrelated setting pairs.

## Round 070 — A codimension-two MOC boundary theorem in every dimension

**Mechanism.** Let A_0 have rank one and B_0 rank n−3, with orthonormal
leading frames v and W whose concatenation has independent columns.
Let their nonzero eigenvalues be α and β_1,...,β_{n−3}. Perturb normally
on their respective kernels:

\[
 A(t)=A_0+tA_1,\qquad B(t)=B_0+tB_1.
\]

The common orthogonal complement H of the leading frames has dimension
two. Put δ=det Gram(v,W), so 0<δ≤1. Exterior expansion gives

\[
 \lim_{t\to0}\frac{\det(A(t)+B(t))}
 {\alpha\prod_s\beta_s\,t^2}
 =\delta\det\bigl(P_H(A_1+B_1)|_H\bigr).
\]

The compression of the A kernel eigenbasis is a 2×(n−1) coisometry; that
of the B kernel eigenbasis is 2×3. Round 065 controls its determinant.
Each size-two matching between these small spectra is a leading
permutation product: the sole large A eigenvalue uses the remaining
small B label, and the n−3 large B eigenvalues use the remaining small
A labels. Permutations pairing two leading eigenvalues have zero
normalized limit.

**Status: proved for every n≥4**, with the ranks reversed by symmetry. The
normalized determinant lies in the limiting permutation hull. This is
a boundary theorem, not an assertion about every nonzero t.

## Round 071 — An explicit finite neighborhood of that boundary

**Mechanism.** Let r=n−2 be the number of leading vectors V_s, with leading
eigenvalues γ_s, and D=A_1+B_1. For S⊆[r], let δ_S=det Gram(V_S) and
H_S=range(V_S)^⊥. Multilinear determinant expansion gives exactly

\[
 \frac{\det(A(t)+B(t))}{(\prod_s\gamma_s)t^2}
 =\sum_{S\subseteq[r]}
 t^{r-|S|}\frac{\delta_S\det(P_{H_S}D|_{H_S})}
 {\prod_{s\notin S}\gamma_s}.
\]

Both this expression and every normalized permutation product are
polynomials of degree at most r. Write their coefficients as d_k and
v_{π,k}. If d_0 lies in the interior of the limiting hull with Euclidean
margin ρ, put L_k=max_π|v_{π,k}|. Then

\[
 \sum_{k=1}^r |t|^k(|d_k|+L_k)<\rho
\]

implies MOC at that t. Indeed every support direction loses at most
Σ|t|^kL_k on the moving hull, and the determinant moves by at most
Σ|t|^k|d_k|. Round 068 and noncollinearity of product vertices give a
generic way to obtain ρ>0.

**Status: proved.** This is a genuine finite open region in every dimension,
with a computable sufficient radius, rather than only an asymptotic claim.

## Round 072 — Scalar CMC for any parents when one compressed summand is normal

**Mechanism.** First record the projective/frame consequence of the common
law: for any two-row frame X and any chosen orthonormal coordinate basis,
there is an ordered pair (I,K) of distinct parent labels such that

\[
 \mathbb E a_I=A_{11},\qquad
 \mathbb E a_K=A_{22},\qquad
 \mathbb E(a_Ia_K)=\det A,
 \quad A=XD_aX^*.
\]

The ordered marginals are the squared entries of the two frame rows;
the unordered pair law is q^X. Suppose A is normal and choose a basis
in which it is diagonal. The random diagonal normal matrix
A_s=diag(a_I,a_K) has E A_s=A and E det A_s=det A. Because
det(A_s+B)=det A_s+det B+tr(adj B A_s) in dimension two,

\[
 \det(A+B)=\mathbb E\det(A_s+B).
\]

For every A_s, the projective/frame common law against Y puts
det(A_s+B) in the desired matching-product hull. Averaging proves the
same for A+B. The spectral labels selected from X remain distinct.

**Status: proved. Scalar CMC(2;m,n) whenever either compressed summand is
normal, with arbitrary complex parent spectra.** In particular this
covers any collinear spectrum on one side, whose compression is normal.

## Round 073 — Two nonnormal summands can be glued when they share an eigenvector

**Mechanism, supplied by the root researcher.** A common eigenvector can be
chosen as the first vector of an orthonormal basis. Both compressed
summands are then upper triangular. Apply the ordered-parent law from
Round 072 separately to X and Y and take these two laws independently.

The expected matching product is

\[
 \det A+\det B+A_{11}B_{22}+A_{22}B_{11}.
\]

Upper triangularity makes this equal to
(A_{11}+B_{11})(A_{22}+B_{22})=det(A+B). Thus the matching products
give the required convex combination even if neither summand is normal.

**Status: proved.** Simultaneous unitary upper triangularization suffices;
independently triangularizing the two matrices in different bases would
not justify the cross terms.

## Round 074 — A basis-free algebraic criterion for the triangular class

**Mechanism.** For 2×2 complex matrices,

\[
 \boxed{\det[A,B]=0
 \quad\Longleftrightarrow\quad
 A,B\text{ have a common eigenvector}.}
\]

If A has distinct eigenvalues, use its eigenbasis. The commutator has
off-diagonal entries (α−δ)B_{12} and −(α−δ)B_{21}; zero determinant
means one of the off-diagonal entries of B vanishes, giving a common
eigenline. If A is a nonscalar Jordan block, subtract its eigenvalue
and scale to N=[[0,1],[0,0]]. For B=[[b,c],[d,e]],
[N,B]=[[d,e−b],[0,−d]], whose determinant is −d². Again d=0 gives the
common eigenline. A scalar A is immediate. The reverse direction
follows from simultaneous triangularity.

**Status: proved.** Round 073 therefore establishes scalar CMC on the
explicit algebraic locus det[A,B]=0, including noncommuting examples.


## Round 078 — A direct scalar rounding formula and its exact geometric defect

**Mechanism.** Apply the projective/frame ordered-parent laws independently
to both compressed summands in any common orthonormal basis. Their
expected matching product M belongs to the desired scalar hull, and

\[
 \boxed{M=\det(A+B)+A_{12}B_{21}+A_{21}B_{12}.}
\]

Write A=a_0I+a·σ and B=b_0I+b·σ with complex Bloch vectors a,b. If the
chosen basis has real unit axis n, the defect is

\[
 S(n)=2\,[a\cdot b-(a\cdot n)(b\cdot n)].
\]

Thus basis averaging would prove the scalar conjecture if zero belonged
to conv{S(n):n∈S²}. Equivalently, for the complex symmetric matrix
T=(ab^T+ba^T)/2, it would require tr T to lie in
{tr(TH):H real PSD, tr H=1}. This is a precise two-observable numerical
range condition, not an automatic trace identity.

The formula also gives the rigorous error estimate
dist(det(A+B), matching hull)≤min_n|S(n)|. In a Schur basis of A it
reduces to |A_{12}B_{21}|; a known interior hull margin larger than that
quantity certifies the scalar conjecture at the given data.

**Scope.** The formula and error bound are proved. A universal zero-defect basis-averaging theorem is not established here.


## Round 080 — A coarse four-parent merging theorem, with the remaining split explicit

**Mechanism suggested by the root researcher and proved here.** For four
left effects E_i=x_ix_i*, merge labels 1 and 2 into Q with effect
E=E_1+E_2. Put d=det E=q^X_{12} and q=q^Y. Reserve total mass d for
selecting Q twice, assigning its right-edge distribution exactly d q.
That event contributes d d_j to the Q incidence at each right vertex j.

The residual right law is (1−d)q. Its three color-incidence effects are

\[
 H_Q=\operatorname{adj}E-dI,\qquad
 H_3=\operatorname{adj}E_3,\qquad
 H_4=\operatorname{adj}E_4.
\]

They are PSD and sum to (1−d)I. Indeed if the eigenvalues of E are e_1,e_2,
those of H_Q are e_2(1−e_1), e_1(1−e_2). Moreover

\[
 \operatorname{tr}H_Q=\operatorname{tr}E-2d\le1-d,
 \qquad \operatorname{tr}H_i=\|x_i\|^2\le1-d\quad(i=3,4).
\]

The first bound is det(I−E)≥0. For the others,
E≤I−E_i implies d≤det(I−E_i)=1−||x_i||².
For every positive contraction K,

\[
 \operatorname{tr}(H_iK)
 \le\operatorname{tr}(H_i)\lambda_{\max}(K)
 \le(1-d)(\operatorname{tr}K-\det K).
\]

Thus every residual colored-edge cut holds. Round 063 supplies its
three-color allocation. Restoring the reserved QQ event yields a
coarse common law with all mixed incidences, q^Y, and the correct
left coarse pair probabilities: fixing the QQ probability and all
three degrees determines QQ,Q3,Q4,34 uniquely.

The unsolved step is a compatible split of Q into children 1 and 2. Filtering by E^{−1/2} makes the children a projective frame, but does not by itself establish the required child-incidence domination against the unchanged Y law.


**Scope.** The coarse merging theorem is proved; compatible scalar or full child splitting is not established. In particular the theorem does not yet furnish the
rank-three CMC(3;3,4) assertion equivalent to MOC4. The independently
proved realification allows that remaining problem to be studied with
real SO(4) eigenvector changes, but does not remove this coupling issue.


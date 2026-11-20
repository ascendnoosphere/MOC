# Exterior compression, Boolean Markov kernels, and the exact product-test order

This note proves the exterior compression representation, exact composition identities, and positive forest-circuit and two-line classes. The product-test order is equivalent to unrestricted complex MOC; it is not proved here.

## 1. Tensor convention and exterior compression

Let V=C² and H_n=V^{tensor n}. For a permutation π, use the right-action
operator

    T_π(v_1⊗...⊗v_n)=v_{π(1)}⊗...⊗v_{π(n)}.

Thus T_π T_σ=T_{σ∘π}. This inverse convention matters in the trace identity.
For U∈U(n), define

    R(U)=(det U)^{-1} sum_π sgn(π) [product_i U_{i,π(i)}] T_π.       (1)

The map

    J:H_n→exterior^n(C^n⊗V),
    J(v_1⊗...⊗v_n)=(e_1⊗v_1)∧...∧(e_n⊗v_n)

is an isometry: computational-basis tensors map to distinct orthonormal
wedges. Let Γ(U)=exterior^n(U⊗I_V)/(det U), a unitary operator. Expansion
of a wedge, followed by projection onto the subspace with one particle at
each site, gives

    R(U)=J* Γ(U) J.                                               (2)

Indeed, the factor appearing at output site i originated at input π(i),
contributing U_{i,π(i)}, while the reordering of the exterior factors
contributes sgn(π). This proves (1), including its convention, directly.

## 2. Every weight block is a nonnegative compound matrix

Let |I> denote the tensor with a 1 at positions I and a 0 elsewhere. The
operator preserves |I|. If |I|=|J|=k, regroup the color-1 wedge factors and
then the color-0 factors. The unnormalized compression entry is

    ε_I ε_J det U[I,J] det U[I^c,J^c].

Here ε_I and ε_J are the signs of the two regroupings. The complementary
minor identity for a unitary matrix is

    det U[I^c,J^c]=ε_I ε_J det U overline(det U[I,J]).

The signs and determinant phase cancel, giving the exact formula

    <I|R(U)|J>=|det U[I,J]|².                                    (3)

Consequently R(U) is real and entrywise nonnegative. Each weight block is
doubly stochastic, since exterior^k U is unitary. In particular its rows
and columns sum to one and its Euclidean operator norm is at most one.
Empty and full blocks are the scalar 1.

This is a simultaneous positivity statement on the entire Boolean lattice,
not merely on the singleton matrix (|U_ij|²). A common probability law on
permutations would require the same mixture in every block; that additional
compatibility is false for some actual U.

## 3. Equivariance and the two-row representation quotient

The tensor permutations commute with g^{tensor n} for every g∈GL(2,C), so
R(U) does as well. The same fact follows from J g^{tensor n}=
exterior^n(I⊗g)J. Thus R(U) commutes with the Boolean raising and lowering
operators and preserves all global symmetric tensors pointwise:

    R(U)v^{tensor n}=v^{tensor n}.

Schur–Weyl duality decomposes H_n into the two-row partitions (n-k,k),
0≤k≤floor(n/2). The image of the permutation algebra has dimension

    sum_k (binom(n,k)-binom(n,k-1))² = Catalan(n).

It is the classical Temperley–Lieb quotient at loop parameter 2, with the
three-strand antisymmetrizer vanishing. This can be seen directly from
exterior³(C²)=0. If e_i=(I-T_(i,i+1))/2, then

    e_i²=e_i,  e_i e_(i+1) e_i=e_i/4,

and distant e_i commute. The tensor convention above only reverses the
permutation multiplication; it does not change this commutant algebra.

Primary background sources inspected:

* Arun Ram, *Combinatorial Representation Theory*, Appendix A.5,
  https://math.soimeme.org/~arunram/Preprints/CRTAppendixASectionA5.html
* M. Q. Trinh, quantum Schur–Weyl lecture notes,
  https://mqtrinh.github.io/math/teaching/yale/math-665/notes/quantum-schur-weyl.pdf

No categorical positivity conclusion follows just from passing to this
quotient. The order cone of convex permutation mixtures is strictly smaller
than the entrywise-positive equivariant cone in relevant dimensions.

## 4. MOC is exactly a two-sided product-test order

Let u_i∈V and let w_i be complex linear covectors. Put

    u=u_1⊗...⊗u_n,  w=w_1⊗...⊗w_n,
    C_ij=w_i(u_j).

Then

    w(T_π u)=product_i C_{i,π(i)},
    w(R(U)u)=det(C∘U)/det U.                                    (4)

Therefore the exact proposed order condition is

    w(R(U)u) ∈ conv_R {w(T_π u):π∈S_n}
    for every pair of product vectors/covectors u,w.              (5)

This is equivalent to unrestricted complex MOC. The usual spectral data
are obtained by u_j=(b_j,1)^T and w_i=(1,a_i), giving C_ij=a_i+b_j.
Conversely, every rank-at-most-two C is a limit of matrices admitting a
factorization C_ij=x_i y_j+z_i t_j with every z_i,y_j nonzero. Divide row i
by z_i and column j by y_j to obtain

    C'_ij=x_i/z_i+t_j/y_j.

Row and column scaling multiply the determinant ratio and every matching
product by the same nonzero complex scalar. Thus MOC implies (5) on the
generic set, and continuity gives all product u,w. Equivalently, the
rank-one idempotent normalization w_i(u_i)=1 is only a convenient affine
chart; it is not a restriction on the final product-test theorem.

## 5. The actual cost variety and the categorical dual

Choose a symplectic identification V*≅V. Each C_ij=w_i(u_j) becomes a
bracket [v_i,u_j] of two spinors. The permutation products are the
bipartite perfect-matching invariants of 2n ordered points on P¹. Their
linear span is the SL(2)-invariant space of dimension Catalan(n); bracket
straightening is the Plücker form of the Temperley–Lieb quotient.

Projectively, the rank-two matching-product variety has generic dimension
2n-3: there are 2n projective spinors, modulo the three-dimensional PGL(2)
action. Equivalently, a rank-two n×n matrix has dimension 4n-4 and row/column
scaling removes 2n-1 dimensions. The bracket invariants separate generic
configurations, so this count is exact generically.

For n=4, the complex cost variety is the five-dimensional ordered-eight-
point quotient in P¹³. A real support cost Re(ηZ) is on a conjugate secant
of this variety. Its real affine parameter dimension is at most 12,
whereas the full real Temperley–Lieb cost space has dimension 14. Thus an
arbitrary linear separator of a non-permutation Boolean kernel need not
be an actual spectral support cost.

## 6. Exact composition defect and phase-averaged composition

Write P=JJ*. Since Γ(UV)=Γ(U)Γ(V),

    R(UV)-R(U)R(V)=J*Γ(U)(I-P)Γ(V)J.                            (7)

The missing paths leave the one-particle-per-site sector and subsequently
return. They are the exact obstruction to making U↦R(U) a functor under
ordinary composition.

For arbitrary u,w (product is not needed for this estimate), Cauchy–Schwarz
gives the quantitative identity-based bound

    |w*[R(UV)-R(U)R(V)]u|²
    ≤ (||w||²-||R(U)*w||²)(||u||²-||R(V)u||²).                  (8)

Indeed, these two factors are the squared norms of
(I-P)Γ(U)*Jw and (I-P)Γ(V)Ju. Thus (8) is a spectral-dependent gluing
certificate: if the classical center w*R(U)R(V)u has enough support margin
inside the permutation hull to absorb the displayed radius, the composite
obeys MOC for that test. The universal margin comparison is still missing.

There is an exact averaged composition law. If D=diag(e^{iθ_1},...,e^{iθ_n})
with independent uniform phases, then

    E_D R(U D V)=R(U)R(V).                                     (9)

For each compound entry, Cauchy–Binet expands the amplitude as
sum_K det U[I,K] e^{i sum_(k∈K)θ_k} det V[K,J]. Averaging its squared
modulus removes precisely the terms K≠L, leaving the matrix product of
the squared-compound kernels. This proves (9) at every level.

Thus the diagonal-double-coset convolution, defined by inserting a Haar
diagonal between two representatives, has an exact positive representation
R into these equivariant Markov operators. Associativity follows from
independent Haar insertions and Fubini. The map is invariant under diagonal
phases on either side. Ordinary multiplication of double cosets is not
well defined; the averaged convolution is the relevant composition law.

## 7. A complete all-dimensional forest-circuit theorem

For a two-site unitary G on sites i,j, let t=|G_ij|². Formula (3) gives

    R(G)=(1-t)I+tT_(ij).                                      (10)

Now suppose U is block diagonal and i,j are in two distinct blocks. In
the compound expansion of GU, a row subset I has at most two possible
intermediate subsets: I itself, and I with i,j exchanged. These two
subsets have different cardinalities in each old block. A block-diagonal
minor U[K,J] vanishes unless K and J have equal cardinalities in every
block. Therefore at most one of the two intermediate amplitudes is
nonzero, so there is no interference:

    R(GU)=R(G)R(U).                                           (11)

It follows inductively that if a unitary is built from two-site gates
whose edge list forms a forest, with **each edge used at most once**,
then its complete squared-minor
profile has a common permutation law. The law is the product, in circuit
order, of the lazy transposition distributions (10). The angles and
complex phases are arbitrary. Each new forest edge joins two distinct
components of the preceding circuit, exactly as required by (11).
A forest as a simple spatial graph is insufficient if its edges are reused:
repeated nearest-neighbor gates can generate general unitaries. The exact
condition is that every gate join distinct preceding components.

More generally, arbitrary initial blocks having common minor laws may be
joined by such bridge gates. Their laws compose positively. This provides
a discrete all-dimensional class; it does not cover a general circuit.
Closing a cycle permits both intermediate amplitudes, and a common law
can already fail in dimension four.

For random phase insertions between arbitrary two-site gates, (9) still
gives the product of lazy transposition laws after averaging. In the
small-angle limit t=rate·dt+o(dt), the averaged generator is

    L=sum_(i<j) rate_ij (T_(ij)-I).

Its restriction to each Boolean level is the exclusion process, and all
levels share one permutation-valued interchange process. This continuous
averaged theorem is exact; it does not imply the pointwise conjecture.

## 8. Product-test closure and a positive two-line theorem

Let C_n be the operators satisfying (5) for every product u,w. It is
convex. It is invariant under left and right multiplication by permutation
operators, since permutation of a product tensor remains a product tensor
and merely relabels the comparison hull. Consequently it is stable under
left or right multiplication by any convex permutation mixture.

It is also monoidal: if R∈C_m and S∈C_n, then R⊗S∈C_(m+n). For product
tests, the scalar is xy, where x and y are convex combinations of the
two comparison sets. Multiplying the two combinations gives nonnegative
product weights on block-preserving permutations, which are among all
permutations of m+n sites. This supplies a genuine tensor-category closure,
but arbitrary composition of two C_n operators is not justified: the
intermediate image of a product input need not be a product input.

There is a stronger positive theorem for two projective input lines.
Let R be any nonnegative GL(2)-equivariant operator whose Boolean columns
sum to one. If the factors u_i lie on at most two projective lines, then

    R u ∈ conv {T_πu}.                                        (12)

If the two lines are distinct, choose one global g∈GL(2) carrying them to
the coordinate lines. Up to one overall scalar, g^{tensor n}u is a single
computational-basis vector |J>. The J-th stochastic column of R expresses
R|J> as a positive mixture of vectors |I> of the same weight. Each is a
permutation of |J>. Conjugate back using equivariance. If there is only
one line, the tensor is globally symmetric and fixed by R.

This proves (5) on that entire input stratum for the larger Boolean cone,
and hence proves the corresponding MOC class with at most two projective
spectral column values. By the same argument applied to R^T, the analogous
output stratum is also covered.

### Two exceptional labels: a stronger all-dimensional positive stratum

For the same larger Boolean cone, (12) holds whenever all but two local
spinors are proportional. Gauge the common line to e_0. If the two
exceptional sites are a,b, write their spinors as αe_0+βe_1 and
γe_0+δe_1. The input has terms only in weights 0,1,2. Let

    p_i=R_1[i,a],  r_i=R_1[i,b],  q_ij=R_2[{i,j},{a,b}].

These are nonnegative, sum(p)=sum(r)=sum(q)=1, and lowering equivariance
gives deg(q)=p+r. An orientation of the edge masses q with first-endpoint
marginal p and second-endpoint marginal r exists precisely when

    q(E(S))≤p(S) for every vertex set S.                        (14)

This is the max-flow/min-cut theorem: split each edge's mass between its
two possible orientations. Its equivalent upper cuts follow from
deg(q)=p+r and total mass one.

The cuts follow directly from positivity of *higher* Boolean levels.
Put s=|S|. Commuting with the appropriate power of the raising operator
gives, with the factorials on the two sides canceling,

    p(S)=sum_{T:|T|=s, a∈T} R_s[S,T],
    q(E(S))=sum_{T:|T|=s, {a,b}⊆T} R_s[S,T].

Thus their difference is the nonnegative sum over a∈T,b∉T. Boundary
s=0,1 is immediate. The ordered two-endpoint law supplied by (14)
reproduces the coefficients αγ, βγp, αδr, βδq of R u. Each ordered pair
is the placement of the two exceptional spinors under a permutation.
This proves the stronger vector-orbit law.

In particular every three-projective-value input in dimension four has multiplicities 2,1,1 and is covered.

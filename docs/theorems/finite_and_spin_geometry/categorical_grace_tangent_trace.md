# Grace operators: tangent classification, finite phase composition, and exact trace deletion

This note proves tangent classification, finite phase composition, and ordinary trace deletion.
It does not establish unrestricted complex MOC. All priority claims are avoided:
the Grace-operator framework and symmetric-exclusion sufficiency are established
background, while complete derivations of the additional statements used here
are supplied below.

## 1. Definitions and the precise remaining question

Let V=C², H_n=V^{⊗n}, and use the tensor convention

    T_π(v_1⊗...⊗v_n)=v_{π(1)}⊗...⊗v_{π(n)}.

Let E_n be the image of the complex permutation algebra on H_n. An operator R
is normalized when it acts as the identity on Sym^n(V). For R∈E_n, write its
graded Boolean matrix entries as R[I,J], with |I|=|J|, and define its symbol

    Q_R(a,b)=Σ_{|I|=|J|} R[I,J] a_{I^c} b_J.                    (1)

This symbol is separately multiaffine in the 2n variables a_i,b_i, homogeneous
of degree n, and injectively encodes R. If R=Σ_π c_π T_π, then

    Q_R(a,b)=Σ_π c_π Π_i(a_i+b_{π(i)}).                         (2)

The coefficient representation in (2) is nonunique when n≥3, but its sum is
well defined and equals the scalar on Sym^n(V). Normalization therefore gives

    Q_R(a,s1)=Π_i(a_i+s),    Q_R(s1,b)=Π_i(s+b_i),
    Q_R(a+t1,b−t1)=Q_R(a,b),    Q_R(1,1)=2^n.                 (3)

Call R a normalized Grace operator if Q_R is stable: it is nonzero whenever
all a_i and b_i have strictly positive imaginary part. Denote this class G_n.
Brändén–Wagner, Proposition 4, identifies this definition with the normalized
Grace-like matching-polynomial definition and with stability preservation by
the permutation-algebra operator. In particular G_n is closed under operator
composition. Ruelle, Proposition 8, proves that each actual unitary kernel

    R(U)[I,J]=|det U[I,J]|²,    U∈U(n),                        (4)

belongs to G_n.

Write A_n=conv_R{R(U):U∈U(n)}. Neither the inclusion G_n⊆A_n nor the scalar product-test hull property on G_n is proved here.

Primary sources inspected:

* David Ruelle, *Grace-like polynomials*, https://arxiv.org/pdf/math-ph/0009030.
* Petter Brändén and David G. Wagner, *A converse to the Grace–Walsh–Szegő
  theorem*, https://arxiv.org/pdf/0809.3225.
* Julius Borcea, Petter Brändén, and Thomas M. Liggett, *Negative dependence
  and the geometry of polynomials*, https://arxiv.org/pdf/0707.2340.

The last source supplies the real multiaffine Rayleigh criterion (Theorem 4.1),
partial-symmetrization preservation (Theorem 4.20), and symmetric-exclusion
sufficiency (Proposition 5.1 / Theorem 5.2). The necessity proof in Section 5
is given independently rather than attributed to a theorem not inspected.

## 2. Reality and positivity follow from normalization and stability

**Proposition 2.1.** Every R∈G_n has real, nonnegative Boolean entries. Each
weight block is doubly stochastic.

**Proof.** The initial coefficient representation (2) may be complex. Since Q
is homogeneous of degree n, upper-half-plane stability also gives
lower-half-plane stability: Q(−z)=(−1)^n Q(z). Fix x∈R^{2n}. The univariate
polynomial q_x(t)=Q(x+t1) has degree n and leading coefficient Q(1)=2^n. A root
with positive or negative imaginary part would contradict the corresponding
half-plane stability. All roots are therefore real, and the leading coefficient
is positive real; hence q_x has real coefficients. In particular Q(x) is real
for every real x. A complex polynomial taking real values on R^{2n} has real
coefficients.

Next let x have all coordinates positive. If Q(x)=0, homogeneity would imply
Q((1+iε)x)=0 for every ε>0, contradicting stability. Thus Q is nonzero on the
connected positive orthant; its value at 1 is positive, so Q(x)>0 there.

For a squarefree degree-n monomial x_S, set x_j=t for j∈S and x_j=1 otherwise.
Because all monomials have degree n, the coefficient of t^n is exactly the
coefficient of x_S. Positivity for all t>0 implies that this coefficient is
nonnegative. These coefficients are precisely the Boolean entries in (1).

Finally, the first identity in (3), by comparison of coefficients of a and s,
gives row sums one. The second gives column sums one. ∎

## 3. Exact finite phase composition

For D_ε=diag(ε_1,...,ε_n), with ε_1=1 and ε_2,...,ε_n∈{−1,1}, one has

    R(U)R(V)=2^{−(n−1)} Σ_ε R(U D_ε V).                        (5)

**Proof.** At weight k, Cauchy–Binet expands

    det(UD_εV)[I,J]=Σ_{|K|=k} det U[I,K] ε_K det V[K,J].

On squaring the absolute value and averaging, the cross term for K,L is
multiplied by E ε_{K△L}. It vanishes unless K△L⊆{1}. Equal cardinalities
exclude K△L={1}; hence only K=L survives. The remaining sum is exactly the
matrix product of the k-th compound-modulus blocks. ∎

Consequently A_n is a compact convex monoid under composition. Compactness
follows from compactness of U(n) and finite-dimensionality. Equation (5),
followed by bilinearity, proves closure under products of arbitrary convex
mixtures. Block sums U⊕V also give

    R(U⊕V)=R(U)⊗R(V),

so A_m⊗A_n⊆A_{m+n}. This is a genuine convex categorical closure, but does not
assert that the nonconvex Grace class equals A_n.

### 3.1 Smaller cyclic designs and a lower bound

Let m_1,...,m_n∈Z/MZ have distinct subset sums within every fixed cardinality.
For ω=exp(2πi/M), put D_l=diag(ω^{lm_1},...,ω^{lm_n}). Character orthogonality
gives the alternative exact formula

    R(U)R(V)=M^{−1} Σ_{l=0}^{M−1} R(U D_l V).                  (6)

For n=4, M=6 and exponents (0,1,2,4) work: their six two-element sums are all
six residues, singleton sums are distinct, and triple sums are complements
of singleton sums. Thus six actual unitary kernels suffice in (6).

A universal positive phase quadrature with N nodes must have

    N≥binom(n,floor(n/2)).                                    (7)

Indeed, at the middle weight, the binomial(n,floor(n/2)) distinct subset
characters must be orthonormal in the N-dimensional L² space of quadrature
nodes. The required orthogonality follows from universally cancelling all
cross terms. Here is a direct verification of necessity. Fix a unitary U with
all relevant row minors nonzero. As a column frame of V varies, its compound
column runs through all unit decomposable k-vectors. The proposed identity
says that one Hermitian form, whose entries are the character-moment errors
times those nonzero U minors, vanishes on all these vectors. Such a form is
zero: for coordinate k-sets K,L, factor out their common basis vectors and
test the decomposable vector made from factors e_{a_j}+z_j e_{b_j}, where
the a_j and b_j enumerate K\\L and L\\K. In its Hermitian quadratic form,
the coefficient of the antiholomorphic monomial Π_j conjugate(z_j), with
no holomorphic factors, isolates the K,L matrix entry. Thus every moment
error vanishes. Therefore the six-node n=4 phase design
is optimal among universal positive phase quadratures. The bound does not
claim that six is necessary for an individual pair U,V or for arbitrary
representations by actual kernels that are not a fixed phase quadrature.

The exact cyclic phase designs and cyclic minimality bounds checked by
code/theorems/finite_and_spin_geometry/categorical_second_batch_exact.py are:

| n | Middle-level lower bound | First cyclic M | Exponents |
|---|---:|---:|---|
| 2 | 2 | 2 | (0,1) |
| 3 | 3 | 3 | (0,1,2) |
| 4 | 6 | 6 | (0,1,2,4) |
| 5 | 10 | 11 | (0,1,2,4,7) |

The n=5 result excludes only cyclic designs with M=10. It does not exclude a
noncyclic ten-node quadrature.

## 4. First-order Rayleigh identity at the identity operator

Let R_t∈G_n, t≥0, with R_0=I and R_t=I+tL+o(t). Write

    c_i=a_i+b_i,    P=Π_i c_i,    Q_{R_t}=P+tF+o(t),
    P_{ij}=Π_{k≠i,j} c_k.

For i≠j the Rayleigh difference is

    Δ_{ij}(Q)=Q_{a_i}Q_{a_j}−Q Q_{a_i a_j}.

Since Δ_{ij}(P)=0 identically, its first-order term is nonnegative at every
real (a,b). Direct expansion gives the useful exact identity

    (d/dt)_{0+} Δ_{ij}(Q_{R_t})
      =−P_{ij} F|_{c_i=c_j=0} ≥0.                             (8)

To verify it without cancellation assumptions, write F=A a_i a_j+B a_i+
C a_j+D, with A,B,C,D independent of a_i,a_j, and substitute a_i=−b_i,
a_j=−b_j on the right. The derivative on the left is
P_iF_j+P_jF_i−PF_{ij}−P_{ij}F, which reduces to the same expression.

Only necessity of the real-stability Rayleigh criterion is used here. The
same calculation applies to any sequence t_m↓0 and R_m∈G_n for which
(R_m−I)/t_m converges; a differentiable path is not essential.

## 5. Complete tangent-cone classification

**Theorem 5.1.** The contingent tangent cone of G_n at I is exactly

    { Σ_{i<j} r_{ij}(T_(ij)−I) : r_{ij}≥0 }.                   (9)

In particular any differentiable one-sided Grace path through I has precisely
such a first derivative. For n=1 the tangent cone is {0}.

**Proof of necessity.** Keep the notation of Section 4 and assume n≥2. Fix
i,j and abbreviate f=F|_{c_i=c_j=0}. Equation (8) says −P_{ij}f≥0 for all real
values of the remaining variables.

For each k outside {i,j}, the factor c_k changes sign across c_k=0. If f did
not vanish on that hyperplane, a generic real point on it with all other
c_l nonzero and f nonzero would give a sign change of −P_{ij}f, impossible.
Therefore c_k divides f. The different linear factors are coprime, so

    f=P_{ij} H_{ij}.

Here H_{ij} is independent of all outside variables a_k,b_k. For example,
as a polynomial in a_k over the integral domain of other variables,
deg_{a_k}((a_k+b_k)H)=1+deg_{a_k}H. Separate multiaffinity of f therefore
forces deg_{a_k}H=0, and the same reasoning in b_k forces deg_{b_k}H=0.
Homogeneity makes H_{ij} a quadratic homogeneous polynomial in b_i,b_j.

Translation covariance (3) leaves the c's fixed and translates every b by
the same amount. Consequently H_{ij}(b_i−s,b_j−s)=H_{ij}(b_i,b_j). Such a
homogeneous quadratic is κ_{ij}(b_i−b_j)². Equation (8), at points with all
outside c_k nonzero, forces κ_{ij}≤0. Write κ_{ij}=−r_{ij}, r_{ij}≥0:

    F|_{c_i=c_j=0}=−r_{ij}(b_i−b_j)² P_{ij}.                  (10)

The symbol of T_(ij)−I is

    F^{ij}=(a_i−a_j)(b_i−b_j) P_{ij}.                         (11)

Its restriction c_i=c_j=0 is exactly −(b_i−b_j)²P_{ij}; its restriction
c_k=c_l=0 is zero for any different pair {k,l}, since the outside product
then contains at least one vanishing c. Set

    F_0=F−Σ_{i<j}r_{ij}F^{ij}.

It follows that F_0 vanishes whenever any two of the c variables vanish.
In the independent polynomial coordinates (c,b), this is membership in

    ⋂_{i<j}(c_i,c_j),

the monomial ideal generated by Π_{k≠i}c_k. To see the ideal description,
a monomial survives outside some pair ideal exactly when its c-support
omits both members of that pair; membership in every pair ideal therefore
requires c-support of size at least n−1.

F_0 is multiaffine in c, since F_0 was multiaffine in a, and is homogeneous
of total degree n. Hence it must have the form

    F_0=A Π_k c_k + Σ_i (Π_{k≠i}c_k) Σ_j l_{ij} b_j.           (12)

Returning to coordinates (a,b), consider the coefficient of b_j². It is

    Σ_{i≠j} l_{ij} Π_{k≠i,j}c_k.

It must vanish by original b_j-multiaffinity. These are distinct monomials
in the independent outside c's, so l_{ij}=0 for i≠j. Finally normalization
gives F_0(a,s1)=0. In (12), setting s=0 first forces A=0; then taking s=1
and varying the independent c's forces every l_{ii}=0. Thus F_0=0.

Injectivity of (1) now gives L=Σ r_{ij}(T_(ij)−I), proving necessity.

**Proof of sufficiency.** For one transposition T and r≥0,

    exp(tr(T−I))=[(1+exp(−2rt))/2] I
                   +[(1−exp(−2rt))/2] T.

Partial symmetrization preserves stability, so this is a normalized Grace
operator. The Lie–Trotter formula, composition closure of G_n, and closedness
of normalized stable symbols imply exp(tΣ r_{ij}(T_(ij)−I))∈G_n. Thus every
direction in (9) is realized by a differentiable path. ∎

### 5.1 Divisibility consequence and its precise limitation

Suppose K(t,s) is a continuously differentiable evolution family, K(s,s)=I,
K(t,s)∈G_n for t≥s, and K(t,r)K(r,s)=K(t,s). The instantaneous generators
therefore have the form

    L_t=Σ_{i<j}r_{ij}(t)(T_(ij)−I),    r_{ij}(t)≥0.

Time-ordered products of the elementary lazy swaps are convex mixtures of
permutations, and the convex permutation hull is closed. Hence every K(t,s)
has a common permutation law. The autonomous special case classifies all
continuous semigroups contained in G_n.

A continuous path t↦R(U_t) of actual unitary kernels need not be divisible
inside G_n: its local inverse propagators need not preserve stability.
Therefore this theorem does not put every actual kernel in the permutation
hull, and it does not imply that G_n is disconnected. Instead it identifies
a precise obstruction to completing MOC solely by integrating local
transposition-preserving directions.

## 6. Ordinary partial trace preserves the Grace class

Let Tr_i be ordinary partial trace over the i-th C² tensor factor. Then

    Q_{Tr_i R}=(∂_{a_i}+∂_{b_i})Q_R |_{a_i=b_i=0}.             (13)

Indeed, the two trace summands are the Boolean entries with i absent from
both I,J and with i present in both. In (1), the former entries multiply a_i
and the latter multiply b_i; terms with only one of I,J containing i do not
contribute to the partial trace.

**Proposition 6.1.** If R∈G_n, let τ=1+R[{i},{i}]. Then 1≤τ≤2 and

    τ^{−1} Tr_i R ∈ G_{n−1}.                                 (14)

**Proof.** Partial trace of an operator commuting with g^{⊗n} commutes with
g^{⊗(n−1)}. Its scalar on the symmetric representation equals its weight-zero
entry, namely τ. That scalar is positive by Proposition 2.1. To verify
stability of (13), first identify a_i=b_i=t. The resulting polynomial in t
and the remaining variables is stable. Differentiate in t, then specialize
t=0. Derivatives and real boundary specialization preserve stability or give
zero; the positive normalization τ rules out the zero polynomial. Equation
(13) is the resulting symbol. ∎

This trace theorem uses no actual-unitary realization assumption.

## 7. Actual partial trace is exactly a two-unitary mixture

Relabel the deleted site first and partition an actual unitary as

    U=[ α  r ],    α∈C, r∈C^{1×(n−1)}, c∈C^{(n−1)×1}.
      [ c  D ]

Assume initially |α|<1 and define the unitary transfer family

    V_z=D+ z c r/(1−zα),    |z|=1.                            (15)

**Unitary verification.** Given x∈C^{n−1}, choose
a=zrx/(1−zα). Then the first component of U(a,x) is a/z and the second is
V_zx. Conservation of norm by U and |z|=1 gives
|a|²+||x||²=|a/z|²+||V_zx||², hence ||V_zx||=||x||. The square matrix V_z is
therefore unitary.

For equal-sized I,J in the remaining sites, put

    d=det D[I,J],
    e=det U[{i}∪I,{i}∪J],

using the same ordering with i first in both row and column sets. The bordered
determinant formula gives e=αd−r_J adj(D[I,J])c_I. The rank-one determinant
formula, valid also for singular D[I,J] by polynomial continuation, gives

    det V_z[I,J]=(d−z e)/(1−zα).                              (16)

Let τ=1+|α|². At z=1 and z=−1, equation (16) and
(|d−e|²+|d+e|²)/2=|d|²+|e|² yield the exact operator identity

    (Tr_i R(U))/τ
      = |1−α|²/(2τ) R(D+c r/(1−α))
         + |1+α|²/(2τ) R(D−c r/(1+α)).                        (17)

Both coefficients are nonnegative and sum to one. If |α|=1, unitarity forces
r=c=0, and the normalized partial trace is simply R(D); this handles all
boundary cases including vanishing denominators by direct decoupling.

For mixtures R=Σ p_l R(U_l), the trace normalization is τ=Σ p_l τ_l and the
new mixture weights become p_l τ_l/τ. Thus A_n is closed under normalized
ordinary partial trace, with an explicit two-term realization for each
actual constituent. Equations (5), (17), and block-sum tensor closure together
give a concrete convex monoidal structure with a dimension-lowering trace.

## 8. Scope of ordinary trace closure

### Rank-one local effects require additional data

For a two-site swap S and any 2×2 matrix K,

    Tr_2[(I⊗K)S]=K.                                          (19)

Take K=diag(1,0), a Hermitian rank-one projector. The result has rank one,
whereas every normalized one-site permutation/Grace operator is I. No scalar
renormalization turns (19) into a member of G_1 or A_1. Unequal positive
diagonal K gives the same obstruction unless K is scalar.

Thus (17) is an ordinary-trace theorem, not a theorem for the rank-one
postselection used in MOC. A prospective induction must retain the new local
effect or the cycles through the deleted site. It cannot discard that data
and apply smaller-dimensional MOC to a normalized Grace kernel without an
additional argument. The transfer family (15) is the concrete structure
available for that next argument.

## 9. A spectral bracket bound for the coherent two-site defect

Let G be a two-site unitary mixing sites i,j, let t=|G_{ij}|², and write
S=T_(ij). Then R(G)=(1−t)I+tS and

    I−R(G)²=2t(1−t)(I−S).                                   (20)

The exterior-compression Cauchy–Schwarz estimate from
categorical_exterior_order.md gives, for arbitrary vectors u,v,

    |v* [R(GU)−R(G)R(U)] u|²
      ≤(v*(I−R(G)²)v)(||u||²−||R(U)u||²).

If v=⊗v_k is a product vector, the first factor is explicitly

    2t(1−t) |det[v_i,v_j]|² Π_{k≠i,j}||v_k||².               (21)

Indeed v*(I−S)v is the two-vector Gram determinant times the squared norms
of the other factors, and the Gram determinant in C² is the squared modulus
of the ordinary determinant. For spectral output covectors w_k=(1,a_k),
take v_k=conjugate(w_k)^T. The coherent error therefore obeys

    |w[R(GU)−R(G)R(U)]u|
      ≤sqrt(2t(1−t)) |a_i−a_j|
         [Π_{k≠i,j}(1+|a_k|²)]^{1/2}
         (||u||²−||R(U)u||²)^{1/2}.                          (22)

This supplies a geometric spectral factor: coherence across a gate vanishes
when the corresponding output projective lines coincide, and is controlled
by their determinant bracket in general. It is a proved quantitative estimate,
but a universal matching-vertex support margin large enough to absorb its
right side is not proved. That support budget remains the substantive
inequality rather than an automatic consequence of compression.

## Scope

The algebraic proofs and exact phase designs above do not establish the unresolved inclusions or unrestricted scalar MOC.

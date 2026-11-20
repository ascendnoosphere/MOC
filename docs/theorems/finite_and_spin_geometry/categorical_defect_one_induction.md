# Rank-one deletion, partial permutations, and the exact transfer-disk obligation

This note proves rank-one deletion and transfer identities, the two-by-two contraction law, and an aligned-defect scalar induction class. The unrestricted scalar target remains unproved.

## 1. The object obtained by an actual rank-one deletion

For an m×m contraction D, define the graded Boolean kernel

    K(D)[I,J]=|det D[I,J]|²,    |I|=|J|,                       (1)

with empty minor one. Its symbol is

    Q_D(a,b)=Σ_{|I|=|J|} a_{I^c} b_J |det D[I,J]|²
            =det(D_a+D D_b D*).                              (2)

Every block is nonnegative and substochastic, since the corresponding
exterior power of D is a contraction. The symbol is real stable: when every
a_i and b_j has positive imaginary part, the imaginary part of the matrix
in (2) is positive definite. However K(D) need not commute with global GL2;
its top and bottom blocks are |detD|² and one.

Now partition an (m+1)-dimensional unitary as

    U=[α r; c D].

Contraction of its first qubit against E00=diag(1,0) gives K(D), because
only compound entries with the deleted site absent from both index sets
remain. This operation is different from ordinary partial trace, which
adds the entries with the site present in both sets.

Conversely every D with rank(I−D*D)≤1 has such a unitary completion. Write

    D=D0+z x y*,    |z|≤1,                                   (3)

where x,y are unit vectors, D0 maps y-perp unitarily onto x-perp, D0y=0,
and D0*x=0. Then

    U(z)=[ −conjugate(z)    sqrt(1−|z|²)y* ]
         [ sqrt(1−|z|²)x       D0+zxy*      ]                 (4)

is unitary by direct block multiplication. A general defect-one D has (3)
by singular-value decomposition; the unitary case follows by decoupling.

## 2. The comparison vertices retain the cycle through the removed label

For a permutation π of {0,1,...,m}, contracting T_π at label 0 against E00
has two possibilities. If π fixes 0, the result is a permutation operator
on the remaining labels. Otherwise delete 0 from its cycle; the result is
that smaller permutation with one E00 inserted on the cut edge. The count
is m! ordinary permutations and m·m! decorated permutations, totaling
(m+1)! as required.

Use product input u_i=(1,b_i)^T and output covector w_i=(a_i,1). An ordinary
vertex is

    Z_σ=Π_i(a_i+b_{σ(i)}),

whereas insertion on row j gives

    Z_{σ,j}=a_j Π_{i≠j}(a_i+b_{σ(i)}).                        (5)

The removed row consumes the column σ(j); the removed column forces the
remaining row j onto E00. Thus the b_{σ(j)} term disappears, but a_j remains.
The exact scalar induction target is

    det(D_a+D D_b D*) ∈ conv_R{Z_σ,Z_{σ,j}}
    whenever rank(I−D*D)≤1.                                 (6)

**Equivalence.** Assertion (6) for all m×m defect-one contractions is
equivalent to MOC in dimension m+1. One direction uses the completion (4)
and product tests. For the reverse, start with generic rank-two matching
data in dimension m+1 and normalize one local overlap to one. A common
GL2 conjugation sends its idempotent to E00. The remaining input spinors
and output covectors can be rescaled into (1,b_i) and (a_i,1); these rescalings
multiply the determinant value and every vertex by the same nonzero scalar.
The resulting scalar is (2), and the vertices are exactly (5). Vanishing
overlaps and unavailable affine charts follow by continuity.

Consequently (6) is not merely a leading-coefficient boundary of MOC. It
retains the entire generic problem through a projective gauge.

## 3. A defect-counted category of partial permutations

A partial permutation matrix M has at most one entry one in every row and
column, with its other entries zero. Its symbol is

    Q_M(a,b)=Π_{unmatched rows i} a_i
              Π_{matched edges (i,j)}(a_i+b_j).              (7)

K(M) is an ordinary tensor permutation followed by E00 on each unmatched
input leg. These kernels form the usual partial-permutation composition
system: a composition remains a partial permutation, and the numbers of
missing matched edges add at most.

More generally a contraction with defect rank

    r=rank(I−D*D)

has a unitary completion in dimension m+r. Contracting the r added qubits
against E00 gives K(D). A full permutation then induces a partial matching
of the remaining labels with at least m−r edges. Conversely every such
partial matching extends to a permutation using r auxiliary labels.
This is an exact construction of the enlarged vertex category, without
asserting that arbitrary actual kernels have a common positive law in it.

The phase-composition identity remains valid for arbitrary contractions:

    K(D)K(E)=2^{−(m−1)}Σ_{ε_1=1, ε_j=±1}K(D D_ε E).          (8)

Its proof is the same equal-cardinality character orthogonality as in the
unitary case. The product defect obeys

    rank(I−DE E*D*)
      ≤rank(I−DD*)+rank(I−EE*),                               (9)

because I−DE E*D*=(I−DD*)+D(I−EE*)D* is a sum of positive semidefinite
matrices. Block sums give tensor products and add defect counts. These
are genuine categorical closure statements, but pointwise composition
K(DE)=K(D)K(E) is still false in general.

## 4. The transfer-circle Fourier data

For U=[α r;c D], |α|<1, let

    V_ζ=D+ζcr/(1−ζα),    |ζ|=1.

The unitary feedback proof and minor formula from the preceding batch give

    det V_ζ[I,J]=(d_{IJ}−ζe_{IJ})/(1−ζα),                    (10)

where d_{IJ}=detD[I,J] and e_{IJ} is the minor of U bordered by the removed
site. Define four complex scalar quantities using the same spectral cost
t_{IJ}=a_{I^c}b_J:

    F0=Σ t_{IJ}|d_{IJ}|²,    F1=Σ t_{IJ}|e_{IJ}|²,
    H =Σ t_{IJ}e_{IJ}conjugate(d_{IJ}),
    H'=Σ t_{IJ}d_{IJ}conjugate(e_{IJ}).

H' need not equal conjugate(H), since the costs are complex. Equation (10)
gives the exact weighted boundary identity

    |1−ζα|² det(D_a+V_ζD_bV_ζ*)
        =F0+F1−ζH−conjugate(ζ)H'.                            (11)

Thus weighted zeroth and first Fourier moments recover the ordinary-trace
sum F0+F1 and the two coherent cross terms. They do not linearly recover F0
alone from arbitrary scalar data.

Unweighted Haar averaging gives a useful leakage formula:

    ∫ det(D_a+V_ζD_bV_ζ*) dζ = F0+G,
    G=Σ t_{IJ}|e_{IJ}−αd_{IJ}|²/(1−|α|²).                    (12)

Indeed the Poisson integrals of 1,ζ,conjugate(ζ) against
|1−ζα|^{-2} are respectively 1,conjugate(α),α divided by 1−|α|².
The numerator of the correction is
|e|²−conjugate(α)e conjugate(d)−αd conjugate(e)+|α|²|d|².
Although its coefficient array is nonnegative, G is not nonnegative after
an arbitrary complex scalar support functional. The missing sign is a
spectral budget issue, not an algebraic omission from the trace identity.

## 5. The radial coefficient is a reciprocal center

Use the singular-value disk (3), now with variable z. Each compound minor
is affine in z:

    det(D0+zxy*)[I,J]=c_{IJ}+z d_{IJ}.

Therefore the determinant has the exact form

    F(z)=C+Hz+H'conjugate(z)+L|z|².                          (13)

The quadratic coefficient has an intrinsic formula:

    C=det(D_a+D0D_bD0*),
    L=det(D_b+D0*D_aD0).                                    (14)

To prove the second identity, note that V_z=D0+zxy* is unitary on the
circle and detV_z=zδ, |δ|=1. Complementary unitary minors imply
|d_{IJ}|²=|c_{I^c,J^c}|² after comparing coefficients in z. Reindexing the
symbol gives precisely the determinant with a,b swapped and D0 adjointed.

Equivalently complete x and y to orthonormal bases and write the two normal
matrices in block form

    A'=[A11 A12; A21 A22],    B'=[B11 B12; B21 B22].

With H0=A11+B11, the block determinant yields

    C=A22 detH0−A21 adj(H0) A12,
    H=−B21 adj(H0) A12,
    H'=−A21 adj(H0) B12,
    L=B22 detH0−B21 adj(H0) B12.                             (15)

These are polynomial identities, so invertibility of H0 is unnecessary.
The decorated dual-center vertices obtained by swapping a,b are the differences

    Z_σ−Z_{σ,j}=b_{σ(j)}Π_{i≠j}(a_i+b_{σ(i)}).

The ordinary dual-center vertices remain Z_σ. Rank deficiency alone does
not let a scalar hull argument delete those ordinary vertices; forcing their
weights to zero uses a common coefficient law, which is precisely the stronger
statement refuted below. This identifies the appropriate leakage budget, but separate center hull
laws would not automatically couple C,L,H,H' with one common assignment.

## 6. A complete common law for every two-by-two contraction

**Theorem.** Every 2×2 contraction D has a spectrum-independent common
compound law on all seven partial permutation matrices.

Put p_{ij}=|D_{ij}|² and t=|detD|². Choose any

    max(0,t−p12,t−p21) ≤ x ≤ min(t,p11,p22).                  (16)

Give the full identity matching weight x, the full swap weight t−x, the
four single-edge matchings weights

    p11−x,    p22−x,    p12−t+x,    p21−t+x,

and the empty matching weight

    1−Σ p_{ij}+t=det(I−D*D).                                (17)

All weights are nonnegative and sum to one. To prove that (16) is nonempty,
let the squared singular values be λ1,λ2∈[0,1]. Every squared row norm and
squared column norm is at least min(λ1,λ2), which is at least λ1λ2=t.
These four inequalities are exactly the nontrivial comparisons between
the proposed lower and upper endpoints in (16). Equation (17) equals
(1−λ1)(1−λ2)≥0.

The singleton entries of the mixture are p, its sole second-compound entry
is x+(t−x)=t, and its empty entry is one. Thus it reproduces every compound
entry and proves the polynomial identity for arbitrary complex a,b.

For defect rank one, one λ equals one, so the empty-matching weight is zero.
The six remaining vertices are exactly (5), proving the defect-one induction
target at m=2. This proof is elementary and does not rely on a generic
continuation or a semigroup factorization.

## 7. An aligned-defect scalar induction in every dimension

Suppose MOC is known in dimension m. Then (6) follows whenever the defect
projection commutes with either D_b on the input side or D_a on the output
side.

For the input version write D=Q S, where S=(D*D)^{1/2} and Q is unitary
(extend the polar partial isometry if needed). If S commutes with D_b,
choose the defect vector within one eigenspace of D_b. Then S D_b S is
normal, and its spectrum is obtained by replacing one b_j by s²b_j,
0≤s≤1. Smaller-dimensional MOC gives a convex combination of products
in which that one factor has changed. Each such product is exactly
s²Z_σ+(1−s²)Z_{σ,i}, where σ(i)=j, proving (6).

For the output version write D=S Q with S=(DD*)^{1/2} commuting with D_a.
When s>0, congruence gives

    det(D_a+S QD_bQ*S)=s²det(S^{-1}D_aS^{-1}+QD_bQ*).

The changed a_i is a_i/s², and multiplication by s² again gives
s²Z_σ+(1−s²)Z_{σ,i}. The case s=0 follows by continuity. This includes
defect vectors aligned with a coordinate label and with a repeated spectral
eigenspace. It is a proved induction class, not the general defect-one step.

## 10. The exact two-by-two positive certificate still required

For a fixed complex support direction η, write the real part of (13) as

    f(z)=c+2Re(bz)+q|z|²,
    c=Re(ηC), q=Re(ηL),
    b=[ηH+conjugate(ηH')]/2.

Let h=max_σ,j Re(ηZ_σ),Re(ηZ_{σ,j}). The inequality f(z)≤h on the unit
disk is equivalent to the existence of λ≥0 such that

    [ h−c−λ     −b      ] >= 0.                             (22)
    [ −conjugate(b)  λ−q ]

Sufficiency follows from
h−f(z)=(1,z)*Q(1,z)+λ(1−|z|²). For necessity one can maximize the radial
quadratic directly. If q≥0, its maximum is c+q+2|b| on the circle. If q<0
and |b|>−q, the maximum is again on the circle. If q<0 and |b|≤−q, the
maximum is c+|b|²/(−q), and (22) holds with λ=0 exactly when

    |b|²≤(h−c)(−q).                                        (23)

In the boundary-maximum cases choose λ=q+|b| when positive; the same
two-by-two check gives (22). Zero and degenerate cases follow directly or
by continuity. Thus (22) is a complete small positive-matrix certificate
for each actual transfer disk. What remains unproved is that the actual
spectral coefficients and the enlarged matching budget always supply it.
Neither a scalar maximum principle nor a spectrum-independent center law is assumed in this equivalence; the universal spectral budget remains unproved.
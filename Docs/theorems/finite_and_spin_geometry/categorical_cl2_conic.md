# Affine Pauli planes, a Cl₂ trace formula, and a proved triangular slice of MOC

This note treats the affine-plane restriction suggested by the holomorphic
face-reduction track. It gives structural reductions valid in every dimension
and proves one degenerate slice completely. It does not prove the generic
conic or isospectral scalar MOC problem.

## 1. Product idempotents and permutation-cycle values

Let P_i=u_i w_i be complex rank-one trace-one idempotents on C², so
w_i(u_i)=1. For the tensor convention in categorical_exterior_order.md, the
quantity

    Z_π=tr[(⊗_i P_i)T_π]

is the product, over permutation cycles, of traces of ordered products of
the P_i along the corresponding cycle (possibly reversed according to the
chosen cycle notation). Equivalently

    Z_π=Π_i w_i(u_{π(i)}).

The exact MOC reformulation is

    tr[(⊗_i P_i)R(U)]∈conv_R{Z_π:π∈S_n}.                     (1)

It is invariant under simultaneous conjugation P_i↦gP_i g^{-1}, since both
R(U) and tensor permutations commute with g^{⊗n}.

Write Q_i=2P_i−I. Then tr Q_i=0 and Q_i²=I. Under a Pauli identification,
Q_i=ν_i·σ and ν_i·ν_i=1 for the complex bilinear form, with no conjugation.
An affine plane condition on the ν_i is equivalently

    tr(A P_i)=constant                                      (2)

for one nonzero traceless matrix A. Classifying A under conjugation gives
the two normal forms below. This is an elementary 2×2 matrix calculation;
no categorical order conclusion is assumed from the Clifford notation.

## 2. Nonisotropic plane: constant diagonal idempotents

If det A≠0, A has two distinct eigenvalues and can be diagonalized. Equation
(2) then says that all P_i have the same upper-left entry p. On the generic
chart p(1−p)≠0, the rank-one relation gives

    P_i = [ p       (1−p)x_i ],    x_i≠0.
          [ p/x_i   1−p       ]                             (3)

Choose u_i=(x_i,1)^T and w_i=(p/x_i,1−p). Their overlap matrix is

    C_ij=w_i(u_j)=(1−p)+p x_j/x_i.                           (4)

Multiplying row i by x_i/p changes every permutation product and the
determinant ratio by one common scalar and gives the additive rank-two
matrix

    C'_ij=((1−p)/p)x_i+x_j.                                  (5)

Thus the generic affine-plane problem is a proportional paired-spectra
problem a_i=κx_i, b_i=x_i, with κ=(1−p)/p. It is still an all-n complex
problem. The cases p=0 or 1 are limits of (3), including configurations on
both branches of the degenerate idempotent conic; they should not all be
silently declared simultaneously triangular.

The natural projective action here acts on the two line coordinates b and
−a by the same Möbius transformation. Statements about conjugacy of the
paired Möbius relation must use this sign convention. In particular the
classification is not obtained by freely reordering a and b without also
changing the unitary basis data.

## 3. The isospectral plane has a common symmetric bilinear form

At p=1/2, corresponding to a_i=b_i=x_i in (5), let

    H=[0 1],    u_i=(x_i,1)^T.
      [1 0]

Then

    P_i=u_i u_i^T H/(u_i^T H u_i),    u_i^T H u_i=2x_i,
    P_i^T H=H P_i.                                         (6)

All P_i are therefore selfadjoint for the same nondegenerate complex
symmetric bilinear form. The form is not a positive Hermitian form, and
ordinary spectral or Hilbert-space positivity does not follow.

For any ordered cycle i_1,...,i_k, taking the transpose of the product and
using (6) yields

    tr(P_{i_1}...P_{i_k})=tr(P_{i_k}...P_{i_1}).               (7)

Consequently the cycle values lose orientation in this central plane. This
is a genuine reduction of the complex trace algebra, but it does not make
the permutation values real or positive.

## 4. An explicit all-n Cl₂ trace expansion

For the same p=1/2 case,

    Q_i=2P_i−I=[ 0       x_i ],    Q_i²=I.
                 [ x_i^{-1} 0 ]

Every odd-length product of the Q_i is off diagonal, so its trace is zero.
An even-length ordered product is diagonal, and direct multiplication gives

    tr(Q_{i_1}...Q_{i_{2m}})=r+r^{-1},
    r=(x_{i_1}x_{i_3}...x_{i_{2m−1}})
         /(x_{i_2}x_{i_4}...x_{i_{2m}}).                    (8)

Expanding P_i=(I+Q_i)/2 yields, for a cycle of length k,

    tr(P_{i_1}...P_{i_k})
       =2^{-k} [2+Σ_{∅≠S⊆[k], |S| even}(r_S+r_S^{-1})],     (9)

where the indices in S retain their order in the cycle, and r_S alternates
between numerator and denominator in that order. Equation (9) is valid for
every cycle length. It provides a Laurent-monomial form of the complete
Cl₂ cycle trace with the odd/chiral contributions removed.

For example, for k=2 it gives

    tr(P_iP_j)=(2+x_i/x_j+x_j/x_i)/4.

The coefficients in (9) are positive rational numbers, but its complex
Laurent monomials have arbitrary phases. Therefore the formula alone does
not produce positive coefficients expressing the complete determinant value
as a convex combination of the original permutation products. A positive scalar support certificate is not established by this formula alone.

## 5. Isotropic plane: constant lower-left entry

If A≠0 but det A=0, A is nilpotent and can be conjugated to E_{12}.
Equation (2) then means that each P_i has the same lower-left entry r:

    P_i=[p_i  q_i  ],    q_i r=p_i(1−p_i).
        [r    1−p_i]

When r≠0, choose u_i=(p_i/r,1)^T and w_i=(r,1−p_i). Then

    w_i(u_j)=1−p_i+p_j.                                     (10)

Thus this plane gives paired spectra with a_i=1−p_i, b_i=p_i, and a_i+b_i=1.
Common scalings allow any nonzero constant paired sum. In the natural line
coordinates b and −a, the pairing is a translation, explaining its
parabolic character. The scalar hull problem for arbitrary complex p_i
remains unproved here.

## 6. The zero-constant triangular case satisfies MOC in every dimension

If r=0, every P_i is upper triangular. The idempotent equations force its
diagonal to be (ε_i,1−ε_i), with ε_i∈{0,1}. The upper-right entries are
arbitrary. Let A={i:ε_i=1} and B=A^c.

**Theorem 6.1.** For every unitary U and every simultaneously triangular
collection of complex rank-one trace-one idempotents,

    tr[(⊗_i P_i)R(U)]=|det U[A,A]|².                         (11)

The permutation-cycle values are exactly 1 for permutations preserving A
and B, and 0 for permutations having a cycle meeting both classes.
Consequently (1) holds.

**Proof.** The product of upper triangular matrices is upper triangular,
and the two diagonal entries of P_{i_1}...P_{i_k} are respectively
Π_l ε_{i_l} and Π_l(1−ε_{i_l}). Its trace is one if the cycle is homogeneous
in ε and zero otherwise. Hence Z_π is the indicator that π preserves A.
Substitute this indicator in the exact permutation expression

    tr[(⊗P_i)R(U)]
       =(det U)^{-1} Σ_π sgn(π)(Π_i U_{i,π(i)})Z_π.

The restricted determinant sum factorizes to
det U[A,A] det U[B,B]/det U. Complementary principal minors of a unitary
matrix satisfy det U[B,B]=det U overline(det U[A,A]), proving (11).
If A or B is empty, all vertices and the target are one. Otherwise both
zero and one occur among the vertices, and the squared modulus in (11)
belongs to [0,1]. This proves the hull assertion in all cases. ∎

The conclusion is invariant under simultaneous conjugation, so the theorem
covers every collection sharing an invariant line, regardless of whether
that line is orthogonal in the original coordinates.

## 7. What the conic reduction achieves and leaves open

The affine-plane restriction splits into a generic proportional-pair family,
a constant-paired-sum family, and a fully proved triangular degeneration.
The central isospectral family has the concrete bilinear selfadjointness
and trace expansion (6)–(9). These are algebraic simplifications of the
actual spectral tests; they do not replace them with arbitrary linear
functionals on the operator algebra. The remaining task is a positive
scalar support certificate for the generic conic families, compatible with
these complex bilinear tests. No such certificate is established in this
note.

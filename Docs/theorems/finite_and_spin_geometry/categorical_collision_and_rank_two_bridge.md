## 1. Every repeated-spectrum case in dimension four holds in the Boolean relaxation

Let B_4 be the class of nonnegative graded Boolean operators whose cardinality
blocks are doubly stochastic and which commute with global GL2. For any
R∈B_4 and product input u=⊗u_i, the stronger vector assertion

    Ru ∈ conv_R{T_πu}

holds when any two of the four input factors are proportional. This is the
all-but-two-exceptional-lines theorem proved in categorical_exterior_order.md:
gauge the common line to e0, reproduce the two exceptional singleton columns
and their pair column by an oriented-edge law, and use positivity of higher
Boolean levels for every max-flow cut.

In particular, for u_i=(1,b_i)^T, a repeated b value is enough. Applying the
same theorem to R^T and the product vector of output covectors proves the
scalar hull assertion whenever any two a values coincide as well. R^T has
the same required positivity and equivariance properties. Pairing the
vector law with the arbitrary opposite product tensor gives

    d_R(a,b)∈conv_R{Π_i(a_i+b_{π(i)})}.                       (1)

The result includes proportional projective factors at infinity, by the
homogeneous formulation or limits. It applies to every repeated pair on
either side, with the other spectrum completely arbitrary. It is not
restricted to both spectra having a repeated value simultaneously.

## 2. Six explicit collision laws

Define R_bad on the Boolean subset basis of (C²)^{⊗4}, with entries between different cardinalities zero. Order subsets by increasing integer mask (site i has bit 2^{i−1}); thus the singleton order is 1,2,3,4, the pair order is 12,13,23,14,24,34, and the triple order is 123,124,134,234. Its cardinality blocks are

    R_0=R_4=[1],

    R_1=(1/3)[ 0 1 1 1;
                1 1 1 0;
                1 1 0 1;
                1 0 1 1 ],

    R_2=(1/3)[ 1 0 1 0 0 1;
                0 0 1 1 1 0;
                1 1 0 0 1 0;
                0 1 0 0 1 1;
                0 1 1 1 0 0;
                1 0 0 1 0 1 ],

    R_3=(1/3)[ 1 1 0 1;
                1 0 1 1;
                0 1 1 1;
                1 1 1 0 ].

It is symmetric. For each repeated input pair below, the average of the three listed permutations agrees with
R_bad on every product tensor satisfying that collision. Permutations are
written in one-line notation with the convention T_πu having factor
u_{π(i)} at output position i. Every weight is exactly 1/3.

| Repeated input positions | Three permutation operators |
|---|---|
| 1,2 | 4312; 3124; 1243 |
| 1,3 | 4123; 2134; 1243 |
| 1,4 | 2314; 3124; 1243 |
| 2,3 | 4213; 2134; 2341 |
| 2,4 | 3241; 2314; 2143 |
| 3,4 | 2134; 3214; 3421 |

These formulas are identities on the whole twelve-dimensional subspace
Sym²(C²) on the repeated pair, tensored with the two remaining C² factors.
The exact script verifies 192 matrix coefficients for each row of the table,
covering all twelve spanning inputs and sixteen outputs. This checks all
spectral values at once, rather than finitely many sample values. For output
collisions use the inverse permutations, by transposing the identities.

The table can also be derived directly: for exceptional input sites a,b,
orient the three nonzero edges of the R_bad pair column, each of mass 1/3,
to reproduce the singleton column for a. The complementary endpoint
marginal is then the singleton column for b. Completing the two exceptional
placements arbitrarily on the common factors gives the listed permutations.


## 4. An explicit orthogonal matrix with a common permutation law

Consider the exact rational orthogonal matrix

    U=(1/882259)
      [ 862328   12753   10842 −185718;
          5499  460784 −752232   13260;
       −135564  566670  336062 −570921;
        127920  494754  315393  646346 ].

The complete Boolean kernel satisfies

    R(U)=Σ_{π in S} λ_π T_π,    λ_π>0,    Σλ_π=1,             (3)

for the fourteen permutations and exact positive weights displayed below and checked by code/theorems/finite_and_spin_geometry/categorical_third_batch_exact.py. The smallest weight is

    2313441/778380943081,

and 778380943081=882259². The exact script solves the fourteen-weight
linear system over the rationals and verifies every one of the seventy
Boolean entries, including both complementary exterior levels.

For a directly inspectable version of (3), all weights share denominator
882259²; their numerators are:

| Permutation | Weight numerator |
|---|---:|
| 1234 | 108698715373 |
| 1243 | 94062436416 |
| 1324 | 308786561811 |
| 1342 | 231886038384 |
| 1432 | 175827600 |
| 2134 | 4435236 |
| 2314 | 158203773 |
| 3142 | 2313441 |
| 3214 | 115235523 |
| 4123 | 23490324 |
| 4213 | 5386817709 |
| 4231 | 4058689635 |
| 4312 | 12717341091 |
| 4321 | 12304836765 |

Hence this matrix already lies in the convex permutation hull at the
kernel level. In particular it lies in the convex hull of kernels admitting
a rank-two update after spectral relabeling, because permutation kernels
are allowed relabelings of the rank-zero identity update.

The distinction is essential: a positive kernel representation forgets
phase information and can mix several genuinely different relative
unitaries. No rank(U−M) conclusion follows from (3).

## 5. A focused unproved bridge and its exact algebraic form

A potentially sufficient bridge for dimension four is the disjunction

    for every O∈SO(4), either R(O)∈conv{T_π},
    or rank(O−M)≤2 for some monomial unitary M.               (4)

A proof of (4) would imply the desired convex rank-two reduction on real
orthogonal kernels. Combining it with the previously proved U4-to-conv(SO4)
kernel reduction would give the corresponding reduction for all actual
complex U4 kernels. It would still require the scalar rank-two MOC theorem
to finish MOC itself.

The root track's exact common-kernel facet work identifies forty-eight
nontrivial facets as one left-right permutation orbit of

    f(R)=R[3,3]+R[2,4]+R[12,13]−R[13,23]≥0.                 (5)

For actual kernels the remaining entry-positivity facets hold automatically.
Thus a concrete route to (4) is

    f(R(O))<0  ==>  some phase-completion discriminant Δ_π≥0, (6)

with regular charts or a limiting argument handling degeneracies. The
with regular charts or a limiting argument handling degeneracies. The
phase-completion discriminants are defined in
`categorical_global_completion_criterion.md`. For real O, the quartic

    Δ_π=−(q0+q1+q2+q12)(q0+q1−q2−q12)
           (q0−q1+q2−q12)(q0−q1−q2+q12).                   (7)

This expresses each torus-completion condition through four real feedback
sign values. It does not prove that the common-law facet forces their
product to be nonpositive.


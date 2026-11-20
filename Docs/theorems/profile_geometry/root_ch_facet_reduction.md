# An exact facet reduction for the four-dimensional coefficient hull

This is a reduction of the remaining universal assertion, not a proof of MOC.

## 1. The coefficient hull

Fix four complex numbers beta_j. For each permutation pi define

    v_pi = (beta_pi(1) (1 + beta_pi(2)) beta_pi(4),
            beta_pi(1) (1 + beta_pi(2))) in C^2 = R^4.

Let P_beta be their real convex hull. If C = U diag(beta) U*, define

    D(U) = (det C[124] + det C[14], C_11 + det C[12]).

The coefficient-hull assertion is D(U) in P_beta for every beta and U. The
normalization and limiting identities in PRIOR_REPORT.md prove that this is
equivalent to MOC in dimension four. The equivalence also holds with U fixed
and with all spectra quantified: common Mobius transformations change the
spectra and multiply every matching product and the determinant by the same
scalar, while preserving U.

For example beta = (0, 1, i, 2) has full affine dimension four. In coordinates
(1, Re v_0, Im v_0, Re v_1, Im v_1), the permutations
1234, 2134, 2143, 2314, 2341 give the exact rank-five rows

    (1,0,0,0,0), (1,2,0,1,0), (1,0,1,1,0),
    (1,2,2,1,1), (1,0,0,1,1).

Thus the exceptional beta for which affine dimension drops form a proper
real algebraic subset. They follow by continuity after the full-dimensional
case is established.

## 2. Facets are a complete set of support obligations

Suppose P_beta has affine dimension four. Its cone of nonnegative affine
functions is

    K_beta = {(h, lambda): h - lambda(v_pi) >= 0 for every pi},

where lambda is a real linear functional on C^2. This cone is pointed: if
both g and -g are nonnegative on P_beta, g vanishes on an affine spanning
set and hence is the zero affine function. It is full dimensional, since
the constant function 1 satisfies every defining inequality strictly.

An extreme ray of this five-dimensional cone has active equations of rank
four. Its zero vertices therefore have affine span of dimension three.
They form a facet of P_beta. Conversely a nonnegative affine function that
vanishes on a facet is unique up to a positive factor, and hence spans an
extreme ray. The polyhedral cone is the nonnegative span of these rays.

Consequently, to prove D(U) in P_beta, it suffices to prove

    h_f - lambda_f(D(U)) >= 0

for the actual facets f. Every other nonnegative affine support deficit is
a nonnegative linear combination of these facet deficits. In particular,
each necessary facet obligation has at least four affinely independent
matching vertices tied at its support value. Checking only two-contact
facets of one planar projection discards this additional structure.

This argument is valid separately for every U and every beta. A theorem on
all actual facets would therefore prove the full coefficient-hull assertion.
It does not follow from certificates for a finite sample of beta.

## 3. The quaternion capacity also reduces to these facets

For the isoclinic quaternion family, a support deficit has the form

    F_delta(q) = sum_i d_i q_i^4
                 + sum_{i<j} e_ij q_i^2 q_j^2
                 - R q_0 q_1 q_2 q_3,

with d_i and e_ij nonnegative linear functions of the 24 vertex gaps delta,
and R a real linear function of the same cost. Its nonnegativity for all
real q is equivalent to

    |R| <= cap(d,e),

where

    cap(d,e) = inf_{x_i>0, product_i x_i=1}
                   (sum_i d_i x_i^2 + sum_{i<j} e_ij x_i x_j).

Capacity is positively homogeneous and superadditive, because it is the
infimum of linear functions of the coefficient vector:

    cap(c + c') >= cap(c) + cap(c').

If a gap vector is delta = sum_f t_f delta_f with t_f >= 0, the triangle
inequality and superadditivity give

    |R(delta)| <= sum_f t_f |R(delta_f)|
               <= sum_f t_f cap(delta_f)
               <= cap(delta).

Therefore proving the capacity bound for every actual coefficient-hull
facet is sufficient for the entire isoclinic quaternion family.

The simpler sufficient expression

    B(d,e) = 4 (d_0 d_1 d_2 d_3)^(1/4)
             + 2 (sqrt(e_01 e_23) + sqrt(e_02 e_13)
                  + sqrt(e_03 e_12))

has the same positive homogeneity and superadditivity. For each geometric
mean term, superadditivity follows from Holder's inequality; the pair terms
are the two-variable instance. Thus |R| <= B also reduces to actual facets.

The quartic expansion for coefficient-hull costs follows either by taking
the normalized spectral limit in the exact determinant expansion, or by
linearity from the matching coordinates. A support functional with first
complex coefficient zero follows by continuity from nonzero coefficients.

## 4. What a successful meta-proof must still provide

The reduction is exact, but the facet gaps still depend on continuous
complex spectral data. The missing theorem is an inequality or a finite
exhaustive classification that uses both their four-contact geometry and
their spectral realizability. Neither nonnegativity of 24 arbitrary gaps,
nor a collection of known restricted spectral cases, supplies this theorem.

Even proving the quaternion capacity inequality would settle only that
unitary family. A further justified extension to arbitrary U(4), and then
to all dimensions, would still be necessary for unrestricted complex MOC.

# Exact coefficient-pair and exterior-square reductions

This note does not prove or disprove the Marcus–de Oliveira conjecture (MOC).

## 1. One complex parameter can be eliminated exactly

Suppose `D(t)=D0+t D1` and `Z_pi(t)=Z_pi,0+t Z_pi,1`. Then

`D(t) in conv{Z_pi(t)} for every complex t`

is equivalent to

`(D0,D1) in conv{(Z_pi,0,Z_pi,1)} subset C^2 = R^4`.

Proof: the reverse direction uses the same convex weights for every t. For the forward direction, every real linear functional on C² is `Re(c0 x+c1 y)`. When c0 is nonzero this is `Re(c0(x+t y))` for t=c1/c0; c0=0 follows by a limit. The separating-hyperplane theorem then gives the result. This does not extend automatically to several free complex parameters, because their monomials satisfy algebraic relations.

For projectively normalized A=(0,1,infinity,t) and finite B spectrum b, the 24 coefficient-pair vertices are

`(Z0,Z1) = (b_i b_l (1+b_j), b_i(1+b_j))`,

where i,j,l are distinct indices and the fourth index is assigned to the infinity row.

Writing C=U diag(b) U*, the determinant coefficient pair is

`D1 = C_00 + det C[{0,1},{0,1}]`,

`D0 = det C[{0,3},{0,3}] + det C[{0,1,3},{0,1,3}]`.

This follows by extracting the leading coefficient of the infinity-row diagonal variable, then expanding the remaining 3×3 determinant in its two nonzero diagonal updates.


## 2. A concrete SU(4) to SO(6) reduction

Multiplying U by a scalar phase does not affect the determinant problem, so assume det U=1. In the exterior basis indexed by 12,13,14,23,24,34, choose the real Hodge basis

`f=(e12+e34, i(e12-e34), e13-e24, i(e13+e24), e14+e23, i(e14-e23))/sqrt(2)`.

In this basis R=Lambda² U is real special orthogonal. Write R as a 3×3 array of 2×2 real blocks R_ab, and define

`m_ab=||R_ab||_F²`, `h_ab=det(R_ab)`.

For primary pairs I1=12,I2=13,I3=14 (and corresponding column pairs),

`q_{Ia,Jb}=q_{Ia^c,Jb^c}=(m_ab+2h_ab)/4`,

`q_{Ia,Jb^c}=q_{Ia^c,Jb}=(m_ab-2h_ab)/4`.

Let S have rows (1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1). Then the singleton matrix is

`q^(1)=(ones(4,4)+S h S^T)/4`.

Thus all squared minors, and hence the determinant, are affine functions of the nine block norms and nine block determinants. The block masses satisfy row and column sums 2.

Here is the exact spectral coefficient formula. Let

`L_ij=a_[4]\i b_j + a_i b_[4]\j`,

`A_a=product_{i in Ia}a_i`, `Ac_a=product_{i in Ia^c}a_i`,

and similarly B_b,Bc_b. Set

`K=product_i a_i + product_j b_j + (1/4) sum_ij L_ij`,

`H_ab=(1/4)(A_a+Ac_a)(B_b+Bc_b)`,

`G_ab=(1/2)(Ac_a-A_a)(B_b-Bc_b)+(1/4)(S^T L S)_ab`.

Then

`det(A+UBU*) = K + sum_ab H_ab m_ab + sum_ab G_ab h_ab`.

The formula follows directly by substituting the displayed minor formulas into the Cauchy–Binet expansion.

The reduction is an exact orthogonal optimization problem with the stated
spectral coefficients H,G. No reduction to block-permutation matrices or
arbitrary independent coefficients is asserted.

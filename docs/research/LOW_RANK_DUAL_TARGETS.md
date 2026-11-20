# Two concrete simultaneous-dual targets

The rank-one plane has an exact original-gap positivity proof; the rank-four family has an exact one-variable reduction, not a universal positivity proof. See the [oracle derivation](low_rank_joint_positivity_oracle.md) and [independent audit](low_rank_dual_targets_independent_review.md). **Neither is unrestricted MOC4.**

All directions and objectives use the same19-coordinate canonical pencil and common allocation from [JOINT_CERTIFICATE_RANK.md](JOINT_CERTIFICATE_RANK.md). No allocation maximum is split among factors. In formulas below, C denotes a formal Hermitian cofactor matrix, not the3by6allocation-constraint matrix.

## 1. A rank-one plane that is unconditionally safe

For real x,z,t set

    T=i t [[0,z,-x],[-z,0,x],[x,-x,0]],
    C=(x,x,z)(x,x,z)^T,       d=0,
    q=(coords T,coords C,d),  Y=qq^T.

The exact matrices give <Y,A_e>=0 for all6allocation directions and <Y,G_j>=0 for all8cubic gauges. Thus the matrix objective does not depend on which common legal allocation is chosen.

Define original support-gap coordinates and auxiliary scalars

    Sminus=w12+w13, Splus=w24+w34, W=w23,
    a=(x-z)^2, b=(x+z)^2, h=|xt|, epsilon=sign(xt),
    L=4[h(x²+z²)-x²(z²+t²)], lambda=max(0,L).

Either epsilon=±1 may be chosen when xt=0. The following are nonnegative combinations of original permutation gaps:

    Aeps=2(Sminus+W)-epsilon J012/2,
    Beps=2(Splus+W)-epsilon J123/2,
    Ceps=d3+2(Sminus+Splus)-epsilon(J012+J123)/2.

Aeps and Beps are individual three-cycle gaps. Using1-based one-line permutation notation,

    Cplus=Delta4123+Delta3421,
    Cminus=Delta2341+Delta4312.

The exact identity, checked in all13profile directions, is

    <Y,F> = (4ha-lambda)Aeps+(4hb-lambda)Beps+lambda Ceps
          +4a(|x|-|t|)^2 Sminus+4b(|x|-|t|)^2 Splus
          +4(lambda-L)W+[(x²-z²)^2-lambda]d3.

Every coefficient is nonnegative. Besides lambda>=0 and lambda>=L, the only required bounds follow from

    4h min(a,b)-L =4x²(|z|-|t|)^2 >=0,
    (x²-z²)^2-L =(x²+z²-2h)^2 >=0.

If L<=0, lambda=0 also satisfies the upper bounds. These identities cover x=0,t=0,z=0 and ties without division. Hence this entire plane is positive even for **formal** supported gap profiles, without needing actual spectral linkage.

Conic sums of these Y also have zero allocation and gauge pairings. For scalar multipliers associated with such a sum, take one common legal alpha. The stationarity equation yields

    mu.w+xi.r =mu.(w-alpha)+nu.alpha+xi.(r+C_allocation alpha) >=0.

Consequently no full joint certificate with its matrix part in this generated subcone can be negative. This does not extend to all pure-plus rank-one vectors: the first two coordinates of the cofactor vector here are equal.

## 2. An explicit rank-(0,4), zero-scalar-support family

Take u,v>0 and real k. Define four feature columns; unspecified entries vanish and lower entries are Hermitian conjugates:

| Column | T | Upper off-diagonal entries of C | d |
|---|---|---|---|
| q0 | diag(u²/v,1/v,1/v) | zero | -v |
| q1 | T12=k | C12=i |0|
| q2 | T13=k | C13=-i |0|
| q3 | T23=k/u | C23=iu |0|

Set Y=sum_l q_l q_l^T and mu=nu=xi=0. This is an explicit PSD factorization; the columns are independent because q0 has a nonzero d and q1,q2,q3 have distinct nonzero C-imaginary coordinates. Thus rankY=4. All14allocation/gauge pairings vanish exactly. Its parity/support pattern is (rplus,rminus,s)=(0,4,0).

Write

    A=w12+w14+w23+w34, B=w13+w24, g=A+B,
    D=d1+d3, E=d2, J=J012-J013+J023-J123.

Its full objective is

    L(u,v,k)=g v²+[A u⁴+B(u²-2)²]/v²
             +u²(-2A+6B+2D-2E)+4A-4B+4E
             +4k²(A+B/u²)+kJ.

The main exact verifier checks all13coefficients, not sampled parameter values. By [ODD_PROFILE_LINKAGE.md](ODD_PROFILE_LINKAGE.md), J=chi/2=-2 Re(eta det[1,a,b,ab]); it is therefore an actual determinant coordinate, not an independently movable odd coefficient.

## 3. The remaining one-variable inequality

Assume g>0 and set tau=u²>0. Since A,B>=0, A tau+B>0. Completing the square in k and minimizing the positive v terms gives the exact infimum

    R(tau)=2sqrt(g[A tau²+B(tau-2)²])
           +tau(-2A+6B+2D-2E)+4A-4B+4E
           -J² tau/[16(A tau+B)].

Indeed, with Q=A tau²+B(tau-2)², the v expression has infimum2sqrt(gQ) by the square (sqrt(g)v-sqrt(Q)/v)^2, and the k minimizer is -J/[8(A+B/tau)]. If Q=0 the v infimum need not be attained, but the universal nonnegativity equivalence remains valid by taking v arbitrarily small. No generic positive-Q assumption is hidden.

Therefore positivity of this **particular family** on a supported actual input is equivalent to

    R(tau)>=0 for every tau>0.

With Delta=4B+D-E, the linear coefficient is -2g+2Delta. Universal actual-spectral nonnegativity is not proved by this reduction.

The g=0 boundary is not included in this displayed division formula, but this family has a direct boundary proof. The already audited boundary support lemma gives every w=0, every three-cycle gap=0 and hence J=0, together with D>=E>=0 from the double-transposition triangle inequalities. The original objective becomes L=2u²(D-E)+4E>=0. Thus only g>0 is left for this family; no unproved boundary continuity or division by zero is required.

[The audited sufficient budget](RANK_FOUR_BUDGET.md) and [new optimized exclusions](OPTIMIZED_RANK_FOUR_BUDGET.md) narrow this remaining parameter region without closing actual-spectral positivity.


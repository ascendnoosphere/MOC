# A smaller exact order-inequality target for the rank-four family

The proposed budget is **not proved for arbitrary actual spectra**, and the rank-four family remains unresolved. **Not unrestricted MOC4.** The [independent mathematical audit](rank_four_budget_independent_review.md) validates the conditional results below.

See [LOW_RANK_DUAL_TARGETS.md](LOW_RANK_DUAL_TARGETS.md) for the independently audited PSD family/reduction and [oracle derivation](rank_four_budget_oracle.md).

## 1. Input and statement

For identity-supported canonical data write

    A=w12+w14+w23+w34, B=w13+w24, g=A+B,
    D=d1+d3, E=d2, J=J012-J013+J023-J123,
    Delta=4B+D-E.

Original-gap inequalities give A,B,D,E>=0 and |J|<=8g. There is also the exact identity

    Delta=gap2341+gap4123>=0,

in one-based one-line permutation notation. Thus this is an original comparison budget, not an extra hypothesis about spectra.

For g>0 the family positivity target is R(t)>=0 for every t>0, where

    R(t)=2sqrt(g[A t²+B(t-2)²])+t(-2A+6B+2D-2E)+4A-4B+4E
         -J² t/[16(A t+B)].

The g0boundary is already closed by the audited support lemma, giving original objective2u²(D-E)+4E>=0.

**Sufficient-budget theorem.** Under the displayed supported-gap inequalities, the additional inequality

    (*)  J²<=64A(A+2B+D)+32B Delta

implies R(t)>=0 for every t>0. Independently of (*), R(t)>=0 on0<t<=2, and for all t>0 whenever E<=D.

**The unresolved actual-spectral question is whether (*) holds universally, or another bound suffices where it fails.** Do not use (*) as an established spectral theorem.

## 2. Exact proof of the unconditional interval

Put h=At+B>0 and P=g[At²+B(t-2)²]. The bound J²<=64g² gives

    R(t)>=S(t)+2tD+2(2-t)E,
    S(t)=2sqrt(P)+(-2A+6B)t+4A-4B-4g²t/h.

In fact S(t)>=0 for all t>0. Set

    N=2g²t+[(A-3B)t-2A+2B]h.

Then S(t)=2[sqrt(P)-N/h], and direct polynomial expansion gives

    P h²-N²=4AB(t-1)²[N+g(At²+B)].

If N<0 the result is immediate. If N>=0 the right side is nonnegative, so sqrt(P)>=N/h. Hence S>=0. For0<t<=2 the remaining D/E terms are nonnegative. If E<=D, rewrite them as2t(D-E)+4E>=0, proving the whole range without (*). These arguments allow A0or B0; g>0 always keeps h positive.

## 3. Exact proof for t>=2 under (*)

The identity

    P-(gt-2B)²=4AB>=0

implies sqrt(P)>=gt-2B, even when the right side is negative. Put H=A-2B+E and C=J²/16. It follows that

    R(t)>=4H+2Delta t-Ct/(At+B).

Define Cs(t)=(4H+2Delta t)(A+B/t). It is enough that C<=Cs(t).

- If H<=0, Cs'(t)=2A Delta-4BH/t²>=0, while

      Cs(2)-4g²=2AB+4AD+2BD>=0.

  Since C<=4g², positivity follows without (*).

- If H>=0, let Cstar=4A(A+2B+D)+2B Delta. The exact identity

      Cs(t)-Cstar=2A Delta(t-2)+4BH/t>=0

  proves the assertion whenever C<=Cstar, which is exactly (*).

All square-root comparisons and divisions use stated nonnegative quantities or h,t>0. No hidden strict A/B/D assumption is needed.

## 4. A much narrower region for any negative

The original |J|bound implies (*) automatically if2AD+B Delta>=2B². Therefore a negative would require **all** of

    t>2, B>0, AD<B²,
    0<=Delta<2B-2AD/B,
    J²>64A(A+2B+D)+32B Delta.

Equivalently, its even parameters must lie in

    D+2B+2AD/B < E <= D+4B.

These are proved exclusions, not a numerical trend. They do not yet rule out this region on actual spectra.


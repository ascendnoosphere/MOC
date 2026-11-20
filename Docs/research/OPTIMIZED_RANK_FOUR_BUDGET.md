# Optimizing the rank-four comparison budget

Stronger sufficient exclusions are proved below. Neither the corrected budget nor positivity of the whole rank-four family is proved on arbitrary actual spectra. **Unrestricted MOC4 remains open.**

[Oracle derivation](optimized_rank_four_budget_oracle.md), [independent verifier](../../code/research/verify_optimized_rank_four_budget.py).

## 1. Only the still-dangerous region is relevant

Use A,B,D,E,J,g,Delta,R from [RANK_FOUR_BUDGET.md](RANK_FOUR_BUDGET.md). The original supported-gap inequalities give A,B,D,E,Delta>=0 and |J|<=8g. The g=0 boundary is closed directly. The previous proved exclusions already restrict a negative to

    t>2, B>0, AD<B², 0<=Delta<2B-2AD/B,
    E>D+2B+2AD/B.

Put

    H=A-2B+E=A+D+2B-Delta>0,
    C=J²/16<=4g².

The valid square-root bound from the preceding note gives, for t>=2,

    R(t)>=4H+2Delta t-Ct/(At+B)
         =t[Cs(t)-C]/(At+B),
    Cs(t)=4AH+2BDelta+2ADelta t+4BH/t.

The following are exact optimizations of this **lower bound**, not of R itself.

## 2. Two stronger sufficient criteria

Either criterion implies R(t)>=0 for every t>0:

    (i)  2ADelta>=BH;
    (ii) J²<=64[sqrt(AH)+sqrt(BDelta/2)]².

Consequently the purely even condition

    (iii) sqrt(AH)+sqrt(BDelta/2)>=A+B

excludes a negative without any further bound on J.

**Proof of(i).** For t>=2,

    Cs'(t)=2ADelta-4BH/t²>=2ADelta-BH>=0.

Also Cs(2)-4g²=2AB+4AD+2BD>=0, so Cs>=C.

**Proof of(ii).** Nonnegative AM–GM, including zero factors, gives

    2ADelta t+4BH/t>=4sqrt(2ABHDelta),
    Cs(t)>=m=4AH+2BDelta+4sqrt(2ABHDelta)
               =4[sqrt(AH)+sqrt(BDelta/2)]².

Condition(ii)is C<=m. The interval0<t<=2was proved separately, so both criteria cover the full target range. Condition(iii)uses the supported bound C<=4g². No complex projection is squared.

When ADelta>0, the unconstrained minimizer is

    tstar=sqrt(2BH/(ADelta)).

If tstar<=2, criterion(i)applies. Otherwise m is the exact minimum of Cs on[2,infinity). If ADelta=0, m is the limiting infimum as t tends to infinity. These statements are about Cs, and do not assert that the lower bound is sharp for R.

The preceding sufficient budget used Cstar=4A(A+2B+D)+2BDelta. In the tstar>2branch,

    m-Cstar=4sqrt(2ABHDelta)-4ADelta>0,

since BH>2ADelta and ADelta>0. Thus the optimized budget genuinely allows larger J² in this branch; it is not just the old inequality renamed.

## 3. An exact actual example enlarging the even-only exclusion

Let

    a=(-2+2i,1+2i,-2+3i,-2+i),
    b=(-2-2i,-3-3i,-3+3i,2-i), eta=1.

Identity height=0 and all24lexicographic gaps are

    (0,24,0,168,380,524, 0,30,0,154,392,516,
     0,30,0,10,470,450, 20,20,26,12,104,90).

The exact canonical profile is

    w=(0,0,3,0,131,6), d=(30,470,90),
    Jcycles=(0,496,-16,-212).

Therefore (A,B,D,E,J,Delta,H)=(9,131,120,470,-300,174,217). The determinant150+64i independently gives J=-2Re(det)=-300.

This lies in the old dangerous **even-parameter** region: AD=1080<B²=17161, and Delta=174<262-2160/131. The old even-only test fails, since 2AD+BDelta=24954<2B²=34322.

But base=4AH+2BDelta=53400, q=2ABHDelta=89033364, and

    16q-25000²=799533824>0.

Both sides of the compared square roots are nonnegative, so m=53400+4sqrt(q)>78400=4g². The new even-only criterion proves positivity even if J is replaced by its full supported maximum. This example is **not** an old corrected-budget violation; its actual J was already small enough. It demonstrates additional even-only coverage, not an actual negative or universal linkage theorem.

## 4. A finite localization for any remaining negative

For ADelta>0 define

    KC=C-4AH-2BDelta.

The same lower bound is

    R(t)>=[2ADelta t²-KC t+4BH]/(At+B).

Thus a negative must have KC>0, KC²>32ABHDelta and

    (KC-sqrt(KC²-32ABHDelta))/(4ADelta)
       <t<
    (KC+sqrt(KC²-32ABHDelta))/(4ADelta),   t>2.

This is necessary, not sufficient. Using K=4g²-4AH-2BDelta in place of KC gives the oracle's weaker even-only finite interval. The main verifier checks the factorization with the sharper actual C.

A remaining negative must also violate both new sufficient criteria:

    2ADelta<BH,
    J²>64[sqrt(AH)+sqrt(BDelta/2)]²,
    sqrt(AH)+sqrt(BDelta/2)<g.

These conditions still leave a nonempty formal region. Actual coupled spectral linkage has not excluded it.


### 1. New exclusion theorem

Use the prescribed quantities and put
\[
g=A+B,\qquad H=A-2B+E=A+D+2B-\Delta,\qquad C=\frac{J^2}{16}.
\]
In the dangerous region, \(B>0\) and
\[
E>D+2B+\frac{2AD}{B},
\]
so \(H>0\).

Then **either** of the following conditions proves \(R(t)\ge0\) for every \(t>0\):
\[
\boxed{2A\Delta\ge BH,} \tag{1}
\]
or
\[
\boxed{
J^2\le64\left(\sqrt{AH}+\sqrt{\frac{B\Delta}{2}}\right)^2.
} \tag{2}
\]

Consequently, using the supported bound \(|J|\le8g\), the purely even condition
\[
\boxed{
\sqrt{AH}+\sqrt{\frac{B\Delta}{2}}\ge A+B
} \tag{3}
\]
also excludes a negative.

Condition (3) excludes additional parameters for which the recorded even-only test
\[
2AD+B\Delta\ge2B^2
\]
fails. That earlier test is at `organized/research/RANK_FOUR_BUDGET.md:81`.

### 2. Proof

The exact \(R\)-reduction and the already-proved interval \(0<t\le2\) are recorded at `organized/research/LOW_RANK_DUAL_TARGETS.md:79–95` and `organized/research/RANK_FOUR_BUDGET.md:32–51`. It remains to prove \(t\ge2\).

Set
\[
h=At+B>0,\qquad P=g\bigl[At^2+B(t-2)^2\bigr].
\]
The identity
\[
P-(gt-2B)^2=4AB\ge0
\]
gives \(\sqrt P\ge gt-2B\). Substitution into \(R\) yields
\[
R(t)\ge4H+2\Delta t-\frac{Ct}{At+B}
       =\frac{t}{At+B}\bigl[C_s(t)-C\bigr],
\]
where
\[
C_s(t)
=(4H+2\Delta t)(A+B/t)
=4AH+2B\Delta+2A\Delta t+\frac{4BH}{t}. \tag{4}
\]
This starts from the valid lower bound in `organized/research/RANK_FOUR_BUDGET.md:59–63`; the improvement is to minimize it rather than replace it by the recorded constant budget.

**Case (1).** For \(t\ge2\),
\[
C_s'(t)=2A\Delta-\frac{4BH}{t^2}
       \ge2A\Delta-BH\ge0.
\]
Moreover,
\[
C_s(2)-4g^2=2AB+4AD+2BD\ge0.
\]
Since support gives \(C\le4g^2\), equation (4) proves positivity.

**Case (2).** Nonnegative AM–GM gives, for every \(t>0\),
\[
2A\Delta t+\frac{4BH}{t}
\ge4\sqrt{2ABH\Delta}.
\]
Therefore
\[
C_s(t)\ge
m:=4AH+2B\Delta+4\sqrt{2ABH\Delta}
=4\left(\sqrt{AH}+\sqrt{\frac{B\Delta}{2}}\right)^2.
\]
Condition (2) is exactly \(C\le m\), proving positivity.

No complex projection was squared here. The sole squaring in the verification example below compares explicitly nonnegative real quantities.

When \(A\Delta>0\), the unconstrained minimizer is
\[
t_*=\sqrt{\frac{2BH}{A\Delta}}.
\]
Thus (1) is precisely the case \(t_*\le2\); otherwise \(m\) is the exact minimum of \(C_s\) on \(t\ge2\).

**The optimized threshold is for this lower bound, not necessarily for \(R\) itself.**

### 3. Why this is stronger than the corrected budget

The corrected budget is \(C\le C_*\), where
\[
C_*=4A(A+2B+D)+2B\Delta.
\]
In the branch \(A\Delta>0,\ t_*>2\),
\[
m-C_*
=4\sqrt{2ABH\Delta}-4A\Delta>0.
\]
Hence (2) permits strictly larger \(J^2\) than the corrected budget in this branch. When \(t_*\le2\), condition (1) proves positivity without any additional determinant budget.

This does **not** establish either budget on all actual spectra.

### 4. Exact actual data in the newly excluded even region

Take
\[
\begin{aligned}
a&=(-2+2i,\ 1+2i,\ -2+3i,\ -2+i),\\
b&=(-2-2i,\ -3-3i,\ -3+3i,\ 2-i),\qquad \eta=1.
\end{aligned}
\]
The identity score is zero. All 24 gaps, in lexicographic one-line permutation order, are
\[
\begin{split}
(&0,24,0,168,380,524,\;
0,30,0,154,392,516,\\
&0,30,0,10,470,450,\;
20,20,26,12,104,90).
\end{split}
\]
Thus identity support holds exactly, including its ties.

With **transposition gaps divided by four and double gaps unscaled**, the profile is
\[
w=(0,0,3,0,131,6),\qquad d=(30,470,90),
\]
\[
(J_{012},J_{013},J_{023},J_{123})=(0,496,-16,-212).
\]
Consequently
\[
(A,B,D,E,J,\Delta,H)=(9,131,120,470,-300,174,217).
\]
Directly,
\[
\det[1,a,b,ab]=150+64i,\qquad
J=-2\Re\det[1,a,b,ab]=-300.
\]
These conventions agree with `organized/research/ACTUAL_FIBER_ALLOCATION.md:15` and `organized/research/ODD_PROFILE_LINKAGE.md:64–75`.

This lies inside the dangerous **even-parameter** region:
\[
AD=1080<17161=B^2,\qquad
0<174<262-\frac{2160}{131}.
\]
The previous even-only exclusion fails:
\[
2AD+B\Delta=24954<34322=2B^2.
\]
But the new exclusion succeeds. Here
\[
4AH+2B\Delta=53400,\qquad
2ABH\Delta=89033364,
\]
and
\[
16(89033364)-25000^2
=\boxed{799533824}>0.
\]
Therefore
\[
m=53400+4\sqrt{89033364}>78400=4g^2.
\]
So the new argument proves positivity even with \(J^2\) replaced by its full supported upper bound \(64g^2\).

This example demonstrates the enlarged **even-only exclusion**. It is neither a violation of the corrected budget nor a negative certificate.

### 5. Explicit remaining gap and \(t\)-localization

After this result, any negative with \(A\Delta>0\) must satisfy, in addition to all previously recorded necessary conditions,
\[
\boxed{
2A\Delta<BH,\qquad
\sqrt{AH}+\sqrt{\frac{B\Delta}{2}}<g,\qquad
J^2>64\left(\sqrt{AH}+\sqrt{\frac{B\Delta}{2}}\right)^2.
}
\]

There is also a rigorous finite localization in \(t\). Put
\[
K=4g^2-4AH-2B\Delta.
\]
From (4) and \(C\le4g^2\),
\[
R(t)\ge
\frac{2A\Delta t^2-Kt+4BH}{At+B}.
\]
Thus a negative requires
\[
K>0,\qquad K^2>32ABH\Delta,
\]
and
\[
\boxed{
\frac{K-\sqrt{K^2-32ABH\Delta}}{4A\Delta}
<t<
\frac{K+\sqrt{K^2-32ABH\Delta}}{4A\Delta},
\qquad t>2.
}
\]

The unresolved boundary faces are explicit:

- **\(A=0\):** for \(t\ge2\),
  \[
  R(t)=4H+t\left(2\Delta-\frac{J^2}{16B}\right).
  \]
  Positivity on this half-line is equivalent to \(J^2\le32B\Delta\). The optimization does not resolve that actual-spectral obligation.
- **\(\Delta=0,\ A>0\):** the optimized budget reduces to the corrected budget \(J^2\le64AH\); no improvement is claimed.
- **\(g=0\)** is covered directly by the existing boundary proof, not continuity (`organized/research/LOW_RANK_DUAL_TARGETS.md:95`).

The proof uses arbitrary supported \(\eta\), without normalizing spectra or changing support direction. Zero \(\eta\), repeated spectra, and support ties require no extension argument.


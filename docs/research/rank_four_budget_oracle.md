## 1. Exact verification of the family

Using all thirteen canonical profile matrices and all fourteen allocation/gauge directions in `organized/research/actual_fiber_allocation/criterion.json:33` and `organized/research/actual_fiber_allocation/criterion.json:5248`, I independently checked symbolically that the four supplied columns satisfy
\[
\operatorname{tr}(Q^TA_eQ)=\operatorname{tr}(Q^TG_jQ)=0
\]
and reproduce the stated \(\mathcal L(u,v,k)\). Their minor on feature rows \(18,13,15,17\), zero-indexed, is \(uv\), so their rank is exactly four.

Thus the target is indeed the family in `organized/research/low_rank_joint_positivity_oracle.md:87–143`, with no scalar multipliers or allocation relaxation introduced.

## 2. Proved: a sufficient budget for the entire family

Write
\[
\Delta=4B+D-E,\qquad g=A+B>0.
\]
The original triangle budgets give
\[
|J|\le8g
\]
(`organized/research/ODD_PROFILE_LINKAGE.md:51–60`). I also checked the exact original-gap identity
\[
\boxed{\Delta=\Delta_{2341}+\Delta_{4123}\ge0,}
\]
where subscripts are one-line permutations.

The following statement is proved purely algebraically.

> **Sufficient-budget lemma.** Under the supported-gap conditions
> \(A,B,D,E,\Delta\ge0\) and \(|J|\le8g\), the inequality
> \[
> \boxed{J^2\le
> 64A(A+2B+D)+32B\Delta} \tag{★}
> \]
> implies \(R(\tau)\ge0\) for every \(\tau>0\).
>
> Independently of (★), \(R(\tau)\ge0\) for \(0<\tau\le2\).

**Crucial limitation:** I have **not** proved (★) for arbitrary actual supported spectra. It is a sufficient target, not an assumed spectral theorem.

### Proof for \(0<\tau\le2\)

Put \(t=\tau\), \(h=At+B>0\), and
\[
P=g\{At^2+B(t-2)^2\}.
\]
Using \(J^2\le64g^2\),
\[
R(t)\ge S(t)+2tD+2(2-t)E,
\]
where
\[
S(t)=2\sqrt P+(-2A+6B)t+4A-4B-\frac{4g^2t}{h}.
\]

In fact \(S(t)\ge0\) for **every** \(t>0\). Define
\[
N=2g^2t+\bigl((A-3B)t-2A+2B\bigr)h.
\]
Then \(S(t)=2(\sqrt P-N/h)\), and exact expansion gives
\[
\boxed{
Ph^2-N^2
=4AB(t-1)^2\bigl[N+g(At^2+B)\bigr].
}
\]
If \(N<0\), positivity is immediate. If \(N\ge0\), the right-hand side is nonnegative, so \(\sqrt P\ge N/h\). Consequently \(S(t)\ge0\), proving the asserted interval result. This also proves whole-family positivity whenever \(E\le D\).

### Proof for \(t\ge2\) under (★)

Cauchy–Schwarz gives
\[
\sqrt P\ge gt-2B.
\]
Set
\[
H=A-2B+E,\qquad C=\frac{J^2}{16}.
\]
It follows that
\[
R(t)\ge4H+2\Delta t-\frac{Ct}{At+B}.
\]
Define
\[
C_s(t)=(4H+2\Delta t)(A+B/t).
\]

If \(H\le0\), then
\[
C_s'(t)=2A\Delta-\frac{4BH}{t^2}\ge0
\]
and
\[
C_s(2)-4g^2=2AB+4AD+2BD\ge0.
\]
Thus \(C\le4g^2\le C_s(t)\), proving positivity without (★).

If \(H\ge0\), put
\[
C_* =4A(A+2B+D)+2B\Delta.
\]
The exact identity
\[
\boxed{
C_s(t)-C_*
=2A\Delta(t-2)+\frac{4BH}{t}\ge0
}
\]
shows that (★), equivalently \(C\le C_*\), suffices. This completes the lemma.

## 3. A narrower necessary region for any negative

Since \(|J|\le8g\), condition (★) holds automatically whenever
\[
2AD+B\Delta\ge2B^2.
\]
Therefore any actual negative in this family must satisfy **all** of
\[
\boxed{
\begin{gathered}
\tau>2,\qquad B>0,\qquad AD<B^2,\\
0\le\Delta<2B-\frac{2AD}{B},\\
J^2>64A(A+2B+D)+32B\Delta.
\end{gathered}}
\]
Equivalently, the unresolved even-budget region requires
\[
D+2B+\frac{2AD}{B}<E\le D+4B.
\]

These are rigorous exclusions, not numerical observations.


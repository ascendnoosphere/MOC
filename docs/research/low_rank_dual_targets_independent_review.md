### 1. Rank-one plane: valid, including degeneracies
**Locations:** `organized/research/LOW_RANK_DUAL_TARGETS.md:9–51`; `organized/research/verify_low_rank_joint_targets.py:96–129`.

- All **14 allocation/gauge pairings vanish identically**.
- All **13 objective coefficients** agree with the stated gap decomposition.
- Independently identified the individual cycle gaps, in one-based one-line notation:
  \[
  A_+=\Delta_{3124},\quad A_-=\Delta_{2314},\qquad
  B_+=\Delta_{1423},\quad B_-=\Delta_{1342}.
  \]
  Both stated \(C_\epsilon\) gap sums are correct.
- The identity uses \(\epsilon h=xt\), which remains valid for either sign when \(xt=0\). In that case \(h=0\), \(L\le0\), and \(\lambda=0\); no sign ambiguity survives.
- Both upper bounds on \(\lambda\) are correct. Together with \(\lambda\ge0,L\), they establish every coefficient’s nonnegativity, including zero parameters and ties.
- The conic-sum argument correctly uses **one common legal allocation**. Its scalar identity follows from stationarity with zero allocation pairing; it does not optimize allocation separately for factors.
- Nothing here justifies replacing \(p=(x,x,z)\) by arbitrary \(p\), or claiming positivity for all pure-plus rank-one certificates.

### 2. Rank-\((0,4)\) family and reduction: valid
**Locations:** `organized/research/LOW_RANK_DUAL_TARGETS.md:55–95`; `organized/research/verify_low_rank_joint_targets.py:59–74`.

- The displayed factorization is PSD. The distinguishing four-row factor minor is exactly \(uv\), so rank is **four everywhere on \(u,v>0\)**, including \(k=0\).
- All columns lie in the minus-parity block; scalar support is zero.
- All **14 annihilators** and **13 profile coefficients** check symbolically. The stated \(\mathcal L(u,v,k)\) is exact.
- Direct expansion in eight independent spectral symbols confirms
  \[
  J=-2\Re\!\left(\eta\det[1,a,b,ab]\right)=\chi/2,
  \]
  including its sign and normalization.
- For \(g>0\), completing the \(k\)-square and taking the \(v\)-infimum gives precisely \(R(\tau)\). If \(Q=0\), the \(v\)-infimum is unattained but approached as \(v\downarrow0\); hence the universal nonnegativity equivalence remains correct.

**Version note:** During review, the main writer replaced the initially excluded \(g=0\) discussion with a direct boundary argument. I reread and checked that update. The division formula still excludes \(g=0\), while the original objective correctly reduces to
\[
\mathcal L=2u^2(D-E)+4E\ge0.
\]
The required \(D\ge E\ge0\) follows from the supported double-transposition triangle inequalities. The verifier explicitly labels this support lemma as a dependency rather than claiming its substitution check proves it.


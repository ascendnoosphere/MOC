### Mathematical audit

- **Supported inputs and normalization — PASS.** With \(w_{ij}=\mathrm{gap}_{(ij)}/4\), the stated \(A,B,D,E\) are nonnegative. The four triangle-gap identities give \(|J|\le8g\). I independently expanded those identities and
  \[
  4B+D-E=\mathrm{gap}_{2341}+\mathrm{gap}_{4123}
  \]
  directly in eight spectral symbols, without using the saved Fourier map. These polynomial identities include repeated spectra and ties.  
  References: `organized/research/RANK_FOUR_BUDGET.md:11–19`.

- **Rank-four target and minimization — PASS.** The four columns define the stated PSD rank-four family; completing the \(k\)-square and minimizing in \(v>0\) gives the displayed \(R(t)\). The \(Q=0\) case correctly uses an infimum rather than claiming attainment. The \(g=0\) boundary is handled separately, not by division or unproved continuity.  
  References: `organized/research/LOW_RANK_DUAL_TARGETS.md:55–95`.

- **\(S(t)\ge0\), including \(A=0\) or \(B=0\) — PASS.** For \(g>0,t>0\), \(h=At+B>0\). When \(N<0\), the result is immediate; when \(N\ge0\), both sides of the required square-root comparison are nonnegative and the exact \(Ph^2-N^2\) identity proves it. No invalid squaring or strict \(A,B\) assumption occurs. Thus \(0<t\le2\) is unconditional, and \(E\le D\) gives the entire range.  
  References: `organized/research/RANK_FOUR_BUDGET.md:38–51`.

- **\(t\ge2\) proof — PASS.** The square-root bound follows from \(P-(gt-2B)^2=4AB\). For \(H\le0\), the derivative and \(C_s(2)\) budget establish the claim without (*). For \(H\ge0\), the exact \(C_s-C_*\) identity establishes sufficiency of (*). The overlap \(H=0\) and all zero-parameter boundaries are harmless.  
  References: `organized/research/RANK_FOUR_BUDGET.md:55–77`.

- **Necessary negative region — PASS.** Comparing the new RHS with \(64g^2\) gives precisely the stated strict exclusions. Division by \(B\) occurs only after establishing \(B>0\). The resulting interval for \(E\) is necessary, not sufficient for a negative.  
  References: `organized/research/RANK_FOUR_BUDGET.md:81–91`.

- **Scope and tied data — PASS.** Neither report promotes (*) to a spectral theorem. The examples are checked directly at their tied, repeated-spectrum inputs; no generic-case approximation is used to transfer a labelled inequality to them.  
  References: `organized/research/RANK_FOUR_BUDGET.md:28–34,119–133`; `organized/research/rank_four_budget_oracle.md:41–51,202–204`.


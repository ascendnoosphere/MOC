### Mathematical audit

- **Original extreme-rank theorem and low-rank corollary: valid.**  
  I independently inspected `organized/research/external/blekherman_hankel_rank/BlekhermanRevision3.tex:139–265`, including the full-Hankel identification, maximal-kernel argument, rank-one evaluation classification, and Gorenstein/kernel proof chain. Four parameter quadrics give a complete intersection with degree-four socle; an additional independent kernel quadric contradicts the nonzero functional through the perfect socle pairing. Hence the non-evaluation extreme rank is \(10-4=6\).  
  The compact trace-one-base argument correctly extends this to **every full-Hankel PSD matrix of rank at most five**: every PSD summand has range contained in the original range, excluding rank-six extreme summands. See `organized/research/HANKEL_RANK_BRIDGE.md:9–17`.

- **Full 20 versus inner 14 relation spaces: valid.**  
  The counts \(55-35=20\) and \(45-31=14\), and the missing six minus-block relations \(\operatorname{adj}(T)=0\), are correct. I additionally reconstructed, without importing project helpers, both pure-parity coefficient-row spaces and confirmed
  \[
  \operatorname{span}(\text{14 canonical quadrics})
  =\operatorname{span}(TC,\operatorname{adj}(C)-dT),
  \]
  with rank 14 on each block. The distinction between zero allocation pairings and scalar-balanced joint stationarity is correctly maintained. See `organized/research/HANKEL_RANK_BRIDGE.md:23–39`.

- **Exact PSD completion criterion, including singular \(D\): valid.**  
  Necessity follows by testing the required principal block against \(\ker D\). For sufficiency, \(Dk=a\) makes the displayed completion a congruence image of \(Y\), with the old \(Y\) retained as a principal submatrix; consequently PSD and rank are preserved exactly. The six new identities complete the full-Hankel relations. Both numerical examples are exact. The shorted residual appropriately retains its **own** range-condition requirement rather than asserting automatic completion. See `organized/research/HANKEL_RANK_BRIDGE.md:43–68`.

- **Minus and scalar-coupled rank-one obstructions: valid.**  
  The exceptional \(q=(I_3,0,0)\) violates the missing Hankel relations. For \(q=(I_3,0,1)\), the pairings are six copies of \(-4\), followed by eight zeros; \(\nu_e=4\), \(\mu=\xi=0\) satisfies stationarity. The normalization denominator is \(4+24=28\). Since \(\operatorname{adj}(C)-dT=-I_3\), this vector lies outside the projective Cayley closure, and rank-one PSD range containment rules out a positive Cayley-atomic decomposition. No negative objective follows or is claimed. See `organized/research/HANKEL_RANK_BRIDGE.md:72–80`.


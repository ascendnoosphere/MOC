import MOC.FourMatchingRelations
import MOC.FourMinorCertificate
import MOC.FourBudgetMinor
import MOC.FourTwoBudgetMinor

/-! The ordinary minor cone and the two capacity alternatives for T5. -/

open BigOperators

namespace MOC

noncomputable section

/-- The six prescribed contacts of paper case T5. -/
def fourT5ContactIndices : Finset (Fin 24) := {1, 2, 3, 4, 6, 8}

private def t5GapProfile (g : Fin 24 → ℝ) : Fin 24 → ℝ :=
  ![g 0, 0, 0, 0, 0, g 0, 0, g 7, 0, g 9, g 10, -g 7 + g 9 + g 10, g 12, g 13,
    g 0 + g 12, -g 7 + g 9 + g 13, g 16, -g 0 - g 7 + g 9 + g 16,
    g 0 + g 7 + g 12 - g 16 + g 22, g 0 + g 13 - g 16 + g 22, g 0 + g 10 + g 12 - g 16 + g 22,
    g 0 - g 7 + g 9 + g 10 + g 13 - g 16 + g 22, g 22, g 9 + g 22]

set_option maxHeartbeats 2000000 in
private theorem t5GapProfile_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (hc : ∀ i ∈ fourT5ContactIndices, fourMatchingEvaluation m i = H) :
    let g := fun i => fourMatchingEvaluation m i - H
    ∀ i, g i = t5GapProfile g i := by
  have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide)
  have h3 := hc 3 (by decide)
  have h4 := hc 4 (by decide)
  have h6 := hc 6 (by decide)
  have h8 := hc 8 (by decide)
  simp [fourMatchingEvaluation] at h1 h2 h3 h4 h6 h8
  dsimp only
  intro i
  fin_cases i <;> simp [t5GapProfile, fourMatchingEvaluation] <;>
    linarith only [h1, h2, h3, h4, h6, h8]

private theorem t5SpectralGapProfile (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT5ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    ∀ i, g i = t5GapProfile g i := by
  let m₀ : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re
  have hm (i : Fin 24) : fourMatchingEvaluation m₀ i =
      (η * matchingProduct a b (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part a b η i
  have hp := t5GapProfile_of_contacts m₀ H (fun i hi => (hm i).trans (hc i hi))
  dsimp only at hp ⊢
  simpa only [hm] using hp

/-- The linear gap identities at 11 and 17 used in the T5 sign reduction. -/
theorem fourT5_gap_eleven_seventeen (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT5ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    g 11 = -g 7 + g 9 + g 10 ∧ g 17 = g 16 - g 0 - g 7 + g 9 := by
  intro g
  have hp : ∀ i, g i = t5GapProfile g i := t5SpectralGapProfile a b η H hc
  refine ⟨hp 11, ?_⟩
  have h : g 17 = -g 0 - g 7 + g 9 + g 16 := by
    simpa [t5GapProfile, Matrix.cons_val] using hp 17
  linarith only [h]

private def t5MinorRows : Fin 13 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 3}, {0}, {0, 1}, {3}, {0, 3}, {0, 2}, {0, 2},
    {1}, {1, 2}, {1, 3}]

private def t5MinorColumns : Fin 13 → Finset (Fin 4) :=
  ![{3}, {2, 3}, {2, 3}, {2, 3}, {2}, {3, 1}, {0}, {1, 2}, {1, 3}, {0, 2},
    {1}, {2, 3}, {2, 1}]

private def t5MinorSupports : Fin 13 → Finset (Fin 24) :=
  ![{18, 19, 20, 21, 22, 23}, {16, 17, 22, 23}, {13, 15, 19, 21}, {12, 14, 18, 20},
    {12, 13, 14, 15, 16, 17}, {10, 11, 20, 21}, {9, 11, 15, 17, 21, 23}, {7, 10, 13, 16},
    {7, 9, 18, 23}, {0, 5, 14, 16}, {0, 1, 14, 15, 20, 21}, {3, 5, 9, 11}, {1, 3, 20, 22}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem t5MinorSupports_spec : ∀ (k : Fin 13) (i : Fin 24),
    i ∈ t5MinorSupports k ↔ (t5MinorColumns k).map (fourPerm i).symm.toEmbedding = t5MinorRows k := by
  decide +kernel

private def t5MinorWeights (g : Fin 24 → ℝ) (u v : ℝ) : Fin 13 → ℝ :=
  let A := g 16 - g 0
  ![g 7 - A + g 22 + u - v, A - g 7 - u + v, g 13 - g 7 - u + v,
    g 12 - u, u, -g 7 + g 10 + v, g 9 - v, g 7 - v, v, g 0, 0, 0, 0]

private def t5MixedWeights (g : Fin 24 → ℝ) (d₄ d₂ : ℝ) : Fin 13 → ℝ :=
  ![g 22 + d₄ + d₂, -d₄, g 13, g 12, 0, g 10, g 17 + d₄, 0, g 7, g 16 + d₄, d₂, d₂, -d₂]

set_option maxHeartbeats 2000000 in
private theorem t5GapProfile_eq_minorSum (g : Fin 24 → ℝ) (u v : ℝ) (i : Fin 24) :
    t5GapProfile g i = ∑ k, if i ∈ t5MinorSupports k then t5MinorWeights g u v k else 0 := by
  fin_cases i <;>
    simp (config := { decide := true }) [t5GapProfile, t5MinorSupports, t5MinorWeights,
      Fin.sum_univ_succ, Matrix.cons_val] <;> ring

set_option maxHeartbeats 2000000 in
private theorem t5GapProfile_eq_mixedSum (g : Fin 24 → ℝ) (d₄ d₂ : ℝ)
    (hd : d₄ + d₂ = g 0 - g 16) (hprofile : ∀ i, g i = t5GapProfile g i) (i : Fin 24) :
    g i = ∑ k, if i ∈ t5MinorSupports k then t5MixedWeights g d₄ d₂ k else 0 := by
  have h17 : g 17 = -g 0 - g 7 + g 9 + g 16 := by
    simpa [t5GapProfile, Matrix.cons_val] using hprofile 17
  rw [hprofile i]
  fin_cases i <;>
    simp (config := { decide := true }) [t5GapProfile, t5MinorSupports, t5MixedWeights,
      Fin.sum_univ_succ, Matrix.cons_val] <;>
    (first | rfl | ring | linarith only [h17, hd])

private theorem t5_exists_nonnegative_weights (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hprofile : ∀ i, g i = t5GapProfile g i) (hA : 0 ≤ g 16 - g 0) :
    ∃ u v, ∀ k, 0 ≤ t5MinorWeights g u v k := by
  let A := g 16 - g 0
  let v := max 0 (max (g 7 - g 10) (max (g 7 - A) (g 7 - g 13)))
  let L := A - g 7 - g 22 + v
  let u := max 0 L
  have h11 : 0 ≤ -g 7 + g 9 + g 10 := by
    have h := hg 11
    rw [hprofile 11] at h
    simpa [t5GapProfile] using h
  have h15 : 0 ≤ -g 7 + g 9 + g 13 := by
    have h := hg 15
    rw [hprofile 15] at h
    simpa [t5GapProfile] using h
  have h17 : 0 ≤ A - g 7 + g 9 := by
    have h := hprofile 17
    simp [t5GapProfile] at h
    dsimp only [A]
    linarith only [h, hg 17]
  have h18 : 0 ≤ g 7 + g 12 - A + g 22 := by
    have h := hprofile 18
    simp [t5GapProfile] at h
    dsimp only [A]
    linarith only [h, hg 18]
  have h19 : 0 ≤ g 13 - A + g 22 := by
    have h := hprofile 19
    simp [t5GapProfile] at h
    dsimp only [A]
    linarith only [h, hg 19]
  have h20 : 0 ≤ g 10 + g 12 - A + g 22 := by
    have h := hprofile 20
    simp [t5GapProfile] at h
    dsimp only [A]
    linarith only [h, hg 20]
  have hv₀ : 0 ≤ v := le_max_left _ _
  have hv₁ : g 7 - g 10 ≤ v := (le_max_left _ _).trans (le_max_right _ _)
  have hv₂ : g 7 - A ≤ v := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hv₃ : g 7 - g 13 ≤ v := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hv7 : v ≤ g 7 := max_le (hg 7) (max_le (sub_le_self _ (hg 10))
    (max_le (sub_le_self _ hA) (sub_le_self _ (hg 13))))
  have hv9 : v ≤ g 9 := max_le (hg 9) (max_le (by linarith only [h11])
    (max_le (by linarith only [h17]) (by linarith only [h15])))
  have hvL : v ≤ g 7 + g 12 - A + g 22 := max_le h18 (max_le (by linarith only [h20])
    (max_le (by linarith only [hg 12, hg 22]) (by linarith only [h19, hg 12])))
  have hu₀ : 0 ≤ u := le_max_left _ _
  have huL : L ≤ u := le_max_right _ _
  have hu₁ : u ≤ A - g 7 + v := max_le (by linarith only [hv₂])
    (by dsimp only [L]; linarith only [hg 22])
  have hu₂ : u ≤ g 13 - g 7 + v := max_le (by linarith only [hv₃])
    (by dsimp only [L]; linarith only [h19])
  have hu₁₂ : u ≤ g 12 := max_le (hg 12) (by dsimp only [L]; linarith only [hvL])
  refine ⟨u, v, fun k => ?_⟩
  fin_cases k <;> norm_num [t5MinorWeights]
  · dsimp only [L, A] at huL
    linarith only [huL]
  · dsimp only [A] at hu₁
    linarith only [hu₁]
  · linarith only [hu₂]
  · exact sub_nonneg.mpr hu₁₂
  · exact hu₀
  · linarith only [hv₁]
  · exact sub_nonneg.mpr hv9
  · exact sub_nonneg.mpr hv7
  · exact hv₀
  · exact hg 0

/-- The two exact capacities suffice for the T5 support inequality on its
positive mixed branch. The ordinary minor branch needs neither capacity. -/
theorem fourT5_support_of_capacity (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT5ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hcap : let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      let d := g 0 - g 16
      0 < d → d ^ 2 ≤ g 10 * g 13 ∨
        d ^ 2 * (g 22 + g 17 + g 7 + d) ≤ g 22 * g 17 * (g 7 - d)) :
    H ≤ (η * determinantValue a b U).re := by
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  have hp' : ∀ i, g i = t5GapProfile g i := t5SpectralGapProfile a b η H hc
  have h1 := hc 1 (by decide)
  by_cases hA : 0 ≤ g 16 - g 0
  · obtain ⟨u, v, hw⟩ := t5_exists_nonnegative_weights g hg hp' hA
    refine four_support_of_minor_gap_decomposition a b η H U hU 1 h1
      t5MinorRows t5MinorColumns (t5MinorWeights g u v) hw (fun i => ?_)
    simp_rw [← t5MinorSupports_spec]
    exact (hp' i).trans (t5GapProfile_eq_minorSum g u v i)
  · let d := g 0 - g 16
    have hd : 0 < d := by dsimp only [d]; linarith only [lt_of_not_ge hA]
    have hgap (d₄ d₂ : ℝ) (hs : d₄ + d₂ = d) :
        (η * determinantValue a b U).re - H = ∑ k,
          t5MixedWeights g d₄ d₂ k * subsetMinorSq U (t5MinorRows k) (t5MinorColumns k) := by
      refine four_gap_eq_minor_decomposition a b η H U hU 1 h1 t5MinorRows t5MinorColumns
        (t5MixedWeights g d₄ d₂) (fun i => ?_)
      simp_rw [← t5MinorSupports_spec]
      exact t5GapProfile_eq_mixedSum g d₄ d₂ hs hp' i
    have h₀ := mul_nonneg (hg 22) (subsetMinorSq_nonneg U {0} {3})
    have h₁ := mul_nonneg (hg 17) (subsetMinorSq_nonneg U {3} {0})
    have h₂ := mul_nonneg (hg 7) (subsetMinorSq_nonneg U {0, 2} {1, 3})
    have h₃ := mul_nonneg (hg 12) (subsetMinorSq_nonneg U {0, 3} {2, 3})
    have h₄ := mul_nonneg (hg 16) (subsetMinorSq_nonneg U {0, 2} {0, 2})
    have h₅ := mul_nonneg (hg 13) (subsetMinorSq_nonneg U {0, 2} {2, 3})
    have h₆ := mul_nonneg (hg 10) (subsetMinorSq_nonneg U {0, 1} {3, 1})
    apply sub_nonneg.mp
    rcases hcap hd with hh | hh
    · have h := four_two_budget_minor_nonneg_t5 (hg 10) (hg 13) hd.le hh U hU
      dsimp only at h
      rw [hgap 0 d (zero_add _)]
      norm_num [Fin.sum_univ_succ, t5MinorRows, t5MinorColumns, t5MixedWeights]
      nlinarith only [h, h₀, h₁, h₂, h₃, h₄]
    · have h := four_budget_minor_nonneg (hg 22) (hg 17) (hg 7) hd.le hh U hU
      dsimp only at h
      rw [hgap d 0 (add_zero _)]
      norm_num [Fin.sum_univ_succ, t5MinorRows, t5MinorColumns, t5MixedWeights]
      nlinarith only [h, h₃, h₄, h₅, h₆]

end

end MOC

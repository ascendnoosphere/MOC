import MOC.FourMatchingRelations
import MOC.FourMinorCertificate
import MOC.FourTwoBudgetMinor
import Mathlib.Tactic.LinearCombination

/-! The ordinary minor cone and mixed budget for paper case T15. -/

open BigOperators

namespace MOC

noncomputable section

/-- The six prescribed contacts of paper case T15. -/
def fourT15ContactIndices : Finset (Fin 24) := {1, 2, 3, 4, 6, 7}

private def t15GapProfile (g : Fin 24 → ℝ) : Fin 24 → ℝ :=
  ![g 0, 0, 0, 0, 0, g 0, 0, 0, g 8, g 9, g 10, -g 8 + g 9 + g 10, g 12, g 13,
    g 0 + g 8 + g 12, g 9 + g 13, g 16, -g 0 - g 8 + g 9 + g 16,
    g 0 + g 12 - g 16 + g 22, g 0 + g 13 - g 16 + g 22, g 0 + g 10 + g 12 - g 16 + g 22,
    g 0 - g 8 + g 9 + g 10 + g 13 - g 16 + g 22, g 22, -g 8 + g 9 + g 22]

set_option maxHeartbeats 2000000 in
private theorem t15GapProfile_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (hc : ∀ i ∈ fourT15ContactIndices, fourMatchingEvaluation m i = H) :
    let g := fun i => fourMatchingEvaluation m i - H
    ∀ i, g i = t15GapProfile g i := by
  have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide)
  have h3 := hc 3 (by decide)
  have h4 := hc 4 (by decide)
  have h6 := hc 6 (by decide)
  have h7 := hc 7 (by decide)
  simp [fourMatchingEvaluation] at h1 h2 h3 h4 h6 h7
  dsimp only
  intro i
  fin_cases i <;> simp [t15GapProfile, fourMatchingEvaluation] <;>
    linarith only [h1, h2, h3, h4, h6, h7]

private theorem t15SpectralGapProfile (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT15ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    ∀ i, g i = t15GapProfile g i := by
  let m₀ : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re
  have hm (i : Fin 24) : fourMatchingEvaluation m₀ i =
      (η * matchingProduct a b (fourPerm i).symm).re := fourMatchingEvaluation_spectral_real_part a b η i
  have h := t15GapProfile_of_contacts m₀ H (fun i hi => (hm i).trans (hc i hi))
  dsimp only at h ⊢
  simpa only [hm] using h

/-- The T15 contacts express the donor margins by two supported gaps. -/
theorem fourT15_gap_eleven_nineteen (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT15ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    let d := g 0 - g 16
    g 11 = g 10 + g 17 + d ∧ g 19 = g 13 + g 22 + d := by
  intro g d
  have hp : ∀ i, g i = t15GapProfile g i := t15SpectralGapProfile a b η H hc
  have h11 : g 11 = -g 8 + g 9 + g 10 := hp 11
  have h17 : g 17 = -g 0 - g 8 + g 9 + g 16 := hp 17
  have h19 : g 19 = g 0 + g 13 - g 16 + g 22 := hp 19
  dsimp only [d]
  constructor
  · linear_combination h11 - h17
  · linear_combination h19

private def t15MinorRows : Fin 13 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 3}, {0}, {0, 1}, {3}, {2}, {0, 1}, {0, 2}, {1}, {1, 2}, {1, 3}]

private def t15MinorColumns : Fin 13 → Finset (Fin 4) :=
  ![{3}, {2, 3}, {2, 3}, {2, 3}, {2}, {3, 1}, {0}, {0}, {1, 2}, {0, 2}, {1}, {2, 3}, {2, 1}]

private def t15MinorSupports : Fin 13 → Finset ℕ :=
  ![{18, 19, 20, 21, 22, 23}, {16, 17, 22, 23}, {13, 15, 19, 21}, {12, 14, 18, 20},
    {12, 13, 14, 15, 16, 17}, {10, 11, 20, 21}, {9, 11, 15, 17, 21, 23}, {8, 10, 14, 16, 20, 22},
    {8, 9, 14, 15}, {0, 5, 14, 16}, {0, 1, 14, 15, 20, 21}, {3, 5, 9, 11}, {1, 3, 20, 22}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem t15MinorSupports_spec (k : Fin 13) (i : Fin 24) :
    i.val ∈ t15MinorSupports k ↔ (t15MinorColumns k).map (fourPerm i).symm.toEmbedding = t15MinorRows k := by
  fin_cases k <;> fin_cases i <;> decide

private def t15MinorWeights (g : Fin 24 → ℝ) (u v : ℝ) : Fin 13 → ℝ :=
  let A := g 16 - g 0
  ![g 22 - A + u, A - g 8 - u + v, g 13 - u, g 12 - u, u, -g 8 + g 10 + v,
    g 9 - v, g 8 - v, v, g 0, 0, 0, 0]

private def t15MixedWeights (g : Fin 24 → ℝ) : Fin 13 → ℝ :=
  let d := g 0 - g 16
  ![g 22 + d, 0, g 13, g 12, 0, g 10, g 17, 0, g 8, g 16, d, d, -d]

set_option maxHeartbeats 2000000 in
private theorem t15GapProfile_eq_minorSum (g : Fin 24 → ℝ) (u v : ℝ) (i : Fin 24) :
    t15GapProfile g i = ∑ k, if i.val ∈ t15MinorSupports k then t15MinorWeights g u v k else 0 := by
  let rhs (n : ℕ) := ∑ k : Fin 13, if n ∈ t15MinorSupports k then t15MinorWeights g u v k else 0
  change t15GapProfile g i = rhs i.val
  fin_cases i
  case' «0» => change g 0 = rhs 0
  case' «1» => change 0 = rhs 1
  case' «2» => change 0 = rhs 2
  case' «3» => change 0 = rhs 3
  case' «4» => change 0 = rhs 4
  case' «5» => change g 0 = rhs 5
  case' «6» => change 0 = rhs 6
  case' «7» => change 0 = rhs 7
  case' «8» => change g 8 = rhs 8
  case' «9» => change g 9 = rhs 9
  case' «10» => change g 10 = rhs 10
  case' «11» => change -g 8 + g 9 + g 10 = rhs 11
  case' «12» => change g 12 = rhs 12
  case' «13» => change g 13 = rhs 13
  case' «14» => change g 0 + g 8 + g 12 = rhs 14
  case' «15» => change g 9 + g 13 = rhs 15
  case' «16» => change g 16 = rhs 16
  case' «17» => change -g 0 - g 8 + g 9 + g 16 = rhs 17
  case' «18» => change g 0 + g 12 - g 16 + g 22 = rhs 18
  case' «19» => change g 0 + g 13 - g 16 + g 22 = rhs 19
  case' «20» => change g 0 + g 10 + g 12 - g 16 + g 22 = rhs 20
  case' «21» => change g 0 - g 8 + g 9 + g 10 + g 13 - g 16 + g 22 = rhs 21
  case' «22» => change g 22 = rhs 22
  case' «23» => change -g 8 + g 9 + g 22 = rhs 23
  all_goals
    norm_num [rhs, t15MinorSupports, t15MinorWeights, Fin.sum_univ_succ, Matrix.cons_val] <;>
      (first | rfl | ring_nf <;> rfl)

set_option maxHeartbeats 2000000 in
private theorem t15GapProfile_eq_mixedSum (g : Fin 24 → ℝ)
    (hprofile : ∀ i, g i = t15GapProfile g i) (i : Fin 24) :
    g i = ∑ k, if i.val ∈ t15MinorSupports k then t15MixedWeights g k else 0 := by
  have h17 : g 17 = -g 0 - g 8 + g 9 + g 16 := hprofile 17
  let rhs (n : ℕ) := ∑ k : Fin 13, if n ∈ t15MinorSupports k then t15MixedWeights g k else 0
  change g i = rhs i.val
  rw [hprofile i]
  fin_cases i
  case' «0» => change g 0 = rhs 0
  case' «1» => change 0 = rhs 1
  case' «2» => change 0 = rhs 2
  case' «3» => change 0 = rhs 3
  case' «4» => change 0 = rhs 4
  case' «5» => change g 0 = rhs 5
  case' «6» => change 0 = rhs 6
  case' «7» => change 0 = rhs 7
  case' «8» => change g 8 = rhs 8
  case' «9» => change g 9 = rhs 9
  case' «10» => change g 10 = rhs 10
  case' «11» => change -g 8 + g 9 + g 10 = rhs 11
  case' «12» => change g 12 = rhs 12
  case' «13» => change g 13 = rhs 13
  case' «14» => change g 0 + g 8 + g 12 = rhs 14
  case' «15» => change g 9 + g 13 = rhs 15
  case' «16» => change g 16 = rhs 16
  case' «17» => change -g 0 - g 8 + g 9 + g 16 = rhs 17
  case' «18» => change g 0 + g 12 - g 16 + g 22 = rhs 18
  case' «19» => change g 0 + g 13 - g 16 + g 22 = rhs 19
  case' «20» => change g 0 + g 10 + g 12 - g 16 + g 22 = rhs 20
  case' «21» => change g 0 - g 8 + g 9 + g 10 + g 13 - g 16 + g 22 = rhs 21
  case' «22» => change g 22 = rhs 22
  case' «23» => change -g 8 + g 9 + g 22 = rhs 23
  all_goals
    norm_num [rhs, h17, t15MinorSupports, t15MixedWeights, Fin.sum_univ_succ, Matrix.cons_val] <;>
      (first | rfl | ring_nf <;> rfl)

private theorem t15_exists_nonnegative_weights (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hprofile : ∀ i, g i = t15GapProfile g i) (hA : 0 ≤ g 16 - g 0) :
    ∃ u v, ∀ k, 0 ≤ t15MinorWeights g u v k := by
  let A := g 16 - g 0
  let u := max 0 (A - g 22)
  let v := max 0 (max (g 8 - g 10) (g 8 + u - A))
  have hh (i : Fin 24) : 0 ≤ t15GapProfile g i := (hprofile i) ▸ hg i
  have h11 : 0 ≤ -g 8 + g 9 + g 10 := hh 11
  have h17 : 0 ≤ -g 0 - g 8 + g 9 + g 16 := hh 17
  have h18 : 0 ≤ g 0 + g 12 - g 16 + g 22 := hh 18
  have h19 : 0 ≤ g 0 + g 13 - g 16 + g 22 := hh 19
  have h23 : 0 ≤ -g 8 + g 9 + g 22 := hh 23
  have hu₀ : 0 ≤ u := le_max_left _ _
  have hu₁ : A - g 22 ≤ u := le_max_right _ _
  have huA : u ≤ A := max_le hA (sub_le_self _ (hg 22))
  have hu12 : u ≤ g 12 := max_le (hg 12) (by dsimp only [A]; linarith only [h18])
  have hu13 : u ≤ g 13 := max_le (hg 13) (by dsimp only [A]; linarith only [h19])
  have hv₀ : 0 ≤ v := le_max_left _ _
  have hv₁ : g 8 - g 10 ≤ v := (le_max_left _ _).trans (le_max_right _ _)
  have hv₂ : g 8 + u - A ≤ v := (le_max_right _ _).trans (le_max_right _ _)
  have hv8 : v ≤ g 8 := max_le (hg 8) (max_le (sub_le_self _ (hg 10)) (by linarith only [huA]))
  have hv9 : v ≤ g 9 := max_le (hg 9) (max_le (by linarith only [h11]) (by
    rcases le_total (A - g 22) 0 with h | h
    · dsimp only [u]; rw [max_eq_left h]; dsimp only [A]; linarith only [h17]
    · dsimp only [u]; rw [max_eq_right h]; linarith only [h23]))
  refine ⟨u, v, fun k => ?_⟩
  fin_cases k
  · change 0 ≤ (g 22 - A + u : ℝ)
    linarith only [hu₁]
  · change 0 ≤ (A - g 8 - u + v : ℝ)
    linarith only [hv₂]
  · change 0 ≤ (g 13 - u : ℝ)
    exact sub_nonneg.mpr hu13
  · change 0 ≤ (g 12 - u : ℝ)
    exact sub_nonneg.mpr hu12
  · change 0 ≤ (u : ℝ)
    exact hu₀
  · change 0 ≤ (-g 8 + g 10 + v : ℝ)
    linarith only [hv₁]
  · change 0 ≤ (g 9 - v : ℝ)
    exact sub_nonneg.mpr hv9
  · change 0 ≤ (g 8 - v : ℝ)
    exact sub_nonneg.mpr hv8
  · change 0 ≤ (v : ℝ)
    exact hv₀
  · change 0 ≤ (g 0 : ℝ)
    exact hg 0
  · change 0 ≤ (0 : ℝ)
    exact le_rfl
  · change 0 ≤ (0 : ℝ)
    exact le_rfl
  · change 0 ≤ (0 : ℝ)
    exact le_rfl

/-- The T15 inequality follows from the two donor bounds on the positive
mixed branch. A nonpositive mixed coefficient closes by ordinary minors. -/
theorem fourT15_support_of_budget (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT15ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hcap : let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      let d := g 0 - g 16
      0 < d → d ^ 2 ≤ g 10 * g 13) : H ≤ (η * determinantValue a b U).re := by
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  have hp : ∀ i, g i = t15GapProfile g i := t15SpectralGapProfile a b η H hc
  have h1 := hc 1 (by decide)
  by_cases hA : 0 ≤ g 16 - g 0
  · obtain ⟨u, v, hw⟩ := t15_exists_nonnegative_weights g hg hp hA
    refine four_support_of_minor_gap_decomposition a b η H U hU 1 h1
      t15MinorRows t15MinorColumns (t15MinorWeights g u v) hw (fun i => ?_)
    simp_rw [← t15MinorSupports_spec]
    exact (hp i).trans (t15GapProfile_eq_minorSum g u v i)
  · have hd : 0 < g 0 - g 16 := by linarith only [lt_of_not_ge hA]
    have h := four_two_budget_minor_nonneg_t5 (hg 10) (hg 13) hd.le (hcap hd) U hU
    dsimp only at h
    have hgap := four_gap_eq_minor_decomposition a b η H U hU 1 h1 t15MinorRows t15MinorColumns
      (t15MixedWeights g) (fun i => by simp_rw [← t15MinorSupports_spec]; exact t15GapProfile_eq_mixedSum g hp i)
    have h₀ := mul_nonneg (hg 22) (subsetMinorSq_nonneg U {0} {3})
    have h₁ := mul_nonneg (hg 17) (subsetMinorSq_nonneg U {3} {0})
    have h₂ := mul_nonneg (hg 8) (subsetMinorSq_nonneg U {0, 1} {1, 2})
    have h₃ := mul_nonneg (hg 12) (subsetMinorSq_nonneg U {0, 3} {2, 3})
    have h₄ := mul_nonneg (hg 16) (subsetMinorSq_nonneg U {0, 2} {0, 2})
    apply sub_nonneg.mp
    rw [hgap]
    norm_num [Fin.sum_univ_succ, t15MinorRows, t15MinorColumns, t15MixedWeights]
    nlinarith only [h, h₀, h₁, h₂, h₃, h₄]

end

end MOC

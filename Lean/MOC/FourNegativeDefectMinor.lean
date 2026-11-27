import MOC.FourMatchingRelations
import MOC.FourMinorCertificate
import MOC.FourTwoBudgetMinor
import Mathlib.Tactic.LinearCombination

/-! The exact minor cone and the two-budget branch for paper case negative-defect pattern. -/

open BigOperators

namespace MOC

noncomputable section

/-- The six prescribed contacts of paper case negative-defect pattern. -/
def fourNegativeDefectContactIndices : Finset (Fin 24) := {0, 1, 2, 3, 7, 8}

/-- The sole additional linear inequality for the negative-defect pattern ordinary minor cone. -/
def fourNegativeDefectMinorDefect (g : Fin 24 → ℝ) : ℝ := -g 4 + g 6 + g 10 - g 12 + g 13 + g 18

private def negativeDefectGapProfile (g : Fin 24 → ℝ) : Fin 24 → ℝ :=
  ![0, 0, 0, 0, g 4, g 4, g 6, 0, 0, g 9, g 10, g 6 + g 9 + g 10,
    g 12, g 13, -g 6 + g 12, g 9 + g 13, g 16, g 6 + g 9 + g 16, g 18,
    g 6 - g 12 + g 13 + g 18, -g 4 + g 10 + g 18,
    g 9 + fourNegativeDefectMinorDefect g, -g 4 + g 6 - g 12 + g 16 + g 18,
    -g 4 + g 6 + g 9 - g 12 + g 16 + g 18]

set_option maxHeartbeats 2000000 in
private theorem negativeDefectGapProfile_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (hc : ∀ i ∈ fourNegativeDefectContactIndices, fourMatchingEvaluation m i = H) :
    let g := fun i => fourMatchingEvaluation m i - H
    ∀ i, g i = negativeDefectGapProfile g i := by
  have h0 := hc 0 (by decide)
  have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide)
  have h3 := hc 3 (by decide)
  have h7 := hc 7 (by decide)
  have h8 := hc 8 (by decide)
  let g (i : Fin 24) := fourMatchingEvaluation m i - H
  change ∀ i, g i = negativeDefectGapProfile g i
  dsimp only [fourMatchingEvaluation, Matrix.cons_val] at h0 h1 h2 h3 h7 h8
  intro i
  fin_cases i
  · change g 0 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h0
  · change g 1 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1
  · change g 2 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h2
  · change g 3 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h3
  · change g 4 = g 4
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> ring
  · change g 5 = g 4
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h0 - h1 - h2 + h3
  · change g 6 = g 6
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> ring
  · change g 7 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h7
  · change g 8 = 0
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h8
  · change g 9 = g 9
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> ring
  · change g 10 = g 10
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> ring
  · change g 11 = g 6 + g 9 + g 10
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h7 - h8
  · change g 12 = g 12
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> ring
  · change g 13 = g 13
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> ring
  · change g 14 = -g 6 + g 12
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h0 - h2 + h8
  · change g 15 = g 9 + g 13
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1 - h3 - h7
  · change g 16 = g 16
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> ring
  · change g 17 = g 6 + g 9 + g 16
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h0 + h1 + h2 - h3 - h7 - h8
  · change g 18 = g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> ring
  · change g 19 = g 6 - g 12 + g 13 + g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h7
  · change g 20 = -g 4 + g 10 + g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1 - h7
  · change g 21 = g 9 + fourNegativeDefectMinorDefect g
    dsimp only [fourNegativeDefectMinorDefect, g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1 + h2 - h3 - 2 * h7 - h8
  · change g 22 = -g 4 + g 6 - g 12 + g 16 + g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h0 + h1 + h2 - h7
  · change g 23 = -g 4 + g 6 + g 9 - g 12 + g 16 + g 18
    dsimp only [g, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h0 + h1 + 2 * h2 - h3 - h7 - h8

private theorem negativeDefectSpectralGapProfile (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourNegativeDefectContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    ∀ i, g i = negativeDefectGapProfile g i := by
  let m₀ : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re
  have hm (i : Fin 24) : fourMatchingEvaluation m₀ i =
      (η * matchingProduct a b (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part a b η i
  have hp := negativeDefectGapProfile_of_contacts m₀ H (fun i hi => (hm i).trans (hc i hi))
  dsimp only at hp ⊢
  simpa only [hm] using hp

/-- The negative-defect pattern contacts express the gap at 21 by the gap at 9 and the minor defect. -/
theorem fourNegativeDefect_gap_twenty_one (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourNegativeDefectContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    g 21 = g 9 + fourNegativeDefectMinorDefect g := by
  simpa only [negativeDefectGapProfile, Matrix.cons_val] using negativeDefectSpectralGapProfile a b η H hc 21

private def negativeDefectMinorRows : Fin 13 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 3}, {0}, {0, 1}, {3}, {0, 2}, {0, 1}, {1},
    {2}, {2, 1}, {2, 3}]

private def negativeDefectMinorColumns : Fin 13 → Finset (Fin 4) :=
  ![{3}, {3, 2}, {2, 3}, {2, 3}, {2}, {1, 3}, {0}, {2, 1}, {0, 3}, {3},
    {1}, {3, 2}, {3, 1}]

private def negativeDefectMinorSupports : Fin 13 → Finset ℕ :=
  ![{18, 19, 20, 21, 22, 23}, {16, 17, 22, 23}, {13, 15, 19, 21}, {12, 14, 18, 20},
    {12, 13, 14, 15, 16, 17}, {10, 11, 20, 21}, {9, 11, 15, 17, 21, 23},
    {6, 11, 12, 17}, {4, 5, 18, 19}, {4, 5, 10, 11, 16, 17}, {2, 4, 12, 17, 18, 23},
    {3, 5, 9, 11}, {2, 3, 12, 13}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem negativeDefectMinorSupports_spec (k : Fin 13) (i : Fin 24) :
    i.val ∈ negativeDefectMinorSupports k ↔ (negativeDefectMinorColumns k).map (fourPerm i).symm.toEmbedding = negativeDefectMinorRows k := by
  fin_cases k <;> fin_cases i <;> decide

private def negativeDefectMinorWeights (g : Fin 24 → ℝ) (u v : ℝ) : Fin 13 → ℝ :=
  ![-g 4 + g 6 - g 12 + g 18 + u + v, g 16 - u - v, g 13 - u,
    -g 6 + g 12 - u, u, g 10 - v, g 9, g 6, g 4 - v, v, 0, 0, 0]

private def negativeDefectMixedWeights (g : Fin 24 → ℝ) : Fin 13 → ℝ :=
  let d := -fourNegativeDefectMinorDefect g
  ![0, g 22, 0, g 20, g 13 + d, 0, g 21, g 6, g 19, g 10, d, d, -d]

/-- The sum of the coefficients of the minors supported at each permutation. -/
private def negativeDefectMinorResponse (w : Fin 13 → ℝ) : Fin 24 → ℝ :=
  ![0,
    0,
    w 10 + w 12,
    w 11 + w 12,
    w 8 + w 9 + w 10,
    w 8 + w 9 + w 11,
    w 7,
    0,
    0,
    w 6 + w 11,
    w 5 + w 9,
    w 5 + w 6 + w 7 + w 9 + w 11,
    w 3 + w 4 + w 7 + w 10 + w 12,
    w 2 + w 4 + w 12,
    w 3 + w 4,
    w 2 + w 4 + w 6,
    w 1 + w 4 + w 9,
    w 1 + w 4 + w 6 + w 7 + w 9 + w 10,
    w 0 + w 3 + w 8 + w 10,
    w 0 + w 2 + w 8,
    w 0 + w 3 + w 5,
    w 0 + w 2 + w 5 + w 6,
    w 0 + w 1,
    w 0 + w 1 + w 6 + w 10]

set_option maxHeartbeats 2000000 in
private theorem negativeDefectMinorResponse_eq_sum (w : Fin 13 → ℝ) (i : Fin 24) :
    negativeDefectMinorResponse w i = ∑ k : Fin 13, if i.val ∈ negativeDefectMinorSupports k then w k else 0 := by
  let rhs (n : ℕ) := ∑ k : Fin 13, if n ∈ negativeDefectMinorSupports k then w k else 0
  change negativeDefectMinorResponse w i = rhs i.val
  fin_cases i
  case' «0» => change (0 : ℝ) = rhs 0
  case' «1» => change (0 : ℝ) = rhs 1
  case' «2» => change w 10 + w 12 = rhs 2
  case' «3» => change w 11 + w 12 = rhs 3
  case' «4» => change w 8 + w 9 + w 10 = rhs 4
  case' «5» => change w 8 + w 9 + w 11 = rhs 5
  case' «6» => change w 7 = rhs 6
  case' «7» => change (0 : ℝ) = rhs 7
  case' «8» => change (0 : ℝ) = rhs 8
  case' «9» => change w 6 + w 11 = rhs 9
  case' «10» => change w 5 + w 9 = rhs 10
  case' «11» => change w 5 + w 6 + w 7 + w 9 + w 11 = rhs 11
  case' «12» => change w 3 + w 4 + w 7 + w 10 + w 12 = rhs 12
  case' «13» => change w 2 + w 4 + w 12 = rhs 13
  case' «14» => change w 3 + w 4 = rhs 14
  case' «15» => change w 2 + w 4 + w 6 = rhs 15
  case' «16» => change w 1 + w 4 + w 9 = rhs 16
  case' «17» => change w 1 + w 4 + w 6 + w 7 + w 9 + w 10 = rhs 17
  case' «18» => change w 0 + w 3 + w 8 + w 10 = rhs 18
  case' «19» => change w 0 + w 2 + w 8 = rhs 19
  case' «20» => change w 0 + w 3 + w 5 = rhs 20
  case' «21» => change w 0 + w 2 + w 5 + w 6 = rhs 21
  case' «22» => change w 0 + w 1 = rhs 22
  case' «23» => change w 0 + w 1 + w 6 + w 10 = rhs 23
  all_goals
    norm_num [rhs, Fin.sum_univ_succ, negativeDefectMinorSupports, Matrix.cons_val, Fin.succ, Fin.val_mk] <;>
      simp -failIfUnchanged only [add_assoc] <;> rfl

private theorem negativeDefectGapProfile_eq_minorSum (g : Fin 24 → ℝ) (u v : ℝ) (i : Fin 24) :
    negativeDefectGapProfile g i = ∑ k, if i.val ∈ negativeDefectMinorSupports k then negativeDefectMinorWeights g u v k else 0 := by
  rw [← negativeDefectMinorResponse_eq_sum (negativeDefectMinorWeights g u v) i]
  fin_cases i
  case' «0» => change (0 : ℝ) = 0
  case' «1» => change (0 : ℝ) = 0
  case' «2» => change (0 : ℝ) = 0 + 0
  case' «3» => change (0 : ℝ) = 0 + 0
  case' «4» => change g 4 = (g 4 - v) + v + 0
  case' «5» => change g 4 = (g 4 - v) + v + 0
  case' «6» => change g 6 = g 6
  case' «7» => change (0 : ℝ) = 0
  case' «8» => change (0 : ℝ) = 0
  case' «9» => change g 9 = g 9 + 0
  case' «10» => change g 10 = (g 10 - v) + v
  case' «11» => change g 6 + g 9 + g 10 = (g 10 - v) + g 9 + g 6 + v + 0
  case' «12» => change g 12 = (-g 6 + g 12 - u) + u + g 6 + 0 + 0
  case' «13» => change g 13 = (g 13 - u) + u + 0
  case' «14» => change -g 6 + g 12 = (-g 6 + g 12 - u) + u
  case' «15» => change g 9 + g 13 = (g 13 - u) + u + g 9
  case' «16» => change g 16 = (g 16 - u - v) + u + v
  case' «17» => change g 6 + g 9 + g 16 = (g 16 - u - v) + u + g 9 + g 6 + v + 0
  case' «18» => change g 18 = (-g 4 + g 6 - g 12 + g 18 + u + v) + (-g 6 + g 12 - u) + (g 4 - v) + 0
  case' «19» => change g 6 - g 12 + g 13 + g 18 = (-g 4 + g 6 - g 12 + g 18 + u + v) + (g 13 - u) + (g 4 - v)
  case' «20» => change -g 4 + g 10 + g 18 = (-g 4 + g 6 - g 12 + g 18 + u + v) + (-g 6 + g 12 - u) + (g 10 - v)
  case' «21» => change g 9 + fourNegativeDefectMinorDefect g = (-g 4 + g 6 - g 12 + g 18 + u + v) + (g 13 - u) + (g 10 - v) + g 9
  case' «22» => change -g 4 + g 6 - g 12 + g 16 + g 18 = (-g 4 + g 6 - g 12 + g 18 + u + v) + (g 16 - u - v)
  case' «23» => change -g 4 + g 6 + g 9 - g 12 + g 16 + g 18 = (-g 4 + g 6 - g 12 + g 18 + u + v) + (g 16 - u - v) + g 9 + 0
  all_goals simp -failIfUnchanged only [fourNegativeDefectMinorDefect] <;> ring

private theorem negativeDefectGapProfile_eq_mixedSum (g : Fin 24 → ℝ)
    (hprofile : ∀ i, g i = negativeDefectGapProfile g i) (i : Fin 24) :
    g i = ∑ k, if i.val ∈ negativeDefectMinorSupports k then negativeDefectMixedWeights g k else 0 := by
  have h19 : g 19 = g 6 - g 12 + g 13 + g 18 := hprofile 19
  have h20 : g 20 = -g 4 + g 10 + g 18 := hprofile 20
  have h21 : g 21 = g 9 + fourNegativeDefectMinorDefect g := hprofile 21
  have h22 : g 22 = -g 4 + g 6 - g 12 + g 16 + g 18 := hprofile 22
  let d := -fourNegativeDefectMinorDefect g
  rw [hprofile i, ← negativeDefectMinorResponse_eq_sum (negativeDefectMixedWeights g) i]
  fin_cases i
  case' «0» => change (0 : ℝ) = 0
  case' «1» => change (0 : ℝ) = 0
  case' «2» => change (0 : ℝ) = d + (-d)
  case' «3» => change (0 : ℝ) = d + (-d)
  case' «4» => change g 4 = g 19 + g 10 + d
  case' «5» => change g 4 = g 19 + g 10 + d
  case' «6» => change g 6 = g 6
  case' «7» => change (0 : ℝ) = 0
  case' «8» => change (0 : ℝ) = 0
  case' «9» => change g 9 = g 21 + d
  case' «10» => change g 10 = 0 + g 10
  case' «11» => change g 6 + g 9 + g 10 = 0 + g 21 + g 6 + g 10 + d
  case' «12» => change g 12 = g 20 + (g 13 + d) + g 6 + d + (-d)
  case' «13» => change g 13 = 0 + (g 13 + d) + (-d)
  case' «14» => change -g 6 + g 12 = g 20 + (g 13 + d)
  case' «15» => change g 9 + g 13 = 0 + (g 13 + d) + g 21
  case' «16» => change g 16 = g 22 + (g 13 + d) + g 10
  case' «17» => change g 6 + g 9 + g 16 = g 22 + (g 13 + d) + g 21 + g 6 + g 10 + d
  case' «18» => change g 18 = 0 + g 20 + g 19 + d
  case' «19» => change g 6 - g 12 + g 13 + g 18 = 0 + 0 + g 19
  case' «20» => change -g 4 + g 10 + g 18 = 0 + g 20 + 0
  case' «21» => change g 9 + fourNegativeDefectMinorDefect g = 0 + 0 + 0 + g 21
  case' «22» => change -g 4 + g 6 - g 12 + g 16 + g 18 = 0 + g 22
  case' «23» => change -g 4 + g 6 + g 9 - g 12 + g 16 + g 18 = 0 + g 22 + g 21 + d
  all_goals simp -failIfUnchanged only [h19, h20, h21, h22, d, fourNegativeDefectMinorDefect] <;> ring

private theorem negativeDefect_exists_nonnegative_weights (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hprofile : ∀ i, g i = negativeDefectGapProfile g i) (hA : 0 ≤ fourNegativeDefectMinorDefect g) :
    ∃ u v, ∀ k, 0 ≤ negativeDefectMinorWeights g u v k := by
  let L := g 4 - g 6 + g 12 - g 18
  let K := max 0 L
  let U := min (g 13) (-g 6 + g 12)
  let V := min (g 10) (g 4)
  have h14 : g 14 = -g 6 + g 12 := by simpa [negativeDefectGapProfile] using hprofile 14
  have h19 : g 19 = g 6 - g 12 + g 13 + g 18 := by simpa [negativeDefectGapProfile] using hprofile 19
  have h20 : g 20 = -g 4 + g 10 + g 18 := by simpa [negativeDefectGapProfile] using hprofile 20
  have h22 : g 22 = g 16 - L := by
    rw [hprofile 22]
    simp [negativeDefectGapProfile, L] <;> ring
  have hU : 0 ≤ U := le_min (hg 13) (h14 ▸ hg 14)
  have hV : 0 ≤ V := le_min (hg 10) (hg 4)
  have hL : L ≤ U + V := by
    have h₁ : L - g 13 ≤ V := le_min
      (by dsimp only [L]; dsimp only [fourNegativeDefectMinorDefect] at hA; linarith only [hA])
      (by dsimp only [L]; linarith only [h19, hg 19])
    have h₂ : L - (-g 6 + g 12) ≤ V := le_min
      (by dsimp [L]; linarith only [h20, hg 20]) (by dsimp [L]; linarith only [hg 18])
    have h : L - V ≤ U := le_min (by linarith only [h₁]) (by linarith only [h₂])
    linarith only [h]
  have hK : K ≤ U + V := max_le (add_nonneg hU hV) hL
  have hK16 : K ≤ g 16 := max_le (hg 16) (by linarith only [h22, hg 22])
  let u := min K U
  let v := K - u
  have hu : 0 ≤ u := le_min (le_max_left _ _) hU
  have hv : 0 ≤ v := sub_nonneg.mpr (min_le_left _ _)
  have huU : u ≤ U := min_le_right _ _
  have hvV : v ≤ V := by
    rcases le_total K U with h | h
    · simpa [v, u, min_eq_left h] using hV
    · have he : u = U := min_eq_right h
      dsimp only [v]
      linarith only [he, hK]
  have hsum : u + v = K := by dsimp only [v]; ring
  have hLK : L ≤ K := le_max_right _ _
  have hu13 : u ≤ g 13 := huU.trans (min_le_left _ _)
  have hu14 : u ≤ -g 6 + g 12 := huU.trans (min_le_right _ _)
  have hv10 : v ≤ g 10 := hvV.trans (min_le_left _ _)
  have hv4 : v ≤ g 4 := hvV.trans (min_le_right _ _)
  refine ⟨u, v, fun k => ?_⟩
  fin_cases k
  · change 0 ≤ (-g 4 + g 6 - g 12 + g 18 + u + v : ℝ)
    dsimp only [L] at hLK
    linarith only [hsum, hLK]
  · change 0 ≤ (g 16 - u - v : ℝ)
    linarith only [hsum, hK16]
  · change 0 ≤ (g 13 - u : ℝ)
    exact sub_nonneg.mpr hu13
  · change 0 ≤ (-g 6 + g 12 - u : ℝ)
    exact sub_nonneg.mpr hu14
  · change 0 ≤ (u : ℝ)
    exact hu
  · change 0 ≤ (g 10 - v : ℝ)
    exact sub_nonneg.mpr hv10
  · change 0 ≤ (g 9 : ℝ)
    exact hg 9
  · change 0 ≤ (g 6 : ℝ)
    exact hg 6
  · change 0 ≤ (g 4 - v : ℝ)
    exact sub_nonneg.mpr hv4
  · change 0 ≤ (v : ℝ)
    exact hv
  · change 0 ≤ (0 : ℝ)
    exact le_rfl
  · change 0 ≤ (0 : ℝ)
    exact le_rfl
  · change 0 ≤ (0 : ℝ)
    exact le_rfl

/-- The negative-defect pattern support inequality follows from the sole two-budget condition on
the negative-defect branch. The other branch uses ordinary squared minors. -/
theorem fourNegativeDefect_support_of_budget (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourNegativeDefectContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hcap : let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      fourNegativeDefectMinorDefect g < 0 → (fourNegativeDefectMinorDefect g) ^ 2 ≤ g 6 * g 22) :
    H ≤ (η * determinantValue a b U).re := by
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  have hp' : ∀ i, g i = negativeDefectGapProfile g i := negativeDefectSpectralGapProfile a b η H hc
  have h0 := hc 0 (by decide)
  by_cases hA : 0 ≤ fourNegativeDefectMinorDefect g
  · obtain ⟨u, v, hw⟩ := negativeDefect_exists_nonnegative_weights g hg hp' hA
    refine four_support_of_minor_gap_decomposition a b η H U hU 0 h0
      negativeDefectMinorRows negativeDefectMinorColumns (negativeDefectMinorWeights g u v) hw (fun i => ?_)
    simp_rw [← negativeDefectMinorSupports_spec]
    exact (hp' i).trans (negativeDefectGapProfile_eq_minorSum g u v i)
  · let d := -fourNegativeDefectMinorDefect g
    have hd : 0 ≤ d := neg_nonneg.mpr (lt_of_not_ge hA).le
    have hcap' : d ^ 2 ≤ g 22 * g 6 := by
      calc
        d ^ 2 = (fourNegativeDefectMinorDefect g) ^ 2 := by dsimp only [d]; ring
        _ ≤ g 6 * g 22 := hcap (lt_of_not_ge hA)
        _ = _ := mul_comm _ _
    have hdecomp (i : Fin 24) : g i = ∑ k,
        if (negativeDefectMinorColumns k).map (fourPerm i).symm.toEmbedding = negativeDefectMinorRows k then
          negativeDefectMixedWeights g k else 0 := by
      simp_rw [← negativeDefectMinorSupports_spec]
      exact negativeDefectGapProfile_eq_mixedSum g hp' i
    have h := four_gap_eq_minor_decomposition a b η H U hU 0 h0
      negativeDefectMinorRows negativeDefectMinorColumns (negativeDefectMixedWeights g) hdecomp
    let m := subsetMinorSq U
    have hmixed := four_two_budget_minor_nonneg_negative_defect (hg 22) (hg 6) hd hcap' U hU
    change 0 ≤ g 22 * m {0, 1} {3, 2} + g 6 * m {0, 2} {2, 1} +
      d * (m {0} {2} + m {2} {1} + m {2, 1} {3, 2} - m {2, 3} {3, 1}) at hmixed
    have h₀ := mul_nonneg (hg 20) (subsetMinorSq_nonneg U {0, 3} {2, 3})
    have h₁ := mul_nonneg (hg 13) (subsetMinorSq_nonneg U {0} {2})
    have h₂ := mul_nonneg (hg 21) (subsetMinorSq_nonneg U {3} {0})
    have h₃ := mul_nonneg (hg 19) (subsetMinorSq_nonneg U {0, 1} {0, 3})
    have h₄ := mul_nonneg (hg 10) (subsetMinorSq_nonneg U {1} {3})
    apply sub_nonneg.mp
    rw [h]
    norm_num [Fin.sum_univ_succ, negativeDefectMinorRows, negativeDefectMinorColumns, negativeDefectMixedWeights]
    dsimp only [m] at hmixed
    dsimp only [d] at hmixed
    nlinarith only [hmixed, h₀, h₁, h₂, h₃, h₄]

end

end MOC

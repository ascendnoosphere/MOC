import MOC.FourMatchingRelations
import MOC.FourMinorCertificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! The ordinary-minor certificate for paper case T7. -/

namespace MOC

open BigOperators

noncomputable section

/-- The six contacts of paper case T7 in lexicographic order. -/
def fourT7ContactIndices : Finset (Fin 24) := {0, 1, 2, 4, 7, 8}

private def t7MinorRows : Fin 10 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 3}, {0}, {0, 1}, {3}, {0, 2}, {3}, {0, 3}]

private def t7MinorColumns : Fin 10 → Finset (Fin 4) :=
  ![{3}, {2, 3}, {2, 3}, {2, 3}, {2}, {1, 3}, {0}, {1, 2}, {1}, {0, 1}]

private def t7MinorSupport : Fin 10 → Finset ℕ :=
  ![{18, 19, 20, 21, 22, 23}, {16, 17, 22, 23}, {13, 15, 19, 21}, {12, 14, 18, 20}, {12, 13, 14, 15, 16, 17}, {10, 11, 20, 21}, {9, 11, 15, 17, 21, 23}, {6, 11, 12, 17}, {3, 5, 13, 16, 19, 22}, {3, 5, 9, 11}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem t7MinorSupport_spec (k : Fin 10) (i : Fin 24) :
    i.val ∈ t7MinorSupport k ↔ (t7MinorColumns k).map (fourPerm i).symm.toEmbedding =
      t7MinorRows k := by
  fin_cases k <;> fin_cases i <;> decide

private def t7MinorWeights (g : Fin 24 → ℝ) (x y : ℝ) : Fin 10 → ℝ :=
  ![-g 12 + g 18 + g 6 + x,
    g 16 - g 3 - x + y,
    g 13 - g 3 - x + y,
    g 12 - g 6 - x,
    x,
    g 10,
    g 9 - y,
    g 6,
    g 3 - y,
    y]

private def t7GapProfile (g : Fin 24 → ℝ) : Fin 24 → ℝ :=
  ![0,
    0,
    0,
    g 3,
    0,
    g 3,
    g 6,
    0,
    0,
    g 9,
    g 10,
    g 10 + g 6 + g 9,
    g 12,
    g 13,
    g 12 - g 6,
    g 13 - g 3 + g 9,
    g 16,
    g 16 - g 3 + g 6 + g 9,
    g 18,
    -g 12 + g 13 + g 18 + g 6,
    g 10 + g 18,
    g 10 - g 12 + g 13 + g 18 - g 3 + g 6 + g 9,
    -g 12 + g 16 + g 18 + g 6,
    -g 12 + g 16 + g 18 - g 3 + g 6 + g 9]

set_option maxHeartbeats 3000000 in
private theorem t7GapProfile_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (h0 : fourMatchingEvaluation m 0 = H) (h1 : fourMatchingEvaluation m 1 = H)
    (h2 : fourMatchingEvaluation m 2 = H) (h4 : fourMatchingEvaluation m 4 = H)
    (h7 : fourMatchingEvaluation m 7 = H) (h8 : fourMatchingEvaluation m 8 = H)
    (i : Fin 24) :
    let g := fun j => fourMatchingEvaluation m j - H
    g i = t7GapProfile g i := by
  let g (j : Fin 24) := fourMatchingEvaluation m j - H
  change g i = t7GapProfile g i
  dsimp only [fourMatchingEvaluation, Matrix.cons_val] at h0 h1 h2 h4 h7 h8
  fin_cases i
  · change g 0 = t7GapProfile g 0
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h0
  · change g 1 = t7GapProfile g 1
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1
  · change g 2 = t7GapProfile g 2
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h2
  · change g 3 = t7GapProfile g 3
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 4 = t7GapProfile g 4
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h4
  · change g 5 = t7GapProfile g 5
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h0 - h1 - h2 + h4
  · change g 6 = t7GapProfile g 6
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 7 = t7GapProfile g 7
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h7
  · change g 8 = t7GapProfile g 8
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h8
  · change g 9 = t7GapProfile g 9
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 10 = t7GapProfile g 10
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 11 = t7GapProfile g 11
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h7 - h8
  · change g 12 = t7GapProfile g 12
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 13 = t7GapProfile g 13
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 14 = t7GapProfile g 14
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h0 - h2 + h8
  · change g 15 = t7GapProfile g 15
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1 - h7
  · change g 16 = t7GapProfile g 16
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 17 = t7GapProfile g 17
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h0 + h1 + h2 - h7 - h8
  · change g 18 = t7GapProfile g 18
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 19 = t7GapProfile g 19
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h7
  · change g 20 = t7GapProfile g 20
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1 - h4 - h7
  · change g 21 = t7GapProfile g 21
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1 + h2 - h4 - 2 * h7 - h8
  · change g 22 = t7GapProfile g 22
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h0 + h1 + h2 - h4 - h7
  · change g 23 = t7GapProfile g 23
    dsimp only [g, t7GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h0 + h1 + 2 * h2 - h4 - h7 - h8

set_option maxHeartbeats 3000000 in
private theorem t7GapProfile_eq_minorSum (g : Fin 24 → ℝ) (x y : ℝ) (i : Fin 24) :
    t7GapProfile g i = ∑ k : Fin 10, if i.val ∈ t7MinorSupport k then
      t7MinorWeights g x y k else 0 := by
  let rhs (i : ℕ) := ∑ k : Fin 10, if i ∈ t7MinorSupport k then t7MinorWeights g x y k else 0
  change t7GapProfile g i = rhs i.val
  fin_cases i
  case' «0» => change 0 = rhs 0
  case' «1» => change 0 = rhs 1
  case' «2» => change 0 = rhs 2
  case' «3» => change g 3 = rhs 3
  case' «4» => change 0 = rhs 4
  case' «5» => change g 3 = rhs 5
  case' «6» => change g 6 = rhs 6
  case' «7» => change 0 = rhs 7
  case' «8» => change 0 = rhs 8
  case' «9» => change g 9 = rhs 9
  case' «10» => change g 10 = rhs 10
  case' «11» => change g 10 + g 6 + g 9 = rhs 11
  case' «12» => change g 12 = rhs 12
  case' «13» => change g 13 = rhs 13
  case' «14» => change g 12 - g 6 = rhs 14
  case' «15» => change g 13 - g 3 + g 9 = rhs 15
  case' «16» => change g 16 = rhs 16
  case' «17» => change g 16 - g 3 + g 6 + g 9 = rhs 17
  case' «18» => change g 18 = rhs 18
  case' «19» => change -g 12 + g 13 + g 18 + g 6 = rhs 19
  case' «20» => change g 10 + g 18 = rhs 20
  case' «21» => change g 10 - g 12 + g 13 + g 18 - g 3 + g 6 + g 9 = rhs 21
  case' «22» => change -g 12 + g 16 + g 18 + g 6 = rhs 22
  case' «23» => change -g 12 + g 16 + g 18 - g 3 + g 6 + g 9 = rhs 23
  all_goals
    norm_num [rhs, Fin.sum_univ_succ, t7MinorSupport,
      t7MinorWeights, Matrix.cons_val] <;> ring

private theorem t7_minorWeights_nonneg (g : Fin 24 → ℝ) (hn : ∀ i, 0 ≤ g i)
    (hprofile : ∀ i, g i = t7GapProfile g i)
    (hA : 0 ≤ g 9 + g 16 - g 3) (hB : 0 ≤ g 9 + g 19 - g 3) :
    let x := max 0 (g 12 - g 18 - g 6)
    let y := min (g 3) (g 9)
    ∀ k, 0 ≤ t7MinorWeights g x y k := by
  let x := max 0 (g 12 - g 18 - g 6)
  let y := min (g 3) (g 9)
  have hx : 0 ≤ x := le_max_left _ _
  have hxlow : g 12 - g 18 - g 6 ≤ x := le_max_right _ _
  have hy : 0 ≤ y := le_min (hn 3) (hn 9)
  have hy3 : y ≤ g 3 := min_le_left _ _
  have hy9 : y ≤ g 9 := min_le_right _ _
  have h14 : 0 ≤ g 12 - g 6 := by simpa only [hprofile 14, t7GapProfile] using hn 14
  have h15 : 0 ≤ g 13 - g 3 + g 9 := by simpa only [hprofile 15, t7GapProfile] using hn 15
  have h19 : 0 ≤ -g 12 + g 13 + g 18 + g 6 := by
    simpa only [hprofile 19, t7GapProfile] using hn 19
  have h22 : 0 ≤ -g 12 + g 16 + g 18 + g 6 := by
    simpa only [hprofile 22, t7GapProfile] using hn 22
  have h23 : 0 ≤ -g 12 + g 16 + g 18 - g 3 + g 6 + g 9 := by
    simpa only [hprofile 23, t7GapProfile] using hn 23
  have hB' : 0 ≤ g 9 + (-g 12 + g 13 + g 18 + g 6) - g 3 := by
    simpa only [hprofile 19, t7GapProfile] using hB
  have hx12 : x ≤ g 12 - g 6 := max_le h14 (by linarith only [hn 18])
  have hx16 : x ≤ g 16 - g 3 + y := by
    dsimp only [y]
    rcases le_total (g 3) (g 9) with h | h
    · rw [min_eq_left h, sub_add_cancel]
      exact max_le (hn 16) (by linarith only [h22])
    · rw [min_eq_right h]
      exact max_le (by linarith only [hA]) (by linarith only [h23])
  have hx13 : x ≤ g 13 - g 3 + y := by
    dsimp only [y]
    rcases le_total (g 3) (g 9) with h | h
    · rw [min_eq_left h, sub_add_cancel]
      exact max_le (hn 13) (by linarith only [h19])
    · rw [min_eq_right h]
      exact max_le h15 (by linarith only [hB'])
  change ∀ k : Fin 10, 0 ≤ t7MinorWeights g x y k
  intro k
  fin_cases k
  case' «0» => change 0 ≤ -g 12 + g 18 + g 6 + x
  case' «1» => change 0 ≤ g 16 - g 3 - x + y
  case' «2» => change 0 ≤ g 13 - g 3 - x + y
  case' «3» => change 0 ≤ g 12 - g 6 - x
  case' «4» => change 0 ≤ x
  case' «5» => change 0 ≤ g 10
  case' «6» => change 0 ≤ g 9 - y
  case' «7» => change 0 ≤ g 6
  case' «8» => change 0 ≤ g 3 - y
  case' «9» => change 0 ≤ y
  all_goals linarith only [hx, hxlow, hy, hy3, hy9, hx12, hx16, hx13, hn 10, hn 6]

/-- Two extra real inequalities complete the ordinary-minor certificate for T7.
This statement isolates the spectral part of the case from the finite linear algebra. -/
theorem fourT7_support_of_two_inequalities (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT7ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    0 ≤ g 9 + g 16 - g 3 → 0 ≤ g 9 + g 19 - g 3 → H ≤ (η * determinantValue a b U).re := by
  let m : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  change 0 ≤ g 9 + g 16 - g 3 → 0 ≤ g 9 + g 19 - g 3 → _
  intro hA hB
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct a b (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part a b η i
  have hcontact (i : Fin 24) (hi : i ∈ fourT7ContactIndices) : fourMatchingEvaluation m i = H :=
    (hm i).trans (hc i hi)
  have hp (i : Fin 24) : g i = t7GapProfile g i := by
    have h := t7GapProfile_of_contacts m H (hcontact 0 (by decide)) (hcontact 1 (by decide))
      (hcontact 2 (by decide)) (hcontact 4 (by decide)) (hcontact 7 (by decide))
      (hcontact 8 (by decide)) i
    simpa only [hm, g] using h
  let x := max 0 (g 12 - g 18 - g 6)
  let y := min (g 3) (g 9)
  have hw : ∀ k, 0 ≤ t7MinorWeights g x y k :=
    t7_minorWeights_nonneg g (fun i => sub_nonneg.mpr (hn i)) hp hA hB
  apply four_support_of_minor_gap_decomposition a b η H U hU 0 (hc 0 (by decide))
    t7MinorRows t7MinorColumns (t7MinorWeights g x y) hw
  intro i
  change g i = _
  simp only [← t7MinorSupport_spec]
  exact (hp i).trans (t7GapProfile_eq_minorSum g x y i)

private theorem t7_interpolation_nonneg (h k l s : ℝ)
    (hD : (h - k) / (k - 1) < 0)
    (hN : 0 < h * (k - l - 1) / (h - k))
    (hq : 0 < s / (h - k)) (hP : 0 < (k + l * s) / (h - k))
    (h9 : 0 ≤ 1 + s / (h - k) * (h - l - 1)) :
    0 ≤ h - l - 1 := by
  let D := h - k
  let W := -(h - l - 1)
  let q := s / D
  let α := h * k - h * l - k
  by_contra! not_nonneg
  have hDne : D ≠ 0 := (div_neg_iff.mp hD).elim (fun h => h.1.ne') (fun h => h.1.ne)
  have hk : k / D < 0 := by
    rcases div_neg_iff.mp hD with hDpos | hDneg
    · have hn : k - l - 1 < 0 := by linarith only [hDpos.1, not_nonneg]
      have hh : h * (k - l - 1) > 0 := (div_pos_iff_of_pos_right hDpos.1).mp hN
      have hhneg : h < 0 := by
        by_contra! hnonneg
        exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hnonneg hn.le)) hh
      exact div_neg_of_neg_of_pos (by linarith only [hhneg, hDpos.1]) hDpos.1
    · exact div_neg_of_pos_of_neg (by linarith only [hDneg.2]) hDneg.1
  have hα : 0 < α / D := by
    have he : α / D = 1 + h * (k - l - 1) / D := by
      dsimp only [α]
      field_simp [hDne] <;> dsimp only [D] <;> ring
    rw [he]
    exact add_pos zero_lt_one hN
  have he : (k + l * s) / D = (1 - q * W) * (k / D) - q * (α / D) := by
    dsimp only [q, W, α]
    field_simp [hDne] <;> dsimp only [D] <;> ring
  have hW : 0 ≤ 1 - q * W := by
    dsimp only [q, W, D]
    rw [mul_neg, sub_neg_eq_add]
    exact h9
  have hright := sub_neg_of_lt
    ((mul_nonpos_of_nonneg_of_nonpos hW hk.le).trans_lt (mul_pos hq hα))
  exact (not_lt_of_ge hP.le) (he.trans_lt hright)

/-- On the T7 sign chart, the interpolation kernels imply the two real
inequalities needed by the squared-minor certificate. -/
theorem fourT7_support_of_interpolation_kernels (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT7ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (h k l s : ℝ)
    (hD : (h - k) / (k - 1) < 0)
    (hN : 0 < h * (k - l - 1) / (h - k))
    (hq : 0 < s / (h - k)) (hP : 0 < (k + l * s) / (h - k)) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    g 9 = (1 + s / (h - k) * (h - l - 1)) * g 3 →
      H ≤ (η * determinantValue a b U).re := by
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  change g 9 = (1 + s / (h - k) * (h - l - 1)) * g 3 → _
  intro he
  have hgi (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  have h93 : g 3 ≤ g 9 := by
    rcases eq_or_lt_of_le (hgi 3) with hz | hpos
    · rw [← hz]
      exact hgi 9
    · have hgap : 0 ≤ (1 + s / (h - k) * (h - l - 1)) * g 3 := he ▸ hgi 9
      have h9 := nonneg_of_mul_nonneg_left hgap hpos
      have hm := t7_interpolation_nonneg h k l s hD hN hq hP h9
      have hp := mul_nonneg hq.le hm
      rw [he, add_mul, one_mul]
      linarith only [mul_nonneg hp hpos.le]
  apply fourT7_support_of_two_inequalities a b η H hn hc U hU
  · change 0 ≤ g 9 + g 16 - g 3
    linarith only [h93, hgi 16]
  · change 0 ≤ g 9 + g 19 - g 3
    linarith only [h93, hgi 19]

end

end MOC

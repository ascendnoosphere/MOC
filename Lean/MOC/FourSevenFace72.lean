import MOC.FourBudgetMinor
import MOC.FourMatchingRelations
import MOC.FourMinorCertificate

/-! The ordinary and four-budget squared-minor certificates for face 72. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The seven contact indices of face 72 in lexicographic order. -/
def fourSevenFace72ContactIndices : Finset (Fin 24) := {3, 4, 8, 9, 10, 12, 13}

/-- The mixed coefficient of the face-72 matching gap. -/
def fourSevenFace72Mixed (g : Fin 24 → ℝ) : ℝ :=
  -g 0 + g 1 + g 2 + g 6 - g 7

private def face72MinorRows : Fin 7 → Finset (Fin 4) :=
  ![{0}, {1}, {2}, {0, 1}, {0, 1}, {0, 2}, {0, 3}]

private def face72MinorColumns : Fin 7 → Finset (Fin 4) :=
  ![{3}, {1}, {2}, {0, 1}, {2, 3}, {0, 2}, {0, 3}]

private def face72MinorSupports : Fin 7 → Finset ℕ :=
  ![{18, 19, 20, 21, 22, 23}, {0, 1, 14, 15, 20, 21}, {0, 5, 6, 11, 19, 21},
    {0, 1, 6, 7}, {16, 17, 22, 23}, {0, 5, 14, 16}, {0, 2, 21, 23}]

private def face72MinorWeights (g : Fin 24 → ℝ) : Fin 7 → ℝ :=
  ![g 18, g 15, g 11, g 7, g 17, -fourSevenFace72Mixed g, g 2]

private def face72MinorResponse (w : Fin 7 → ℝ) : Fin 24 → ℝ :=
  ![w 1 + w 2 + w 3 + w 5 + w 6, w 1 + w 3, w 6, 0, 0, w 2 + w 5,
    w 2 + w 3, w 3, 0, 0, 0, w 2, 0, 0, w 1 + w 5, w 1, w 4 + w 5,
    w 4, w 0, w 0 + w 2, w 0 + w 1, w 0 + w 1 + w 2 + w 6,
    w 0 + w 4, w 0 + w 4 + w 6]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem face72MinorSupports_spec (k : Fin 7) (i : Fin 24) :
    i.val ∈ face72MinorSupports k ↔
      (face72MinorColumns k).map (fourPerm i).symm.toEmbedding = face72MinorRows k := by
  fin_cases k <;> fin_cases i <;> decide

set_option maxHeartbeats 2000000 in
private theorem face72MinorResponse_eq_sum (w : Fin 7 → ℝ) (i : Fin 24) :
    face72MinorResponse w i = ∑ k : Fin 7, if i.val ∈ face72MinorSupports k then w k else 0 := by
  let rhs (n : ℕ) := ∑ k : Fin 7, if n ∈ face72MinorSupports k then w k else 0
  change face72MinorResponse w i = rhs i.val
  fin_cases i
  case' «0» => change w 1 + w 2 + w 3 + w 5 + w 6 = rhs 0
  case' «1» => change w 1 + w 3 = rhs 1
  case' «2» => change w 6 = rhs 2
  case' «3» => change (0 : ℝ) = rhs 3
  case' «4» => change (0 : ℝ) = rhs 4
  case' «5» => change w 2 + w 5 = rhs 5
  case' «6» => change w 2 + w 3 = rhs 6
  case' «7» => change w 3 = rhs 7
  case' «8» => change (0 : ℝ) = rhs 8
  case' «9» => change (0 : ℝ) = rhs 9
  case' «10» => change (0 : ℝ) = rhs 10
  case' «11» => change w 2 = rhs 11
  case' «12» => change (0 : ℝ) = rhs 12
  case' «13» => change (0 : ℝ) = rhs 13
  case' «14» => change w 1 + w 5 = rhs 14
  case' «15» => change w 1 = rhs 15
  case' «16» => change w 4 + w 5 = rhs 16
  case' «17» => change w 4 = rhs 17
  case' «18» => change w 0 = rhs 18
  case' «19» => change w 0 + w 2 = rhs 19
  case' «20» => change w 0 + w 1 = rhs 20
  case' «21» => change w 0 + w 1 + w 2 + w 6 = rhs 21
  case' «22» => change w 0 + w 4 = rhs 22
  case' «23» => change w 0 + w 4 + w 6 = rhs 23
  all_goals
    norm_num [rhs, Fin.sum_univ_succ, face72MinorSupports, Matrix.cons_val, Fin.succ, Fin.val_mk] <;>
      first | rfl | ring_nf <;> rfl

set_option maxHeartbeats 2000000 in
private theorem face72MinorResponse_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, fourMatchingEvaluation m i = H) :
    let g := fun i => fourMatchingEvaluation m i - H
    ∀ i, g i = face72MinorResponse (face72MinorWeights g) i := by
  have h3 := sub_eq_zero.mpr (hc 3 (by decide))
  have h4 := sub_eq_zero.mpr (hc 4 (by decide))
  have h8 := sub_eq_zero.mpr (hc 8 (by decide))
  have h9 := sub_eq_zero.mpr (hc 9 (by decide))
  have h10 := sub_eq_zero.mpr (hc 10 (by decide))
  have h12 := sub_eq_zero.mpr (hc 12 (by decide))
  have h13 := sub_eq_zero.mpr (hc 13 (by decide))
  simp only [fourMatchingEvaluation, Matrix.cons_val] at h3 h4 h8 h9 h10 h12 h13
  dsimp only
  intro i
  fin_cases i <;> simp [face72MinorResponse, face72MinorWeights, fourSevenFace72Mixed,
    fourMatchingEvaluation]
  · linear_combination h3 + h8 - 2 * h9 - h10 - h13
  · linear_combination h3 - h9 - h13
  · linear_combination h3
  · linear_combination h4
  · linear_combination h3 + h4 + h8 - h9 - h10
  · linear_combination h8 - h9 - h10
  · linear_combination h8
  · linear_combination h9
  · linear_combination h10
  · linear_combination h12
  · linear_combination h13
  · linear_combination h3 + h8 - h9 + h12 - h13
  · linear_combination h3 + h8 - h9
  · linear_combination h8 - h9 - h10 - h12 + h13
  · linear_combination h3 - h4 - h9 + h10 - h13
  · linear_combination -h4 - h9 - h12
  · linear_combination h3 - h4 + h8 - h9 - h12
  · linear_combination -h4 - h12

private theorem face72SpectralMinorResponse (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    ∀ i, g i = face72MinorResponse (face72MinorWeights g) i := by
  let m : Fin 14 → ℝ := fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re
  have hm (i : Fin 24) : fourMatchingEvaluation m i = (η * matchingProduct a b (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part a b η i
  have h := face72MinorResponse_of_contacts m H (fun i hi => (hm i).trans (hc i hi))
  dsimp only at h ⊢
  simpa only [hm] using h

/-- Removing the mixed contribution from the three affected weights
recovers the gaps at 14, 5, and 16. -/
theorem fourSevenFace72_donor_gaps (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    let d := fourSevenFace72Mixed g
    g 15 = g 14 + d ∧ g 11 = g 5 + d ∧ g 17 = g 16 + d := by
  intro g d
  have hp : ∀ i, g i = face72MinorResponse (face72MinorWeights g) i :=
    face72SpectralMinorResponse a b η H hc
  have h14 := hp 14
  have h5 := hp 5
  have h16 := hp 16
  change g 14 = g 15 + -d at h14
  change g 5 = g 11 + -d at h5
  change g 16 = g 17 + -d at h16
  exact ⟨by linarith only [h14], by linarith only [h5], by linarith only [h16]⟩

private def face72CubicLift (A B C D E F t H : ℝ) : Fin 14 → ℝ :=
  ![F - t, t, -A - F, -B - t, B + t, t, D + E, -C - t, C + t,
    B + C - E + t, -B - t, -C - t, -F, A + E + F + H + t]

set_option maxHeartbeats 2000000 in
/-- The spectral matching cubic restricted to the seven face-72 contacts. -/
theorem fourSevenFace72_cubic (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    let d := fourSevenFace72Mixed g
    (g 7 * g 16 + H * (g 7 + g 16)) * (g 2 - d) =
      (g 18 + g 16 + d) * (g 14 + d) * (g 5 + d) + g 7 * d * (g 18 + d) + H * d ^ 2 := by
  intro g d
  have hp : ∀ i, g i = face72MinorResponse (face72MinorWeights g) i :=
    face72SpectralMinorResponse a b η H hc
  have he (i : Fin 24) : H + face72MinorResponse (face72MinorWeights g) i =
      (η * matchingProduct a b (fourPerm i).symm).re := by
    rw [← hp i]
    dsimp only [g]
    ring
  obtain ⟨h15, h11, h17⟩ := fourSevenFace72_donor_gaps a b η H hc
  change g 15 = g 14 + d at h15
  change g 11 = g 5 + d at h11
  change g 17 = g 16 + d at h17
  have hd : fourSevenFace72Mixed g = d := rfl
  let m := face72CubicLift (g 18) (g 14) (g 5) (g 7) (g 16) (g 2) d H
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct a b (fourPerm i).symm).re := by
    rw [← he i]
    fin_cases i <;> simp [m, face72CubicLift, fourMatchingEvaluation, face72MinorResponse,
      face72MinorWeights, hd, h15, h11, h17] <;> ring
  have h := fourMatchingCubic_zero_of_evaluation_eq_spectral a b η m hm
  simp [m, face72CubicLift, fourMatchingCubic] at h
  linear_combination h

/-- The real determinant gap at the seven contacts is an exact signed sum
of seven squared minors. -/
theorem fourSevenFace72_gap_eq_minors (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    let m := subsetMinorSq U
    (η * determinantValue a b U).re - H =
      g 18 * m {0} {3} + g 15 * m {1} {1} + g 11 * m {2} {2} + g 7 * m {0, 1} {0, 1} +
        g 17 * m {0, 1} {2, 3} + (-fourSevenFace72Mixed g) * m {0, 2} {0, 2} +
        g 2 * m {0, 3} {0, 3} := by
  intro g m
  have hg := face72SpectralMinorResponse a b η H hc
  have h := four_gap_eq_minor_decomposition a b η H U hU 3 (hc 3 (by decide))
    face72MinorRows face72MinorColumns (face72MinorWeights g) (fun i => by
      simp_rw [← face72MinorSupports_spec]
      exact (hg i).trans (face72MinorResponse_eq_sum _ i))
  rw [h]
  norm_num [Fin.sum_univ_succ, face72MinorRows, face72MinorColumns, face72MinorWeights,
    Matrix.cons_val, Fin.succ, Fin.val_mk] <;> first | rfl | ring_nf <;> rfl

/-- The four-budget inequality transported to the face-72 minors. -/
theorem fourSevenFace72_budget_minor_nonneg {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcap : d ^ 2 * (a + b + c + d) ≤ a * b * (c - d))
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let m := subsetMinorSq U
    0 ≤ a * m {1} {1} + b * m {2} {2} + c * m {0, 1} {0, 1} +
      d * (m {1} {1} + m {2} {2} + m {0, 1} {2, 3} - m {0, 2} {0, 2}) := by
  let r := fourPerm 10
  let s := fourPerm 13
  let V := U.submatrix r s
  have hV : IsUnitary V := unitary_reindex r s hU
  have hsingle (i j : Fin 4) :
      subsetMinorSq V {i} {j} = subsetMinorSq U {r i} {s j} := by
    rw [subsetMinorSq_singleton V hV, subsetMinorSq_singleton U hU] <;> rfl
  have hpair {i k j l : Fin 4} (hi : i ≠ k) (hj : j ≠ l) :
      subsetMinorSq V {i, k} {j, l} = subsetMinorSq U {r i, r k} {s j, s l} := by
    rw [subsetMinorSq_pair V hV hi hj, subsetMinorSq_pair U hU
      (fun h => hi (r.injective h)) (fun h => hj (s.injective h))] <;> rfl
  have hm₁ : subsetMinorSq V {0} {3} = subsetMinorSq U {1} {1} := by
    rw [hsingle, show r 0 = 1 by decide +kernel, show s 3 = 1 by decide +kernel]
  have hm₂ : subsetMinorSq V {3} {0} = subsetMinorSq U {2} {2} := by
    rw [hsingle, show r 3 = 2 by decide +kernel, show s 0 = 2 by decide +kernel]
  have hm₃ : subsetMinorSq V {0, 2} {1, 3} = subsetMinorSq U {0, 1} {0, 1} := by
    rw [hpair (by decide) (by decide),
      show ({r 0, r 2} : Finset (Fin 4)) = {0, 1} by decide +kernel,
      show ({s 1, s 3} : Finset (Fin 4)) = {0, 1} by decide +kernel]
  have hm₄ : subsetMinorSq V {0, 2} {0, 2} = subsetMinorSq U {0, 1} {2, 3} := by
    rw [hpair (by decide) (by decide),
      show ({r 0, r 2} : Finset (Fin 4)) = {0, 1} by decide +kernel,
      show ({s 0, s 2} : Finset (Fin 4)) = {2, 3} by decide +kernel]
  have hm₅ : subsetMinorSq V {0, 1} {2, 3} = subsetMinorSq U {0, 2} {0, 2} := by
    rw [hpair (by decide) (by decide),
      ← subsetMinorSq_compl U hU {0, 2} {0, 2},
      show ({r 0, r 1} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4))ᶜ by decide +kernel,
      show ({s 2, s 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4))ᶜ by decide +kernel]
  have h := four_budget_minor_nonneg ha hb hc hd hcap V hV
  dsimp only at h ⊢
  rwa [hm₁, hm₂, hm₃, hm₄, hm₅] at h

/-- Face 72 has the lower support bound when the mixed coefficient is
nonpositive or the three positive donors satisfy the four-budget capacity. -/
theorem fourSevenFace72_support_of_budget (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hcap :
      let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      let d := fourSevenFace72Mixed g
      0 < d → d ^ 2 * (g 14 + g 5 + g 7 + d) ≤ g 14 * g 5 * (g 7 - d)) :
    H ≤ (η * determinantValue a b U).re := by
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  let d := fourSevenFace72Mixed g
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  have hm (I J : Finset (Fin 4)) := subsetMinorSq_nonneg U I J
  apply sub_nonneg.mp
  rw [fourSevenFace72_gap_eq_minors a b η H hc U hU]
  change 0 ≤
    g 18 * subsetMinorSq U {0} {3} + g 15 * subsetMinorSq U {1} {1} +
      g 11 * subsetMinorSq U {2} {2} + g 7 * subsetMinorSq U {0, 1} {0, 1} +
      g 17 * subsetMinorSq U {0, 1} {2, 3} + (-d) * subsetMinorSq U {0, 2} {0, 2} +
      g 2 * subsetMinorSq U {0, 3} {0, 3}
  have h₀ := mul_nonneg (hg 18) (hm {0} {3})
  have h₆ := mul_nonneg (hg 2) (hm {0, 3} {0, 3})
  rcases le_or_gt d 0 with hd | hd
  · exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg (add_nonneg h₀ (mul_nonneg (hg 15) (hm {1} {1})))
              (mul_nonneg (hg 11) (hm {2} {2})))
            (mul_nonneg (hg 7) (hm {0, 1} {0, 1})))
          (mul_nonneg (hg 17) (hm {0, 1} {2, 3})))
        (mul_nonneg (neg_nonneg.mpr hd) (hm {0, 2} {0, 2}))) h₆
  · obtain ⟨h15, h11, h17⟩ := fourSevenFace72_donor_gaps a b η H hc
    change g 15 = g 14 + d at h15
    change g 11 = g 5 + d at h11
    change g 17 = g 16 + d at h17
    have hGram := fourSevenFace72_budget_minor_nonneg (hg 14) (hg 5) (hg 7) hd.le
      (hcap hd) U hU
    have h₄ := mul_nonneg (hg 16) (hm {0, 1} {2, 3})
    dsimp only at hGram
    rw [h15, h11, h17]
    nlinarith only [hGram, h₀, h₄, h₆]

end

end MOC

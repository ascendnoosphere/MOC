import MOC.FourMatchingRelations
import MOC.FourMinorCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The cubic exclusion for the two negative budgets of zero-height type 32. -/

namespace MOC

open BigOperators

/-- Matching coordinates of the eight ordinary and two mixed rays on
the zero-height face with contacts `{2, 3, 4, 8, 10, 12, 13}`. -/
def fourZeroHeightType32Lift (a₃ a₅ a₁₀ a₁₂ a₁₆ a₂₁ a₂₃ a₂₆ α β : ℝ) : Fin 14 → ℝ :=
  ![a₂₃ + a₂₆ - α + β, -a₂₃ - a₂₆ + α - β, -a₂₆ - a₃ - β,
    a₂₆ - a₅ - α, -a₂₆ + a₅ + α, -a₂₃ - a₂₆ + α - β,
    a₁₆ + a₂₁ + a₂₃ + a₂₆, -a₁₀ + a₂₆ - α, a₁₀ - a₂₆ + α,
    a₁₀ - a₂₁ - a₂₆ + a₅ + α + β, a₂₆ - a₅ - α, -a₁₀ + a₂₆ - α,
    -a₁₂ - a₂₆ - β, a₁₂ + a₂₁ + a₂₆ + a₃ + α + β]

private theorem type32_negative_budget_cubic (x y v w p q u : ℝ) :
    fourMatchingCubic
      ![-u, u, -x, -(v + u), v + u, u, p + q, -(w + u), w + u, v + w - p + u,
        -(v + u), -(w + u), -y, x + y + p + u] =
      -(u ^ 3 + u ^ 2 * (p + q + v + w + x + y) +
        u * (p * q + p * (v + w) + q * (x + y) + v * w + (v + w) * (x + y) + x * y) +
        (p + x + y) * v * w + (q + v + w) * x * y) := by
  simp [fourMatchingCubic]
  ring

private theorem type32_first_budget {a₃ a₅ a₁₀ a₁₂ a₁₆ a₂₁ a₂₃ a₂₆ α β : ℝ}
    (h₃ : 0 ≤ a₃) (h₅ : 0 ≤ a₅) (h₁₀ : 0 ≤ a₁₀) (h₁₂ : 0 ≤ a₁₂)
    (h₁₆ : 0 ≤ a₁₆) (h₂₁ : 0 ≤ a₂₁) (h₂₃ : 0 ≤ a₂₃) (h₂₆ : 0 ≤ a₂₆)
    (hβ : 0 ≤ β)
    (hc : fourMatchingCubic (fourZeroHeightType32Lift a₃ a₅ a₁₀ a₁₂ a₁₆ a₂₁ a₂₃ a₂₆ α β) = 0) :
    0 ≤ a₂₃ + a₂₆ - α + β := by
  by_contra h
  have hl : a₂₃ + a₂₆ - α + β < 0 := lt_of_not_ge h
  let u := α - (a₂₃ + a₂₆ + β)
  let x := a₃ + a₂₆ + β
  let y := a₁₂ + a₂₆ + β
  let v := a₅ + a₂₃ + β
  let w := a₁₀ + a₂₃ + β
  let p := a₂₁ + a₂₃
  let q := a₁₆ + a₂₆
  have hu : 0 < u := by dsimp only [u]; linarith only [hl]
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hy : 0 ≤ y := by dsimp only [y]; positivity
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hlift :
      fourZeroHeightType32Lift a₃ a₅ a₁₀ a₁₂ a₁₆ a₂₁ a₂₃ a₂₆ α β =
        ![-u, u, -x, -(v + u), v + u, u, p + q, -(w + u), w + u, v + w - p + u,
          -(v + u), -(w + u), -y, x + y + p + u] := by
    funext i
    fin_cases i <;> simp [fourZeroHeightType32Lift, x, y, v, w, p, q, u] <;> ring
  rw [hlift, type32_negative_budget_cubic] at hc
  have hpos : 0 < u ^ 3 + u ^ 2 * (p + q + v + w + x + y) +
      u * (p * q + p * (v + w) + q * (x + y) + v * w + (v + w) * (x + y) + x * y) +
      (p + x + y) * v * w + (q + v + w) * x * y := by positivity
  exact (ne_of_lt (neg_neg_of_pos hpos)) hc

private theorem type32_swap_cubic (a₃ a₅ a₁₀ a₁₂ a₁₆ a₂₁ a₂₃ a₂₆ α β : ℝ) :
    fourMatchingCubic (fourZeroHeightType32Lift a₃ a₁₀ a₅ a₁₂ a₂₃ a₂₆ a₁₆ a₂₁ β α) =
      fourMatchingCubic (fourZeroHeightType32Lift a₃ a₅ a₁₀ a₁₂ a₁₆ a₂₁ a₂₃ a₂₆ α β) := by
  simp [fourMatchingCubic, fourZeroHeightType32Lift]
  ring

/-- Cubic vanishing excludes either negative ordinary-minor budget on the
zero-height type 32 ray lift. -/
theorem fourZeroHeightType32_budgets {a₃ a₅ a₁₀ a₁₂ a₁₆ a₂₁ a₂₃ a₂₆ α β : ℝ}
    (h₃ : 0 ≤ a₃) (h₅ : 0 ≤ a₅) (h₁₀ : 0 ≤ a₁₀) (h₁₂ : 0 ≤ a₁₂)
    (h₁₆ : 0 ≤ a₁₆) (h₂₁ : 0 ≤ a₂₁) (h₂₃ : 0 ≤ a₂₃) (h₂₆ : 0 ≤ a₂₆)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hc : fourMatchingCubic (fourZeroHeightType32Lift a₃ a₅ a₁₀ a₁₂ a₁₆ a₂₁ a₂₃ a₂₆ α β) = 0) :
    0 ≤ a₂₃ + a₂₆ - α + β ∧ 0 ≤ a₁₆ + a₂₁ + α - β := by
  refine ⟨type32_first_budget h₃ h₅ h₁₀ h₁₂ h₁₆ h₂₁ h₂₃ h₂₆ hβ hc, ?_⟩
  have hs : fourMatchingCubic (fourZeroHeightType32Lift a₃ a₁₀ a₅ a₁₂ a₂₃ a₂₆ a₁₆ a₂₁ β α) = 0 :=
    (type32_swap_cubic a₃ a₅ a₁₀ a₁₂ a₁₆ a₂₁ a₂₃ a₂₆ α β).trans hc
  have h := type32_first_budget h₃ h₁₀ h₅ h₁₂ h₂₃ h₂₆ h₁₆ h₂₁ hα hs
  linarith only [h]

/-- The prescribed matching contacts of zero-height type 32. -/
def fourZeroHeightType32Contacts : Finset (Fin 24) := {2, 3, 4, 8, 10, 12, 13}

private def type32Coordinates (x y v w p q u : ℝ) : Fin 14 → ℝ :=
  ![-u, u, -x, -(v + u), v + u, u, p + q, -(w + u), w + u, v + w - p + u,
    -(v + u), -(w + u), -y, x + y + p + u]

private def type32Profile (x y v w p q u : ℝ) : Fin 24 → ℝ :=
  ![q + u + v + w, q + u + v, 0, 0, 0, w, q + u + w, q, 0, y, 0, u + w + y, 0, 0,
    v, u + v + y, p, p + u + y, x, u + w + x, u + v + x, 2 * u + v + w + x + y,
    p + u + x, p + u + x + y]

set_option maxHeartbeats 400000 in
private theorem type32_eval (x y v w p q u : ℝ) (i : Fin 24) :
    fourMatchingEvaluation (type32Coordinates x y v w p q u) i = type32Profile x y v w p q u i := by
  fin_cases i <;>
    dsimp only [fourMatchingEvaluation, type32Coordinates, type32Profile, Matrix.cons_val] <;>
    ring

set_option maxHeartbeats 2000000 in
private theorem type32_coordinates_of_contacts (m : Fin 14 → ℝ)
    (hc : ∀ i ∈ fourZeroHeightType32Contacts, fourMatchingEvaluation m i = 0) :
    let g := fourMatchingEvaluation m
    m = type32Coordinates (g 18) (g 9) (g 14) (g 5) (g 16) (g 7) (-m 0) := by
  dsimp only
  have h₂ := hc 2 (by decide)
  have h₃ := hc 3 (by decide)
  have h₄ := hc 4 (by decide)
  have h₈ := hc 8 (by decide)
  have h₁₀ := hc 10 (by decide)
  have h₁₂ := hc 12 (by decide)
  have h₁₃ := hc 13 (by decide)
  simp only [fourMatchingEvaluation, Matrix.cons_val] at h₂ h₃ h₄ h₈ h₁₀ h₁₂ h₁₃
  funext i
  fin_cases i <;> simp [type32Coordinates, fourMatchingEvaluation, Matrix.cons_val] <;>
    linarith only [h₂, h₃, h₄, h₈, h₁₀, h₁₂, h₁₃]

private theorem type32_u_nonpos {x y v w p q u : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hv : 0 ≤ v) (hw : 0 ≤ w) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hc : fourMatchingCubic (type32Coordinates x y v w p q u) = 0) : u ≤ 0 := by
  by_contra h
  have hu : 0 < u := lt_of_not_ge h
  have hpos : 0 < u ^ 3 + u ^ 2 * (p + q + v + w + x + y) +
      u * (p * q + p * (v + w) + q * (x + y) + v * w + (v + w) * (x + y) + x * y) +
      (p + x + y) * v * w + (q + v + w) * x * y := by positivity
  change fourMatchingCubic
    ![-u, u, -x, -(v + u), v + u, u, p + q, -(w + u), w + u, v + w - p + u,
      -(v + u), -(w + u), -y, x + y + p + u] = 0 at hc
  rw [type32_negative_budget_cubic] at hc
  exact (ne_of_lt (neg_neg_of_pos hpos)) hc

private theorem type32_coordinate_swap_cubic (x y v w p q u : ℝ) :
    fourMatchingCubic (type32Coordinates (p + u + x) (p + u + y) (q + u + w) (q + u + v)
      q p (-p - q - u)) = fourMatchingCubic (type32Coordinates x y v w p q u) := by
  simp [fourMatchingCubic, type32Coordinates]
  ring

private def type32MinorRows : Fin 8 → Finset (Fin 4) :=
  ![{0}, {3}, {1}, {2}, {0, 1}, {0, 1}, {0, 2}, {0, 2}]

private def type32MinorColumns : Fin 8 → Finset (Fin 4) :=
  ![{3}, {0}, {1}, {2}, {2, 3}, {0, 1}, {0, 2}, {1, 3}]

private def type32MinorSupports : Fin 8 → Finset ℕ :=
  ![{18, 19, 20, 21, 22, 23}, {9, 11, 15, 17, 21, 23}, {0, 1, 14, 15, 20, 21},
    {0, 5, 6, 11, 19, 21}, {16, 17, 22, 23}, {0, 1, 6, 7}, {0, 5, 14, 16}, {7, 9, 18, 23}]

set_option maxRecDepth 10000 in
private theorem type32_minor_support (k : Fin 8) (i : Fin 24) :
    i.val ∈ type32MinorSupports k ↔
      (type32MinorColumns k).map (fourPerm i).symm.toEmbedding = type32MinorRows k := by
  fin_cases k <;> fin_cases i <;> decide

private def type32MinorWeights (x y v w p q u t : ℝ) : Fin 8 → ℝ :=
  ![x + u + t, y + u + t, v - t, w - t, p - t, q + u + t, t, -u - t]

set_option maxHeartbeats 2000000 in
private theorem type32_minor_evaluation (x y v w p q u t : ℝ) (i : Fin 24) :
    type32Profile x y v w p q u i =
      ∑ k : Fin 8, if i.val ∈ type32MinorSupports k then type32MinorWeights x y v w p q u t k else 0 := by
  fin_cases i <;>
    simp (config := { decide := true }) [type32Profile, type32MinorSupports, type32MinorWeights,
      Fin.sum_univ_succ, Matrix.cons_val] <;> ring

set_option maxHeartbeats 1500000 in
/-- At zero height the seven type 32 contacts force a nonnegative
squared-minor decomposition. Additional contacts and spectral collisions
are allowed. -/
theorem fourZeroHeightType32_support (a b : Fin 4 → ℂ) (η : ℂ)
    (hn : ∀ i, 0 ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourZeroHeightType32Contacts, (η * matchingProduct a b (fourPerm i).symm).re = 0)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    0 ≤ (η * determinantValue a b U).re := by
  let m : Fin 14 → ℝ := fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re
  let g := fourMatchingEvaluation m
  let x := g 18
  let y := g 9
  let v := g 14
  let w := g 5
  let p := g 16
  let q := g 7
  let u := -m 0
  have hg (i : Fin 24) : g i = (η * matchingProduct a b (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part a b η i
  have hm : m = type32Coordinates x y v w p q u :=
    type32_coordinates_of_contacts m (fun i hi => (hg i).trans (hc i hi))
  have hprofile (i : Fin 24) : g i = type32Profile x y v w p q u i := by
    calc
      _ = fourMatchingEvaluation (type32Coordinates x y v w p q u) i :=
        congrArg (fun n => fourMatchingEvaluation n i) hm
      _ = _ := type32_eval x y v w p q u i
  have hg₀ (i : Fin 24) : 0 ≤ type32Profile x y v w p q u i :=
    (hprofile i) ▸ ((hg i).symm ▸ hn i)
  have hx : 0 ≤ x := (hg 18).symm ▸ hn 18
  have hy : 0 ≤ y := (hg 9).symm ▸ hn 9
  have hv : 0 ≤ v := (hg 14).symm ▸ hn 14
  have hw : 0 ≤ w := (hg 5).symm ▸ hn 5
  have hp : 0 ≤ p := (hg 16).symm ▸ hn 16
  have hq : 0 ≤ q := (hg 7).symm ▸ hn 7
  have hc₀ : fourMatchingCubic m = 0 := fourMatchingCubic_of_spectral_real_part a b η
  have hC : fourMatchingCubic (type32Coordinates x y v w p q u) = 0 := hm ▸ hc₀
  have hu : u ≤ 0 := type32_u_nonpos hx hy hv hw hp hq hC
  have h22 : 0 ≤ p + u + x := hg₀ 22
  have h17 : 0 ≤ p + u + y := hg₀ 17
  have h6 : 0 ≤ q + u + w := hg₀ 6
  have h1 : 0 ≤ q + u + v := hg₀ 1
  have hu' : -p - q - u ≤ 0 := type32_u_nonpos h22 h17 h6 h1 hq hp
    ((type32_coordinate_swap_cubic x y v w p q u).trans hC)
  have h11 : 0 ≤ u + w + y := hg₀ 11
  have h15 : 0 ≤ u + v + y := hg₀ 15
  have h19 : 0 ≤ u + w + x := hg₀ 19
  have h20 : 0 ≤ u + v + x := hg₀ 20
  let t := max 0 (max (-u - x) (max (-u - y) (-u - q)))
  let c := type32MinorWeights x y v w p q u t
  have hle (s : ℝ) (h₀ : 0 ≤ s) (h₁ : -u - x ≤ s) (h₂ : -u - y ≤ s) (h₃ : -u - q ≤ s) :
      t ≤ s := max_le h₀ (max_le h₁ (max_le h₂ h₃))
  have ht₀ : 0 ≤ t := le_max_left _ _
  have ht₁ : t ≤ -u := hle _ (by linarith only [hu])
    (by linarith only [hx]) (by linarith only [hy]) (by linarith only [hq])
  have htv : t ≤ v := hle _ hv (by linarith only [h20]) (by linarith only [h15]) (by linarith only [h1])
  have htw : t ≤ w := hle _ hw (by linarith only [h19]) (by linarith only [h11]) (by linarith only [h6])
  have htp : t ≤ p := hle _ hp (by linarith only [h22]) (by linarith only [h17]) (by linarith only [hu'])
  have hxt : -u - x ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have hyt : -u - y ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hqt : -u - q ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hweights (k : Fin 8) : 0 ≤ c k := by
    fin_cases k
    · change 0 ≤ x + u + t
      linarith only [hxt]
    · change 0 ≤ y + u + t
      linarith only [hyt]
    · exact (sub_nonneg.mpr htv : 0 ≤ v - t)
    · exact (sub_nonneg.mpr htw : 0 ≤ w - t)
    · exact (sub_nonneg.mpr htp : 0 ≤ p - t)
    · change 0 ≤ q + u + t
      linarith only [hqt]
    · exact ht₀
    · exact (sub_nonneg.mpr ht₁ : 0 ≤ -u - t)
  refine four_support_of_minor_gap_decomposition a b η 0 U hU 2 (hc 2 (by decide))
    type32MinorRows type32MinorColumns c hweights (fun i => ?_)
  rw [sub_zero, ← hg, hprofile]
  simp_rw [← type32_minor_support]
  exact type32_minor_evaluation x y v w p q u t i

end MOC

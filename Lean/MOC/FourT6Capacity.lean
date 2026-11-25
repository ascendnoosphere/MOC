import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The rational two-budget capacities in the two nonminor T6 charts. -/

namespace MOC

/-- The same geometric capacity identity governs both T6 charts. This
form clears the positive divisors in the geometric identity. -/
theorem fourT6_geometric_budget {K L M A T R : ℝ}
    (hK : 0 < K) (hM : 0 < M) (hML : M ≤ L) (hA : 0 ≤ A) (hT : 0 < T)
    (hKR : A ^ 2 ≤ K * R) (hLR : A ≤ L * R)
    (hId : L * (K - M * T) = M * (K - L * A)) : A ^ 2 / T ≤ M * R := by
  have hL : 0 < L := hM.trans_le hML
  have hR : 0 ≤ R := (mul_nonneg_iff_of_pos_left hK).mp ((sq_nonneg A).trans hKR)
  apply (div_le_iff₀ hT).mpr
  by_cases h : K ≤ M * T
  · calc
      _ ≤ K * R := hKR
      _ ≤ (M * T) * R := mul_le_mul_of_nonneg_right h hR
      _ = _ := by ring
  · have hpos : 0 < L * (K - M * T) := mul_pos hL (sub_pos.mpr (lt_of_not_ge h))
    have hK' : 0 ≤ K - L * A := ((mul_pos_iff_of_pos_left hM).mp (hId ▸ hpos)).le
    have he : L * (M * T - L * A) = (L - M) * (K - L * A) := by
      linear_combination -hId
    have hprod : L * A ≤ M * T := sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hL).mp
      (he.symm ▸ mul_nonneg (sub_nonneg.mpr hML) hK'))
    calc
      A ^ 2 = A * A := pow_two A
      _ ≤ A * (L * R) := mul_le_mul_of_nonneg_left hLR hA
      _ = (L * A) * R := by ring
      _ ≤ (M * T) * R := mul_le_mul_of_nonneg_right hprod hR
      _ = _ := by ring

/-- In case I the exact coefficient `η` is feasible and gives the
nonnegative two-budget determinant. -/
theorem fourT6_case_one_budget {K J h b : ℝ}
    (hJ : 0 < J) (hh : h < 0) (hK : K ≤ 1 + J)
    (hb₁ : 1 ≤ b) (hbK : K ≤ b) (hbA : (1 + J) ^ 2 / (1 + (2 - h) * J) ≤ b) :
    let T := 1 + (2 - h) * J
    let η := max 0 (max (K - 1) (J * (J + h) / T))
    0 ≤ η ∧ η ≤ J ∧ η + 1 ≤ b ∧ K ≤ η + 1 ∧
      0 ≤ η - h * J ∧ (J - η) ^ 2 ≤ (η - h * J) * (η + 1) := by
  intro T η
  have hT : 0 < T := by
    have hh' : 0 < 2 - h := by linarith only [hh]
    dsimp only [T]
    linarith only [mul_pos hh' hJ]
  have hη₀ : 0 ≤ η := le_max_left _ _
  have hηK : K - 1 ≤ η := (le_max_left _ _).trans (le_max_right _ _)
  have hηT : J * (J + h) / T ≤ η := (le_max_right _ _).trans (le_max_right _ _)
  have hJT : J + h ≤ T := by
    have he : T - (J + h) = (1 - h) * (1 + J) := by dsimp only [T]; ring
    have hp := mul_nonneg (show 0 ≤ 1 - h by linarith only [hh]) (show 0 ≤ 1 + J by linarith only [hJ])
    linarith only [he, hp]
  have hηJ : η ≤ J := max_le hJ.le (max_le (by linarith only [hK])
    ((div_le_iff₀ hT).mpr (mul_le_mul_of_nonneg_left hJT hJ.le)))
  have hEq : (1 + J) ^ 2 = T + J * (J + h) := by dsimp only [T]; ring
  have hbA' : J * (J + h) / T ≤ b - 1 := by
    have hb' : (1 + J) ^ 2 ≤ b * T := (div_le_iff₀ hT).mp hbA
    exact (div_le_iff₀ hT).mpr (by linarith only [hb', hEq])
  have hηb : η ≤ b - 1 := max_le (sub_nonneg.mpr hb₁) (max_le (by linarith only [hbK]) hbA')
  have hcoef := mul_nonpos_of_nonpos_of_nonneg hh.le hJ.le
  have hcap := (div_le_iff₀ hT).mp hηT
  refine ⟨hη₀, hηJ, by linarith only [hηb], by linarith only [hηK], ?_, ?_⟩
  · linarith only [hη₀, hcoef]
  · have he : (η - h * J) * (η + 1) - (J - η) ^ 2 = η * T - J * (J + h) := by
      dsimp only [T]
      ring
    linarith only [he, hcap]

/-- In case II the endpoint coefficient saturates the two-budget bound
and all its displayed ordinary coefficients are nonnegative. -/
theorem fourT6_case_two_budget {P α B : ℝ} (hP : 0 < P) (hα : 0 < P + α)
    (hB : P ^ 2 / (2 * P + α) ≤ B) :
    let T := 2 * P + α
    let η := P ^ 2 / T
    0 ≤ η ∧ 0 ≤ η + α ∧ η ≤ P ∧ η ≤ B ∧ (P - η) ^ 2 = η * (η + α) := by
  intro T η
  have hT : 0 < T := by dsimp only [T]; linarith only [hP, hα]
  have hη₀ : 0 ≤ η := div_nonneg (sq_nonneg _) hT.le
  have he : η * T = P ^ 2 := div_mul_cancel₀ _ hT.ne'
  have hpT : P ≤ T := by dsimp only [T]; linarith only [hα]
  have hηP : η ≤ P := by
    apply (div_le_iff₀ hT).mpr
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hpT hP.le
  have hηα : 0 ≤ η + α := by
    apply (mul_nonneg_iff_of_pos_right hT).mp
    have h : (η + α) * T = (P + α) ^ 2 := by
      dsimp only [T] at he ⊢
      linear_combination he
    rw [h]
    exact sq_nonneg _
  refine ⟨hη₀, hηα, hηP, hB, ?_⟩
  dsimp only [T] at he
  linear_combination -he

end MOC

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! A finite halfspace clipping step for linear support tests. -/

open BigOperators

namespace MOC

variable {E κ : Type*} [AddCommGroup E] [Module ℝ E] [Fintype κ]

/-- The tests on retained rays and positive-negative crossings give a
nonnegative multiplier for the new halfspace. -/
theorem exists_halfspace_multiplier (r : κ → E) (A L : E →ₗ[ℝ] ℝ)
    (hkeep : ∀ i, 0 ≤ A (r i) → 0 ≤ L (r i))
    (hcross : ∀ i j, 0 < A (r i) → A (r j) < 0 →
      0 ≤ L (A (r i) • r j - A (r j) • r i)) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ i, a * A (r i) ≤ L (r i) := by
  classical
  let q : Option κ → ℝ
    | none => 0
    | some i => if A (r i) < 0 then L (r i) / A (r i) else 0
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ q
    ⟨none, Finset.mem_univ _⟩
  have hmax (j : Option κ) : q j ≤ q k := hk j (Finset.mem_univ j)
  refine ⟨q k, hmax none, fun i => ?_⟩
  rcases lt_trichotomy (A (r i)) 0 with hn | hz | hp
  · apply (div_le_iff_of_neg hn).mp
    simpa only [q, if_pos hn] using hmax (some i)
  · rw [hz, mul_zero]
    exact hkeep i hz.ge
  · apply (le_div_iff₀ hp).mp
    have hzero : 0 ≤ L (r i) / A (r i) := div_nonneg (hkeep i hp.le) hp.le
    cases k with
    | none => exact hzero
    | some j =>
      by_cases hj : A (r j) < 0
      · simp only [q, if_pos hj]
        apply (div_le_iff_of_neg hj).mpr
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hp).mpr
        have he := hcross i j hp hj
        simp only [map_sub, map_smul, smul_eq_mul, sub_nonneg] at he
        simpa only [mul_comm (L (r i)), mul_comm (L (r j))] using he
      · simpa only [q, if_neg hj] using hzero

/-- A linear test nonnegative on the retained rays and the crossing rays
is nonnegative on the old cone intersected with the new halfspace. -/
theorem halfspace_clip_support_nonneg (r : κ → E) (A L : E →ₗ[ℝ] ℝ)
    (hkeep : ∀ i, 0 ≤ A (r i) → 0 ≤ L (r i))
    (hcross : ∀ i j, 0 < A (r i) → A (r j) < 0 →
      0 ≤ L (A (r i) • r j - A (r j) • r i))
    (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hA : 0 ≤ A (∑ i, w i • r i)) :
    0 ≤ L (∑ i, w i • r i) := by
  obtain ⟨a, ha, h⟩ := exists_halfspace_multiplier r A L hkeep hcross
  calc
    0 ≤ a * A (∑ i, w i • r i) := mul_nonneg ha hA
    _ = ∑ i, w i * (a * A (r i)) := by
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, w i * L (r i) := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i)
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

end MOC

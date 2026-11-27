import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The determinant comparison for spin factors of rank two.
The proof uses the norm and inner product of the real vector part. -/

namespace MOC.Reformulations

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def spinDeterminant (s : ℝ) (x : E) : ℝ := s ^ 2 - ‖x‖ ^ 2

/-- The two possible eigenvalue matchings are the two endpoints. -/
theorem spinEndpoints (s t r w : ℝ) :
    (s + r + (t + w)) * (s - r + (t - w)) = (s + t) ^ 2 - (r + w) ^ 2 ∧
    (s + r + (t - w)) * (s - r + (t + w)) = (s + t) ^ 2 - (r - w) ^ 2 := by
  constructor <;> ring

theorem spinFactorBounds (s t : ℝ) (x y : E) (Q : E ≃ₗᵢ[ℝ] E) :
    (s + t) ^ 2 - (‖x‖ + ‖y‖) ^ 2 ≤ spinDeterminant (s + t) (x + Q y) ∧
    spinDeterminant (s + t) (x + Q y) ≤ (s + t) ^ 2 - (‖x‖ - ‖y‖) ^ 2 := by
  have h := abs_real_inner_le_norm x (Q y)
  rw [Q.norm_map] at h
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  unfold spinDeterminant
  rw [norm_add_sq_real, Q.norm_map]
  constructor <;> nlinarith only [hlo, hhi]

end
end MOC.Reformulations

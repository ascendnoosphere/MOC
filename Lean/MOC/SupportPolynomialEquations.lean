import MOC.Support
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Strict separation written with unit direction and polynomial slack equations. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_square_slack_iff_pos (g : ℝ) :
    (∃ t : ℝ, g * t ^ 2 = 1) ↔ 0 < g := by
  constructor
  · rintro ⟨t, ht⟩
    by_contra! hg
    have hn : g * t ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hg (sq_nonneg t)
    linarith only [ht, hn]
  · intro hg
    refine ⟨(Real.sqrt g)⁻¹, ?_⟩
    rw [inv_pow, Real.sq_sqrt hg.le, mul_inv_cancel₀ hg.ne']

/-- A witness outside the matching hull is equivalent to one solution of
the unit-direction equation and one slack equation per matching. -/
theorem not_holds_iff_support_polynomial_equations (a b : ι → ℂ) (U : Matrix ι ι ℂ) :
    ¬ Holds a b U ↔
      ∃ (η : ℂ) (t : Equiv.Perm ι → ℝ), Complex.normSq η = 1 ∧
        ∀ σ, (η * (determinantValue a b U - matchingProduct a b σ)).re * t σ ^ 2 = 1 := by
  classical
  rw [holds_iff_directional]
  push_neg
  constructor
  · rintro ⟨k, hk⟩
    have hk₀ : k ≠ 0 := by
      rintro rfl
      simpa using hk (Equiv.refl ι)
    have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk₀
    let η : ℂ := ((‖k‖⁻¹ : ℝ) : ℂ) * k
    have hη : Complex.normSq η = 1 := by
      rw [Complex.normSq_eq_norm_sq, show η = ((‖k‖⁻¹ : ℝ) : ℂ) * k from rfl, norm_mul,
        Complex.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg k)),
        inv_mul_cancel₀ hkpos.ne', one_pow]
    have hp (σ : Equiv.Perm ι) :
        0 < (η * (determinantValue a b U - matchingProduct a b σ)).re := by
      dsimp only [η]
      rw [mul_assoc, Complex.re_ofReal_mul, mul_sub, Complex.sub_re]
      exact mul_pos (inv_pos.mpr hkpos) (sub_pos.mpr (hk σ))
    choose t ht using fun σ => (exists_square_slack_iff_pos _).mpr (hp σ)
    exact ⟨η, t, hη, ht⟩
  · rintro ⟨η, t, _, ht⟩
    refine ⟨η, fun σ => ?_⟩
    have hp := (exists_square_slack_iff_pos _).mp ⟨t σ, ht σ⟩
    rw [mul_sub, Complex.sub_re] at hp
    exact sub_pos.mp hp

end MOC

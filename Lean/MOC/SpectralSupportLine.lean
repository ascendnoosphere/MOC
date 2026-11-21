import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! An equality of centered outer products detects collinearity on the
support of their common coordinate weights. -/

open scoped ComplexConjugate

namespace MOC

/-- If centering a spectrum at `μ` gives the same weighted outer product
before and after conjugating the centered spectral values, the supported
values lie on one affine line through `μ`. -/
theorem exists_spectral_line_of_centered_outer_eq {ι : Type*}
    (β w : ι → ℂ) (μ : ℂ)
    (h : ∀ j k, ((β j - μ) * w j) * conj ((β k - μ) * w k) =
      (conj (β j - μ) * w j) * conj (conj (β k - μ) * w k)) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ j, w j ≠ 0 → ∃ t : ℝ, β j = μ + d * (t : ℂ) := by
  by_cases hex : ∃ k, w k ≠ 0 ∧ β k ≠ μ
  · obtain ⟨k, hwk, hβk⟩ := hex
    let d := β k - μ
    have hd : d ≠ 0 := sub_ne_zero.mpr hβk
    have hconj {z : ℂ} (hz : z ≠ 0) : conj z ≠ 0 := by
      intro he
      have h' := congrArg (fun v : ℂ => conj v) he
      exact hz (by simpa only [starRingEnd_self_apply, map_zero] using h')
    refine ⟨d, hd, fun j hwj => ?_⟩
    have hcross : (β j - μ) * conj d = conj (β j - μ) * d := by
      apply mul_right_cancel₀ (mul_ne_zero hwj (hconj hwk))
      have he := h j k
      simp only [map_mul, starRingEnd_self_apply] at he
      dsimp only [d]
      linear_combination he
    have hratio : conj ((β j - μ) / d) = (β j - μ) / d := by
      rw [map_div₀]
      exact (div_eq_div_iff (hconj hd) hd).mpr hcross.symm
    obtain ⟨t, ht⟩ := Complex.conj_eq_iff_real.mp hratio
    have he := (div_eq_iff hd).mp ht
    refine ⟨t, ?_⟩
    linear_combination he
  · refine ⟨1, one_ne_zero, fun j hwj => ⟨0, ?_⟩⟩
    have hj : β j = μ := not_not.mp fun hj => hex ⟨j, hwj, hj⟩
    simpa only [Complex.ofReal_zero, mul_zero, add_zero] using hj

end MOC

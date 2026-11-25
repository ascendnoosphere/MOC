import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! Complex orientation and equality of directional projections. -/

namespace MOC

/-- Two planar vectors have zero orientation exactly when they have a common
nonzero direction in which both real projections vanish. -/
theorem im_mul_conj_eq_zero_iff_exists_common_projection {u v : ℂ} (hu : u ≠ 0) :
    (u * star v).im = 0 ↔
      ∃ η : ℂ, η ≠ 0 ∧ (η * u).re = 0 ∧ (η * v).re = 0 := by
  have hor : (u * star v).im = u.im * v.re - u.re * v.im := by
    simp only [Complex.star_def, Complex.mul_im, Complex.conj_im, Complex.conj_re]
    ring
  constructor
  · intro h
    let η := Complex.I * star u
    have hre : η.re = u.im := by
      simp [η, Complex.star_def, Complex.mul_re]
    have him : η.im = u.re := by
      simp [η, Complex.star_def, Complex.mul_im]
    refine ⟨η, mul_ne_zero Complex.I_ne_zero (star_ne_zero.mpr hu), ?_, ?_⟩
    · rw [Complex.mul_re, hre, him, mul_comm u.im, sub_self]
    · rwa [Complex.mul_re, hre, him, ← hor]
  · rintro ⟨η, hη, hηu, hηv⟩
    rw [Complex.mul_re] at hηu hηv
    rw [hor]
    by_cases hre : η.re = 0
    · have him : η.im ≠ 0 := fun h => hη (Complex.ext hre h)
      apply (mul_eq_zero.mp ?_).resolve_left him
      linear_combination u.re * hηv - v.re * hηu
    · apply (mul_eq_zero.mp ?_).resolve_left hre
      linear_combination u.im * hηv - v.im * hηu

/-- If three complex values have nonzero orientation, a nonzero direction
cannot tie all three of their real projections. -/
theorem no_three_tied_projections_iff_orientation {κ : Type*} {f : κ → ℂ}
    (hf : Function.Injective f) :
    (∀ η : ℂ, η ≠ 0 → ∀ p q r : κ, p ≠ q → p ≠ r → q ≠ r →
      (η * f p).re = (η * f q).re → (η * f p).re ≠ (η * f r).re) ↔
    ∀ p q r : κ, p ≠ q → p ≠ r → q ≠ r →
      ((f p - f q) * star (f p - f r)).im ≠ 0 := by
  constructor
  · intro h p q r hpq hpr hqr hz
    have hsub : f p - f q ≠ 0 := sub_ne_zero.mpr (hf.ne hpq)
    obtain ⟨η, hη, hηpq, hηpr⟩ :=
      (im_mul_conj_eq_zero_iff_exists_common_projection hsub).mp hz
    simp only [mul_sub, Complex.sub_re, sub_eq_zero] at hηpq hηpr
    exact h η hη p q r hpq hpr hqr hηpq hηpr
  · intro h η hη p q r hpq hpr hqr hηpq hηpr
    have hsub : f p - f q ≠ 0 := sub_ne_zero.mpr (hf.ne hpq)
    apply h p q r hpq hpr hqr
    apply (im_mul_conj_eq_zero_iff_exists_common_projection hsub).mpr
    exact ⟨η, hη, by simp only [mul_sub, Complex.sub_re, sub_eq_zero, hηpq],
      by simp only [mul_sub, Complex.sub_re, sub_eq_zero, hηpr]⟩

end MOC

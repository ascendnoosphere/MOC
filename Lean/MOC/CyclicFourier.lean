import MOC.Core
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! Unitary Fourier mixing on a finite cyclic group. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

/-- Conjugating the cyclic character negates its argument. -/
theorem cyclicCharacter_conj {n : ℕ} [NeZero n] (x : ZMod n) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.star_def]
  apply (Complex.inv_eq_conj ?_).symm
  exact Circle.norm_coe (ZMod.toCircle x)

/-- The normalized discrete Fourier matrix over the cyclic group of order `n`. -/
def cyclicFourier (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) * ZMod.stdAddChar (i * j)

private theorem fourier_scale_sq (n : ℕ) :
    ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by positivity)]

theorem cyclicFourier_scale_mul (n : ℕ) :
    (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) =
      (n : ℂ)⁻¹ := by
  rw [← Complex.ofReal_mul, ← pow_two, fourier_scale_sq, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem cyclicFourier_unitary (n : ℕ) [NeZero n] : IsUnitary (cyclicFourier n) := by
  have h : cyclicFourier n * (cyclicFourier n)ᴴ = 1 := by
    ext i k : 1
    have hreal : star (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) =
        (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
    have ht (j : ZMod n) : cyclicFourier n i j * star (cyclicFourier n k j) =
        (n : ℂ)⁻¹ * ZMod.stdAddChar (j * (i - k)) := by
      simp only [cyclicFourier, star_mul', hreal, cyclicCharacter_conj]
      rw [mul_mul_mul_comm, cyclicFourier_scale_mul, ← AddChar.map_add_eq_mul]
      rw [show i * j + -(k * j) = j * (i - k) by ring]
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [Matrix.mul_apply]
    simp_rw [Matrix.conjTranspose_apply, ht]
    rw [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n)]
    by_cases hik : i = k
    · subst k
      simp [ZMod.card, hn]
    · simp [sub_ne_zero.mpr hik, Matrix.one_apply_ne hik]
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

end

end MOC

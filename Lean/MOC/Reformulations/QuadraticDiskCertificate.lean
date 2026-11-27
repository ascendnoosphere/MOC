import MOC.RankOneDefectSupport
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases

/-! An exact two-by-two semidefinite certificate for the support
quadratic on a closed complex disk. -/

open Matrix
open scoped ComplexOrder

namespace MOC.Reformulations

noncomputable section

/-- The certificate for an upper bound on the quadratic disk score. -/
def diskCertificateMatrix (a b : ℝ) (d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), -d; -star d, (b : ℂ)]

private theorem diskCertificateQuadratic (a b : ℝ) (d : ℂ) (x : Fin 2 → ℂ) :
    dotProduct (star x) (diskCertificateMatrix a b d *ᵥ x) =
      ((a * Complex.normSq (x 0) - 2 * (d * star (x 0) * x 1).re +
        b * Complex.normSq (x 1) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [diskCertificateMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val,
      Complex.star_def, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im] <;> ring

private theorem diskCertificateMatrix_posSemidef (a b : ℝ) (d : ℂ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hdet : ‖d‖ ^ 2 ≤ a * b) : (diskCertificateMatrix a b d).PosSemidef := by
  constructor
  · unfold Matrix.IsHermitian
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      simp [diskCertificateMatrix, Matrix.conjTranspose_apply, Matrix.cons_val, Complex.star_def]
  · intro x
    rw [diskCertificateQuadratic, Complex.nonneg_iff]
    simp only [Complex.ofReal_re, Complex.ofReal_im, and_true, eq_self_iff_true,
      Complex.normSq_eq_norm_sq]
    have hlinear : (d * star (x 0) * x 1).re ≤ ‖d‖ * ‖x 0‖ * ‖x 1‖ := by
      simpa only [norm_mul, Complex.star_def, Complex.norm_conj] using
        Complex.re_le_norm (d * star (x 0) * x 1)
    have hquad : 0 ≤ a * ‖x 0‖ ^ 2 - 2 * (‖d‖ * ‖x 0‖ * ‖x 1‖) + b * ‖x 1‖ ^ 2 := by
      by_cases hzero : b = 0
      · have he : ‖d‖ = 0 := by
          rw [hzero, mul_zero] at hdet
          exact pow_eq_zero (le_antisymm hdet (sq_nonneg _))
        simp only [he, hzero, zero_mul, mul_zero, sub_zero, add_zero]
        exact mul_nonneg ha (sq_nonneg _)
      · apply nonneg_of_mul_nonneg_left _ (lt_of_le_of_ne hb (Ne.symm hzero))
        have hd := mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg ‖x 0‖)
        nlinarith only [hd, sq_nonneg (b * ‖x 1‖ - ‖d‖ * ‖x 0‖)]
    linarith only [hquad, hlinear]

/-- A quadratic real score lies below `M` on the closed unit disk if and
only if it admits the stated two-by-two positive semidefinite certificate. -/
theorem quadratic_disk_bound_iff_semidefinite (p q M : ℝ) (d : ℂ) :
    (∀ z : ℂ, ‖z‖ ≤ 1 → p + 2 * (d * z).re + q * ‖z‖ ^ 2 ≤ M) ↔
      ∃ multiplier : ℝ, 0 ≤ multiplier ∧
        (diskCertificateMatrix (M - p - multiplier) (multiplier - q) d).PosSemidef := by
  constructor
  · intro h
    obtain ⟨_, z, hz, he, _⟩ := quadraticDiskSupport_max p q d
    change p + 2 * (d * z).re + q * ‖z‖ ^ 2 = _ at he
    have hm := h z hz
    rw [he] at hm
    by_cases hq : -‖d‖ ≤ q
    · simp only [if_pos hq] at hm
      refine ⟨q + ‖d‖, by linarith only [hq], ?_⟩
      have hb : q + ‖d‖ - q = ‖d‖ := by ring
      rw [hb]
      have ha : ‖d‖ ≤ M - p - (q + ‖d‖) := by linarith only [hm]
      exact diskCertificateMatrix_posSemidef _ _ _ ((norm_nonneg d).trans ha)
        (norm_nonneg d) (by simpa only [pow_two] using mul_le_mul_of_nonneg_right ha (norm_nonneg d))
    · simp only [if_neg hq] at hm
      have hb : 0 < -q := by linarith only [lt_of_not_ge hq, norm_nonneg d]
      have ha : ‖d‖ ^ 2 / (-q) ≤ M - p := by linarith only [hm]
      refine ⟨0, le_rfl, ?_⟩
      simp only [sub_zero, zero_sub]
      have hdet := (div_le_iff₀ hb).mp ha
      exact diskCertificateMatrix_posSemidef _ _ _
        ((div_nonneg (sq_nonneg _) hb.le).trans ha) hb.le (by simpa only [mul_comm] using hdet)
  · rintro ⟨multiplier, hmultiplier, hM⟩ z hz
    have hc := hM.2 (![1, z] : Fin 2 → ℂ)
    rw [diskCertificateQuadratic, Complex.nonneg_iff] at hc
    have he := hc.1
    simp only [Complex.ofReal_re, Matrix.cons_val_zero, Matrix.cons_val_one, star_one, mul_one,
      Complex.normSq_eq_norm_sq, norm_one, one_pow] at he
    have hz₂ : ‖z‖ ^ 2 ≤ 1 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hz) (add_nonneg zero_le_one (norm_nonneg z))]
    nlinarith only [he, mul_nonneg hmultiplier (sub_nonneg.mpr hz₂)]

end
end MOC.Reformulations

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Real evaluations of a three-group affine pencil can satisfy fixed group
mass constraints while a complex evaluation fails. -/

namespace MOC

/-- The equal-weight Minkowski average of the three segments with endpoints
`±(z - 1)`, `±(z * I)`, and `±((z + 1) * (1 + I))`. -/
def threeGroupAffineHull (z : ℂ) : Set ℂ :=
  {w | ∃ r s t : ℝ, |r| ≤ 1 / 3 ∧ |s| ≤ 1 / 3 ∧ |t| ≤ 1 / 3 ∧
    w = (z - 1) * (r : ℂ) + (z * Complex.I) * (s : ℂ) +
      ((z + 1) * (1 + Complex.I)) * (t : ℂ)}

/-- Every real evaluation of the target pencil satisfies the three group
mass constraints. -/
theorem real_div_eight_mem_threeGroupAffineHull (x : ℝ) :
    (x : ℂ) / 8 ∈ threeGroupAffineHull (x : ℂ) := by
  change ∃ r s t : ℝ, |r| ≤ 1 / 3 ∧ |s| ≤ 1 / 3 ∧ |t| ≤ 1 / 3 ∧
    (x : ℂ) / 8 = ((x : ℂ) - 1) * (r : ℂ) + ((x : ℂ) * Complex.I) * (s : ℂ) +
      (((x : ℂ) + 1) * (1 + Complex.I)) * (t : ℂ)
  by_cases hsmall : x ≤ 1 / 2
  · have hneg : x - 1 < 0 := by linarith only [hsmall]
    have hmag : |x| ≤ |x - 1| := by
      rw [abs_of_neg hneg]
      exact abs_le.mpr ⟨by linarith, by linarith only [hsmall]⟩
    have hden : 0 < 8 * |x - 1| := mul_pos (by norm_num) (abs_pos.mpr hneg.ne)
    have hcoef : |x / (8 * (x - 1))| ≤ 1 / 3 := by
      rw [abs_div, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 8 by norm_num)]
      exact (div_le_iff₀ hden).mpr (by linarith only [hmag, abs_nonneg (x - 1)])
    have he : x / 8 = (x - 1) * (x / (8 * (x - 1))) := by
      field_simp [hneg.ne] <;> ring
    refine ⟨x / (8 * (x - 1)), 0, 0, hcoef, by norm_num, by norm_num, ?_⟩
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_zero, mul_zero, add_zero]
      using congrArg Complex.ofReal he
  · have hx : 1 / 2 < x := lt_of_not_ge hsmall
    have hxpos : 0 < x := by linarith only [hx]
    let s : ℝ := -(x + 1) / (16 * x)
    have hs : |s| ≤ 1 / 3 := by
      have hplus : 0 < x + 1 := by linarith only [hxpos]
      have hden : 0 < 16 * x := mul_pos (by norm_num) hxpos
      dsimp only [s]
      rw [abs_div, abs_neg, abs_of_pos hplus, abs_of_pos hden]
      exact (div_le_iff₀ hden).mpr (by linarith only [hx])
    have hprod : x * s = -(x + 1) / 16 := by
      dsimp only [s]
      field_simp [hxpos.ne'] <;> ring
    have hprodC : (x : ℂ) * (s : ℂ) = -((x : ℂ) + 1) / 16 := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
        Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_one]
        using congrArg Complex.ofReal hprod
    refine ⟨1 / 16, s, 1 / 16, by norm_num, hs, by norm_num, ?_⟩
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
    linear_combination (-Complex.I) * hprodC

/-- At `(1 - 2i) / 5`, the same target lies outside the group average.
The real part after multiplication by `1 + 2i` separates it. -/
theorem complex_div_eight_not_mem_threeGroupAffineHull :
    ((⟨1 / 5, -(2 / 5)⟩ : ℂ) / 8) ∉ threeGroupAffineHull ⟨1 / 5, -(2 / 5)⟩ := by
  rintro ⟨r, s, t, _, _, _, h⟩
  have hscore := congrArg (fun w : ℂ => ((⟨1, 2⟩ : ℂ) * w).re) h
  norm_num [Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] at hscore <;>
    linarith only [hscore]

end MOC

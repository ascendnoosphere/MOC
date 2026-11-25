import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! Exact polynomial identities for Zheng's six-label T55 pattern
(preprint DOI: 10.13140/RG.2.2.36790.25923, Appendix E).
Labels here are row-to-column assignments, the inverses of the repository's
column-to-row matching indices. -/

namespace MOC
namespace ZhengT55

variable (a b : Fin 4 → ℂ)

private def atPositions (a b : Fin 4 → ℂ) (i j k l : Fin 4) : ℂ :=
  (a 0 + b i) * (a 1 + b j) * (a 2 + b k) * (a 3 + b l)

def p₁ : ℂ := atPositions a b 0 1 3 2
def p₂ : ℂ := atPositions a b 0 2 1 3
def p₃ : ℂ := atPositions a b 0 2 3 1
def p₆ : ℂ := atPositions a b 1 0 2 3
def p₁₁ : ℂ := atPositions a b 1 3 2 0
def p₁₂ : ℂ := atPositions a b 2 0 1 3
def p₁₃ : ℂ := atPositions a b 2 0 3 1
def p₁₇ : ℂ := atPositions a b 2 3 1 0
def p₂₀ : ℂ := atPositions a b 3 1 0 2

/-- Its two missing corners follow by separating the two disjoint swaps. -/
theorem rectangle_products :
    p₂ a b * p₁₃ a b = p₃ a b * p₁₂ a b ∧
    p₆ a b * p₁₇ a b = p₁₁ a b * p₁₂ a b := by
  unfold p₂ p₁₃ p₃ p₁₂ p₆ p₁₇ p₁₁ atPositions
  constructor <;> ring

private theorem pure_imaginary_missing_corner {u v w x : ℂ}
    (h : u*x = v*w) (hu : u ≠ 0) (huR : u.re = 0)
    (hv : v.re = 0) (hw : w.re = 0) : x.re = 0 := by
  have hi := congrArg Complex.im h
  rw [Complex.mul_im, Complex.mul_im, huR, hv, hw, zero_mul, zero_mul, mul_zero,
    zero_add, add_zero] at hi
  have huI : u.im ≠ 0 := by
    intro he
    apply hu
    apply Complex.ext
    · simpa using huR
    · simpa using he
  exact (mul_eq_zero.mp hi).resolve_left huI

/-- At zero support height the two incomplete rectangles must both
complete, with no generic phase or noncollision assumptions. -/
theorem force_zero_height_contacts (η : ℂ) (hη : η ≠ 0)
    (hn₂ : p₂ a b ≠ 0) (hn₆ : p₆ a b ≠ 0)
    (h₂ : (η*p₂ a b).re = 0) (h₃ : (η*p₃ a b).re = 0)
    (h₆ : (η*p₆ a b).re = 0) (h₁₁ : (η*p₁₁ a b).re = 0)
    (h₁₂ : (η*p₁₂ a b).re = 0) :
    (η*p₁₃ a b).re = 0 ∧ (η*p₁₇ a b).re = 0 := by
  obtain ⟨r₁,r₂⟩ := rectangle_products a b
  have e₁ : (η*p₂ a b)*(η*p₁₃ a b) = (η*p₃ a b)*(η*p₁₂ a b) := by
    calc
      _ = η^2 * (p₂ a b * p₁₃ a b) := by ring
      _ = η^2 * (p₃ a b * p₁₂ a b) := by rw [r₁]
      _ = _ := by ring
  have e₂ : (η*p₆ a b)*(η*p₁₇ a b) = (η*p₁₁ a b)*(η*p₁₂ a b) := by
    calc
      _ = η^2 * (p₆ a b * p₁₇ a b) := by ring
      _ = η^2 * (p₁₁ a b * p₁₂ a b) := by rw [r₂]
      _ = _ := by ring
  exact ⟨pure_imaginary_missing_corner e₁ (mul_ne_zero hη hn₂) h₂ h₃ h₁₂,
    pure_imaginary_missing_corner e₂ (mul_ne_zero hη hn₆) h₆ h₁₁ h₁₂⟩

/-- This quadratic couples the dangerous T55 gap 17 to gap 20.
It is a universal identity in the eight spectral values. -/
theorem signed_gap_relation :
    (p₁ a b-p₃ a b)*(p₂₀ a b-p₁₂ a b) +
      (p₁ a b-p₆ a b)*(p₁₇ a b-p₁₂ a b) =
    (p₁ a b-p₁₂ a b)*(p₁ a b+p₁₁ a b-p₃ a b-p₆ a b) := by
  unfold p₁ p₃ p₂₀ p₁₂ p₆ p₁₇ p₁₁ atPositions
  ring

/-- The imaginary contact differences weight the two real gaps in the
projected identity. -/
theorem projected_gap_relation (η : ℂ) (H : ℝ)
    (h₁ : (η*p₁ a b).re = H) (h₃ : (η*p₃ a b).re = H)
    (h₆ : (η*p₆ a b).re = H) (h₁₁ : (η*p₁₁ a b).re = H)
    (h₁₂ : (η*p₁₂ a b).re = H) :
    (η*(p₁ a b-p₃ a b)).im * (H-(η*p₂₀ a b).re) +
      (η*(p₁ a b-p₆ a b)).im * (H-(η*p₁₇ a b).re) = 0 := by
  have ep := signed_gap_relation a b
  have e : (η*(p₁ a b-p₃ a b))*(η*(p₂₀ a b-p₁₂ a b)) +
      (η*(p₁ a b-p₆ a b))*(η*(p₁₇ a b-p₁₂ a b)) =
      (η*(p₁ a b-p₁₂ a b))*(η*(p₁ a b+p₁₁ a b-p₃ a b-p₆ a b)) := by
    calc
      _ = η^2 * ((p₁ a b-p₃ a b)*(p₂₀ a b-p₁₂ a b) +
        (p₁ a b-p₆ a b)*(p₁₇ a b-p₁₂ a b)) := by ring
      _ = η^2 * ((p₁ a b-p₁₂ a b)*(p₁ a b+p₁₁ a b-p₃ a b-p₆ a b)) := by rw [ep]
      _ = _ := by ring
  have h13 : (η*(p₁ a b-p₃ a b)).re = 0 := by simp [mul_sub,h₁,h₃]
  have h16 : (η*(p₁ a b-p₆ a b)).re = 0 := by simp [mul_sub,h₁,h₆]
  have h112 : (η*(p₁ a b-p₁₂ a b)).re = 0 := by simp [mul_sub,h₁,h₁₂]
  have hf : (η*(p₁ a b+p₁₁ a b-p₃ a b-p₆ a b)).re = 0 := by
    simp [mul_sub,mul_add,h₁,h₁₁,h₃,h₆]
  have hi := congrArg Complex.im e
  simp only [Complex.add_im,Complex.mul_im,h13,h16,h112,hf,
    zero_mul,mul_zero,zero_add,add_zero] at hi
  have hx : (η*(p₂₀ a b-p₁₂ a b)).re = (η*p₂₀ a b).re-H := by simp [mul_sub,h₁₂]
  have hy : (η*(p₁₇ a b-p₁₂ a b)).re = (η*p₁₇ a b).re-H := by simp [mul_sub,h₁₂]
  rw [hx,hy] at hi
  simp only [Complex.mul_im]
  linarith

end ZhengT55
end MOC

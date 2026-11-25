import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The reciprocal certificate for the two-budget bound in paper case T15. -/

namespace MOC

/-- The T15 reciprocal quotients force the order of the two positive
chart parameters. Both denominators have a nonzero imaginary part. -/
theorem fourT15_parameter_order_of_quotients (X T μ : ℝ) (U V : ℂ)
    (hX : 0 < X) (hT : 0 < T) (hU : 0 < μ * U.im) (hV : 0 < μ * V.im) :
    let C := 1 + X
    let H := 1 + T
    let k := T * X - 1
    let D₁ := (C : ℂ) * U + k
    let D₂ := (k : ℂ) - (H : ℂ) * V
    let Z := ((T - X : ℝ) : ℂ) * U * V - ((H * X : ℝ) : ℂ) * U - ((T * C : ℝ) : ℂ) * V
    0 ≤ μ * (Z / D₁).im → 0 ≤ -μ * (Z / D₂).im → X ≤ T := by
  intro C H k D₁ D₂ Z hm hn
  have hC : 0 < C := by dsimp only [C]; positivity
  have hH : 0 < H := by dsimp only [H]; positivity
  have hi₁ : D₁.im = C * U.im := by simp [D₁, Complex.add_im, Complex.mul_im]
  have hi₂ : D₂.im = -H * V.im := by simp [D₂, Complex.sub_im, Complex.mul_im, neg_mul]
  have hi₁p : 0 < μ * D₁.im := by
    rw [hi₁]
    have h : μ * (C * U.im) = C * (μ * U.im) := by ring
    rw [h]
    exact mul_pos hC hU
  have hi₂n : μ * D₂.im < 0 := by
    rw [hi₂]
    have h : μ * (-H * V.im) = -H * (μ * V.im) := by ring
    rw [h]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hH) hV
  have h₁ : D₁ ≠ 0 := fun h => hi₁p.ne' (by simp [h])
  have h₂ : D₂ ≠ 0 := fun h => hi₂n.ne (by simp [h])
  have hCc : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have hHc : (H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hH.ne'
  let α := (X - T) / (C * H)
  let β := T * C / H
  let γ := X * H / C
  have hZ : Z = (α : ℂ) * D₁ * D₂ - (β : ℂ) * D₁ + (γ : ℂ) * D₂ := by
    dsimp only [Z, α, β, γ, D₁, D₂]
    push_cast
    field_simp [hCc, hHc]
    dsimp only [C, H, k]
    push_cast
    ring
  have hZ₁ : Z / D₁ = (α : ℂ) * D₂ - β + (γ : ℂ) * (D₂ / D₁) := by
    rw [hZ]
    field_simp [h₁] <;> ring
  have hZ₂ : Z / D₂ = (α : ℂ) * D₁ - (β : ℂ) * (D₁ / D₂) + γ := by
    rw [hZ]
    field_simp [h₂] <;> ring
  have hIm₁ : (Z / D₁).im = α * D₂.im + γ * (D₂ / D₁).im := by
    rw [hZ₁]
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im]
  have hIm₂ : (Z / D₂).im = α * D₁.im - β * (D₁ / D₂).im := by
    rw [hZ₂]
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im]
  by_contra! hXT
  have hα : 0 < α := div_pos (sub_pos.mpr hXT) (mul_pos hC hH)
  have hβ : 0 < β := div_pos (mul_pos hT hC) hH
  have hγ : 0 < γ := div_pos (mul_pos hX hH) hC
  have him₁ : 0 < μ * (D₂ / D₁).im := by
    have he : μ * (Z / D₁).im = α * (μ * D₂.im) + γ * (μ * (D₂ / D₁).im) := by
      rw [hIm₁]
      ring
    have h := mul_neg_of_pos_of_neg hα hi₂n
    have hprod : 0 < γ * (μ * (D₂ / D₁).im) := by linarith only [hm, he, h]
    exact (mul_pos_iff_of_pos_left hγ).mp hprod
  have him₂ : 0 < μ * (D₁ / D₂).im := by
    have he : -μ * (Z / D₂).im = -α * (μ * D₁.im) + β * (μ * (D₁ / D₂).im) := by
      rw [hIm₂]
      ring
    have h := mul_pos hα hi₁p
    have hprod : 0 < β * (μ * (D₁ / D₂).im) := by linarith only [hn, he, h]
    exact (mul_pos_iff_of_pos_left hβ).mp hprod
  have hInv : D₁ / D₂ = (D₂ / D₁)⁻¹ := by rw [inv_div]
  rw [hInv, Complex.inv_im] at him₂
  have hN : 0 < Complex.normSq (D₂ / D₁) := Complex.normSq_pos.mpr (div_ne_zero h₂ h₁)
  have he : μ * (-((D₂ / D₁).im) / Complex.normSq (D₂ / D₁)) =
      -(μ * (D₂ / D₁).im) / Complex.normSq (D₂ / D₁) := by ring
  rw [he] at him₂
  exact (not_lt_of_ge (div_neg_of_neg_of_pos (neg_lt_zero.mpr him₁) hN).le) him₂

/-- The T15 chart order and the two donor bounds imply the two-budget
capacity without dividing by a donor. -/
theorem fourT15_two_budget_of_order {X T a b d : ℝ}
    (hXT : X ≤ T) (hb : 0 ≤ b) (hd : 0 ≤ d) (hdb : d ≤ X * b)
    (hda : T * d ≤ a) : d ^ 2 ≤ a * b := by
  calc
    d ^ 2 = d * d := pow_two _
    _ ≤ d * (X * b) := mul_le_mul_of_nonneg_left hdb hd
    _ = X * (d * b) := by ring
    _ ≤ T * (d * b) := mul_le_mul_of_nonneg_right hXT (mul_nonneg hd hb)
    _ = (T * d) * b := by ring
    _ ≤ a * b := mul_le_mul_of_nonneg_right hda hb

end MOC

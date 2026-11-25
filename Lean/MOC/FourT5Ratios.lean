import MOC.FourT5Chart
import Mathlib.Tactic.FieldSimp

/-! Ratios of T5 matching products after cancelling the common chart factors. -/

namespace MOC

set_option maxHeartbeats 1400000 in
/-- The ten original T5 ratios needed for the capacity argument. -/
theorem fourT5_exact_pole_ratios (x t r u z w v : ℂ)
    (hv : v ≠ 0) (hu : u ≠ 0) (hzw : z ≠ w) (hf : x - t * v ≠ 0)
    (hG : x - (t + u) * v ≠ 0) (hP : x - (t + u) * v - r ≠ 0)
    (hz : z = r * v / (x - (t + u) * v)) (hw : w = (x - r - t * v) / u) :
    let F := fourT5PoleProduct z x w v t
    let R (i : Fin 24) := (F i - F 1) / (v * (z - w))
    let f := x - t * v
    let G := x - (t + u) * v
    let P := G - r
    let W := f - r
    let V := W - u
    let K := u * x - W
    let C := t * (1 - v)
    R 0 = x / v - x ∧ R 7 = t - t * v * (r + u) / f ∧ R 9 = t - t * v * (r + u * x) / f ∧
    R 10 = t - 1 + r - r * (x - 1) / f ∧ R 11 = -K * (t * v - 1) / f + C ∧
    R 12 = -(x - r - t - u) - r * V / P ∧ R 13 = -t * (x - v) * V * G / (f * P) + C ∧
    R 16 = -W * (x - v) * (t * v - 1) * G / (v * f * P) + C ∧
    R 17 = -K * (t * v - 1) * G / (f * P) + C ∧ R 22 = W * (x - v) * (r - t * G) / (f * P) + C := by
  intro F R f G P W V K C
  let D := v * (z - w)
  have hf' : f ≠ 0 := hf
  have hG' : G ≠ 0 := hG
  have hP' : P ≠ 0 := hP
  have hD₀ : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hz' : z = r * v / G := hz
  have hw' : w = W / u := by rw [hw]; dsimp only [W, f]; ring
  have hzw_eq : z - w = -f * P / (u * G) := by
    rw [hz', hw']
    field_simp [hu, hG']
    dsimp only [W, P, G, f]
    ring
  let Dn := -v * f * P
  have hDn : Dn ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hv) hf') hP'
  have hD : D = Dn / (u * G) := by
    dsimp only [D]
    rw [hzw_eq]
    field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring
  have hzv : z - v = -v * P / G := by rw [hz']; field_simp [hG']; dsimp only [P]; ring
  have hztv : z - t * v = v * (r - t * G) / G := by rw [hz']; field_simp [hG'] <;> ring
  have hw₁ : w - 1 = V / u := by rw [hw']; field_simp [hu]
  have hxw : x - w = K / u := by rw [hw']; field_simp [hu]
  have hF₀ : F 0 = (1 - v) * (z - w) * f := fourT5_pole_product_values z x w v t 0
  have hF₁ : F 1 = t * v * (v - 1) * (z - w) := fourT5_pole_product_values z x w v t 1
  have hF₇ : F 7 = t * v * (z - v) * (w - 1) := fourT5_pole_product_values z x w v t 6
  have hF₉ : F 9 = -t * v * (z - v) * (x - w) := fourT5_pole_product_values z x w v t 8
  have hF₁₀ : F 10 = w * (z - v) * (t * v - 1) := fourT5_pole_product_values z x w v t 9
  have hF₁₁ : F 11 = -(z - v) * (x - w) * (t * v - 1) := fourT5_pole_product_values z x w v t 10
  have hF₁₂ : F 12 = v * (w - 1) * f := fourT5_pole_product_values z x w v t 11
  have hF₁₃ : F 13 = t * v * (x - v) * (w - 1) := fourT5_pole_product_values z x w v t 12
  have hF₁₆ : F 16 = w * (x - v) * (t * v - 1) := fourT5_pole_product_values z x w v t 13
  have hF₁₇ : F 17 = v * (x - w) * (t * v - 1) := fourT5_pole_product_values z x w v t 14
  have hF₂₂ : F 22 = -w * (x - v) * (z - t * v) := fourT5_pole_product_values z x w v t 15
  have hR (i : Fin 24) : R i = F i / D + C := by
    change (F i - F 1) / D = _
    have h : F 1 = D * (t * (v - 1)) := by rw [hF₁]; dsimp only [D]; ring
    rw [h, sub_div, mul_div_cancel_left₀ _ hD₀]
    dsimp only [C]
    ring
  have hRnorm (i : Fin 24) (a b : ℂ) (hb : b ≠ 0)
      (hnum : F i * (u * G) * b = a * Dn) : R i = a / b + C := by
    rw [hR, hD, div_div_eq_mul_div, (div_eq_div_iff hDn hb).mpr hnum]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR, hF₀]
    dsimp only [D]
    field_simp [hv, sub_ne_zero.mpr hzw] <;> dsimp only [f, C] <;> ring
  · rw [hRnorm 7 (t * v * V) f hf' (by
      rw [hF₇, hzv, hw₁]
      field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring)]
    field_simp [hf'] <;> dsimp only [V, W, C] <;> ring
  · rw [hRnorm 9 (-t * v * K) f hf' (by
      rw [hF₉, hzv, hxw]
      field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring)]
    field_simp [hf'] <;> dsimp only [K, W, C] <;> ring
  · rw [hRnorm 10 (W * (t * v - 1)) f hf' (by
      rw [hF₁₀, hzv, hw']
      field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring)]
    field_simp [hf'] <;> dsimp only [W, f, C] <;> ring
  · apply hRnorm 11 _ _ hf'
    rw [hF₁₁, hzv, hxw]
    field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring
  · rw [hRnorm 12 (-V * G) P hP' (by
      rw [hF₁₂, hw₁]
      field_simp [hu] <;> dsimp only [Dn] <;> ring)]
    field_simp [hP'] <;> dsimp only [P, V, W, f, C] <;> ring
  · apply hRnorm 13 _ _ (mul_ne_zero hf' hP')
    rw [hF₁₃, hw₁]
    field_simp [hu] <;> dsimp only [Dn] <;> ring
  · apply hRnorm 16 _ _ (mul_ne_zero (mul_ne_zero hv hf') hP')
    rw [hF₁₆, hw']
    field_simp [hu] <;> dsimp only [Dn] <;> ring
  · apply hRnorm 17 _ _ (mul_ne_zero hf' hP')
    rw [hF₁₇, hxw]
    field_simp [hu] <;> dsimp only [Dn] <;> ring
  · apply hRnorm 22 _ _ (mul_ne_zero hf' hP')
    rw [hF₂₂, hztv, hw']
    field_simp [hu, hG'] <;> dsimp only [Dn] <;> ring

end MOC

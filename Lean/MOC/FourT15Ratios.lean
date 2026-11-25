import MOC.FourT15Chart

/-! Factored original-product ratios for the T15 reciprocal obstruction. -/

namespace MOC

set_option maxHeartbeats 1400000 in
/-- Six T15 ratios have expressions using only `w-1` and `w-v`. -/
theorem fourT15_exact_pole_ratios (z x w v t : ℂ) (hv : v ≠ 0) (hw₁ : w ≠ 1)
    (hwv : w ≠ v) (hQ : v + 1 - w ≠ 0) (hz : z = v / (v + 1 - w)) :
    let R := fourT15PoleRatio z x w v t
    let U := (t * v - 1) / (w - 1)
    let V := (v - x) / (w - v)
    let f := x - t * v
    R 10 = 1 - t - U ∧ R 11 = (1 - x) * R 10 + x * (1 - t) ∧
    R 13 = t * (x - 1 + V) ∧ R 19 = t * (x - 1) + (t - 1) * V ∧
    R 8 = x - t + f / (w - 1) ∧ R 12 = x - t - f / (w - v) := by
  intro R U V f
  let F := fourT5PoleProduct z x w v t
  let D := v * (z - w)
  let Q := v + 1 - w
  let W := w - 1
  let Y := w - v
  let N := v * W * Y
  have hW : W ≠ 0 := sub_ne_zero.mpr hw₁
  have hY : Y ≠ 0 := sub_ne_zero.mpr hwv
  have hQ' : Q ≠ 0 := hQ
  have hN : N ≠ 0 := mul_ne_zero (mul_ne_zero hv hW) hY
  have hD_eq : D = N / Q := by
    dsimp only [D, N, W, Y]
    rw [hz]
    change v * (v / Q - w) = _
    field_simp [hQ']
    dsimp only [Q]
    ring
  have hD : D ≠ 0 := by rw [hD_eq]; exact div_ne_zero hN hQ'
  have hzv : z - v = v * Y / Q := by
    rw [hz]
    change v / Q - v = _
    field_simp [hQ']
    dsimp only [Q, Y]
    ring
  have hzt : z - t * v = v * (1 - t * Q) / Q := by
    rw [hz]
    change v / Q - t * v = _
    field_simp [hQ'] <;> ring
  have hF₁ : F 1 = D * (t * (v - 1)) := by
    rw [show F 1 = t * v * (v - 1) * (z - w) from fourT5_pole_product_values z x w v t 1]
    dsimp only [D]
    ring
  have hF₈ : F 8 = -w * (z - v) * f := fourT5_pole_product_values z x w v t 7
  have hF₁₀ : F 10 = w * (z - v) * (t * v - 1) := fourT5_pole_product_values z x w v t 9
  have hF₁₁ : F 11 = -(z - v) * (x - w) * (t * v - 1) := fourT5_pole_product_values z x w v t 10
  have hF₁₂ : F 12 = v * W * f := fourT5_pole_product_values z x w v t 11
  have hF₁₃ : F 13 = t * v * (x - v) * W := fourT5_pole_product_values z x w v t 12
  have hF₁₉ : F 19 = (1 - w) * (x - v) * (z - t * v) := by
    have h0 : (fourPerm 19).symm 0 = 1 := by decide +kernel
    have h1 : (fourPerm 19).symm 1 = 3 := by decide +kernel
    have h3 : (fourPerm 19).symm 3 = 0 := by decide +kernel
    have hv0 : (![z, 1, 0, x] : Fin 4 → ℂ) 0 = z := rfl
    have hv1 : (![z, 1, 0, x] : Fin 4 → ℂ) 1 = 1 := rfl
    have hv3 : (![z, 1, 0, x] : Fin 4 → ℂ) 3 = x := rfl
    simp only [F, fourT5PoleProduct, h0, h1, h3, hv0, hv1, hv3]
  have hR (i : Fin 24) (a b : ℂ) (hb : b ≠ 0) (hn : F i * Q * b = a * N) :
      R i = t * (v - 1) - a / b := by
    change (F 1 - F i) / D = _
    rw [hF₁, sub_div, mul_div_cancel_left₀ _ hD, hD_eq, div_div_eq_mul_div, (div_eq_div_iff hN hb).mpr hn]
  have h10 : R 10 = 1 - t - U := by
    rw [hR 10 (w * (t * v - 1)) W hW (by
      rw [hF₁₀, hzv]; field_simp [hQ'] <;> dsimp only [N] <;> ring)]
    change t * (v - 1) - w * (t * v - 1) / W = 1 - t - (t * v - 1) / W
    field_simp [hW] <;> dsimp only [W] <;> ring
  have h13 : R 13 = t * (x - 1 + V) := by
    rw [hR 13 (t * (x - v) * Q) Y hY (by rw [hF₁₃]; dsimp only [N]; ring)]
    change t * (v - 1) - t * (x - v) * Q / Y = t * (x - 1 + (v - x) / Y)
    field_simp [hY] <;> dsimp only [Q, Y] <;> ring
  refine ⟨h10, ?_, h13, ?_, ?_, ?_⟩
  · rw [h10, hR 11 (-(x - w) * (t * v - 1)) W hW (by
      rw [hF₁₁, hzv]; field_simp [hQ'] <;> dsimp only [N] <;> ring)]
    change t * (v - 1) - (-(x - w) * (t * v - 1)) / W =
      (1 - x) * (1 - t - (t * v - 1) / W) + x * (1 - t)
    field_simp [hW] <;> dsimp only [W] <;> ring
  · rw [hR 19 ((v - x) * (1 - t * Q)) Y hY (by
      rw [hF₁₉, hzt]; field_simp [hQ'] <;> dsimp only [N, W] <;> ring)]
    change t * (v - 1) - (v - x) * (1 - t * Q) / Y = t * (x - 1) + (t - 1) * ((v - x) / Y)
    field_simp [hY] <;> dsimp only [Q, Y] <;> ring
  · rw [hR 8 (-w * f) W hW (by rw [hF₈, hzv]; field_simp [hQ'] <;> dsimp only [N] <;> ring)]
    change t * (v - 1) - (-w * f) / W = x - t + f / W
    field_simp [hW] <;> dsimp only [W, f] <;> ring
  · rw [hR 12 (f * Q) Y hY (by rw [hF₁₂]; dsimp only [N]; ring)]
    change t * (v - 1) - f * Q / Y = x - t - f / Y
    field_simp [hY] <;> dsimp only [Q, Y, f] <;> ring

end MOC

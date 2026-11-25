import MOC.FourT3Chart
import Mathlib.Tactic.FieldSimp

/-! Factored expressions for the original T3 matching products. -/

namespace MOC

private def t3RatioIndices : Fin 11 → Fin 24 := ![0, 4, 6, 9, 10, 12, 13, 14, 18, 20, 22]

private theorem t3RatioProductValues (z x w v t : ℂ) (i : Fin 11) :
    fourT3PoleProduct z x w v t (t3RatioIndices i) =
      (![v * (z - w) * (t * v - 1), (1 - v) * (z - w) * (x - t * v),
        w * (z - v) * (t * v - 1), -t * v * (z - v) * (x - w),
        (z - v) * (1 - w) * (x - t * v), w * (v - 1) * (z - t * v),
        -w * (x - v) * (z - t * v), v * (w - 1) * (z - t * v),
        w * (v - 1) * (x - t * v), v * (w - 1) * (x - t * v),
        t * v * (x - v) * (w - 1)] : Fin 11 → ℂ) i := by
  have h : ∀ k : Fin 11,
      let σ := (fourPerm (t3RatioIndices k)).symm
      σ 0 = (![0, 0, 1, 3, 2, 1, 1, 2, 1, 2, 2] : Fin 11 → Fin 4) k ∧
      σ 1 = (![1, 2, 0, 0, 0, 2, 3, 1, 2, 1, 3] : Fin 11 → Fin 4) k ∧
      σ 2 = (![2, 3, 2, 1, 3, 0, 0, 0, 3, 3, 1] : Fin 11 → Fin 4) k := by
    decide +kernel
  obtain ⟨h₀, h₁, h₂⟩ := h i
  dsimp only [fourT3PoleProduct]
  rw [h₀, h₁, h₂]
  fin_cases i <;> simp [Matrix.cons_val] <;> ring_nf <;> simp

set_option maxHeartbeats 1400000 in
/-- Original T3 products in factored chart coordinates. The quotient at
the suppressed pole is never used, and the common finite factors are nonzero. -/
theorem fourT3_exact_pole_ratios (x t r u z w v : ℂ)
    (hv : v ≠ 0) (hzw : z ≠ w) (hf : x - t * v ≠ 0)
    (hG : (u + t) * v - x ≠ 0) (hK' : z - 1 - r ≠ 0)
    (hz : z = u * v / ((u + t) * v - x))
    (hw : w = (v * (z - 1) - r * z) / (z - 1 - r)) :
    let F := fourT3PoleProduct z x w v t
    let R (i : Fin 24) := (F i - F 0) / (v * (z - w))
    let f := x - t * v
    let G := (u + t) * v - x
    let L := u - G
    let V := v - 1 - r
    let W := f - r * u
    let J := u - t * G
    let C := 1 - t * v
    L ≠ 0 ∧ R 4 = x / v + (1 - x - t) ∧ R 6 = r * u * (1 - t * v) / f ∧
    R 9 = -t * (f * (x - v) + r * (u * v - x * G)) / f + C ∧
    R 10 = -V * f / v + C ∧ R 12 = W * (v - 1) * J / (f * L) + C ∧
    R 13 = -W * (x - v) * J / (f * L) + C ∧
    R 14 = V * ((1 - t) * u) / L + (1 - t * (1 + r)) ∧
    R 18 = W * (v - 1) * G / (v * L) + C ∧ R 20 = V * f * G / (v * L) + C ∧
    R 22 = t * V * (x - v) * G / (v * L) + C := by
  intro F R f G L V W J C
  let D := v * (z - w)
  let K := f - r * G
  have hf' : f ≠ 0 := hf
  have hG' : G ≠ 0 := hG
  have hz' : z = u * v / G := hz
  have hD₀ : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hz₁ : z - 1 = f / G := by rw [hz']; field_simp [hG']; dsimp only [f, G]; ring
  have hK_eq : z - 1 - r = K / G := by rw [hz₁]; field_simp [hG']; dsimp only [K]; ring
  have hK : K ≠ 0 := by
    intro h
    rw [hK_eq, h, zero_div] at hK'
    exact hK' rfl
  have hw_eq : w = v * W / K := by
    rw [hw, hK_eq, hz₁, hz', div_div_eq_mul_div]
    field_simp [hG', hK] <;> dsimp only [W] <;> ring
  have hw₁ : w - 1 = V * f / K := by
    rw [hw_eq]
    field_simp [hK]
    dsimp only [W, K, V, G, f]
    ring
  have h₁w : 1 - w = -V * f / K := by
    rw [show 1 - w = -(w - 1) by ring, hw₁]
    field_simp [hK] <;> ring
  have hxw : x - w = (f * (x - v) + r * (u * v - x * G)) / K := by
    rw [hw_eq]
    field_simp [hK]
    dsimp only [W, K]
    ring
  have hzv : z - v = v * L / G := by
    rw [hz']
    field_simp [hG'] <;> dsimp only [L] <;> ring
  have hztv : z - t * v = v * J / G := by
    rw [hz']
    field_simp [hG'] <;> dsimp only [J] <;> ring
  have hzw_eq : z - w = v * f * L / (G * K) := by
    rw [hw_eq, hz']
    field_simp [hG', hK] <;> dsimp only [W, K, L] <;> ring
  have hL : L ≠ 0 := by
    intro h
    apply sub_ne_zero.mpr hzw
    rw [hzw_eq, h, mul_zero, zero_div]
  have hD : D = v ^ 2 * f * L / (G * K) := by
    dsimp only [D]
    rw [hzw_eq]
    field_simp [hG', hK] <;> ring
  have hF₀ : F 0 = D * (t * v - 1) := t3RatioProductValues z x w v t 0
  have hF₄ : F 4 = (1 - v) * (z - w) * f := t3RatioProductValues z x w v t 1
  have hF₆ : F 6 = w * (z - v) * (t * v - 1) := t3RatioProductValues z x w v t 2
  have hF₉ : F 9 = -t * v * (z - v) * (x - w) := t3RatioProductValues z x w v t 3
  have hF₁₀ : F 10 = (z - v) * (1 - w) * f := t3RatioProductValues z x w v t 4
  have hF₁₂ : F 12 = w * (v - 1) * (z - t * v) := t3RatioProductValues z x w v t 5
  have hF₁₃ : F 13 = -w * (x - v) * (z - t * v) := t3RatioProductValues z x w v t 6
  have hF₁₄ : F 14 = v * (w - 1) * (z - t * v) := t3RatioProductValues z x w v t 7
  have hF₁₈ : F 18 = w * (v - 1) * f := t3RatioProductValues z x w v t 8
  have hF₂₀ : F 20 = v * (w - 1) * f := t3RatioProductValues z x w v t 9
  have hF₂₂ : F 22 = t * v * (x - v) * (w - 1) := t3RatioProductValues z x w v t 10
  have hR (i : Fin 24) : R i = F i / D + C := by
    change (F i - F 0) / D = _
    rw [hF₀, sub_div, mul_div_cancel_left₀ _ hD₀]
    dsimp only [C]
    ring
  refine ⟨hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR, hF₄]
    dsimp only [D]
    field_simp [hv, sub_ne_zero.mpr hzw] <;> dsimp only [C, f] <;> ring
  · rw [hR, hF₆, hw_eq, hzv, hD, div_div_eq_mul_div]
    field_simp [hG', hK, hv, hf', hL] <;> dsimp only [C, W] <;> ring
  · rw [hR, hF₉, hzv, hxw, hD, div_div_eq_mul_div]
    field_simp [hG', hK, hv, hf', hL] <;> ring
  · rw [hR, hF₁₀, hzv, h₁w, hD, div_div_eq_mul_div]
    field_simp [hG', hK, hv, hf', hL] <;> ring
  · rw [hR, hF₁₂, hw_eq, hztv, hD, div_div_eq_mul_div]
    field_simp [hG', hK, hv, hf', hL] <;> ring
  · rw [hR, hF₁₃, hw_eq, hztv, hD, div_div_eq_mul_div]
    field_simp [hG', hK, hv, hf', hL] <;> ring
  · rw [hR, hF₁₄, hw₁, hztv, hD, div_div_eq_mul_div]
    field_simp [hG', hK, hv, hf', hL] <;> dsimp only [V, L, C, J] <;> ring
  · rw [hR, hF₁₈, hw_eq, hD, div_div_eq_mul_div]
    field_simp [hG', hK, hv, hf', hL] <;> ring
  · rw [hR, hF₂₀, hw₁, hD, div_div_eq_mul_div]
    field_simp [hG', hK, hv, hf', hL] <;> ring
  · rw [hR, hF₂₂, hw₁, hD, div_div_eq_mul_div]
    field_simp [hG', hK, hv, hf', hL] <;> ring

end MOC

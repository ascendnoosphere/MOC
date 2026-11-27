import MOC.FourMixedBudgetChart
import Mathlib.Tactic.FieldSimp

/-! The nonreal ordered-ratio pattern pole chart, with its real parameter stratum detected
by the gap at index zero. -/

namespace MOC

/-- ordered-ratio pattern uses the negative of the mixed-budget pattern original product convention. -/
noncomputable def fourOrderedRatioPoleRatio (z x w v t : ℂ) (i : Fin 24) : ℂ :=
  (fourMixedBudgetPoleProduct z x w v t 1 - fourMixedBudgetPoleProduct z x w v t i) / (v * (z - w))

/-- Real `x` and `v` make the zeroth normalized ordered-ratio pattern gap zero. -/
theorem fourOrderedRatio_pole_ratio_zero (z x w v t : ℂ) (hv : v ≠ 0) (hzw : z ≠ w) :
    fourOrderedRatioPoleRatio z x w v t 0 = x - x / v := by
  have h1 : fourMixedBudgetPoleProduct z x w v t 1 = t * v * (v - 1) * (z - w) :=
    fourMixedBudget_pole_product_values z x w v t 1
  have h0 : fourMixedBudgetPoleProduct z x w v t 0 = (1 - v) * (z - w) * (x - t * v) :=
    fourMixedBudget_pole_product_values z x w v t 0
  rw [fourOrderedRatioPoleRatio, h1, h0]
  field_simp [hv, sub_ne_zero.mpr hzw] <;> ring

/-- The last two ordered-ratio pattern contacts force `z = v/(v+1-w)` when `v` is nonreal.
The real-`v` branch is tested by `fourOrderedRatio_pole_ratio_zero`. -/
theorem fourOrderedRatio_pole_chart (x t : ℝ) (z w v : ℂ) (hx : x ≠ 0) (ht : t ≠ 0)
    (hv : v ≠ 0) (hzw : z ≠ w) (hf : (x : ℂ) - (t : ℂ) * v ≠ 0) (hvi : v.im ≠ 0)
    (h6 : (fourOrderedRatioPoleRatio z x w v t 6).im = 0) (h7 : (fourOrderedRatioPoleRatio z x w v t 7).im = 0) :
    v + 1 - w ≠ 0 ∧ z = v / (v + 1 - w) := by
  let D := v * (z - w)
  let f := (x : ℂ) - (t : ℂ) * v
  let R := fourOrderedRatioPoleRatio z x w v t
  let J := (x : ℂ) - (t : ℂ) - R 6
  have hD : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hf' : f ≠ 0 := hf
  have hf₁ : fourMixedBudgetPoleProduct z x w v t 1 = D * ((t : ℂ) * (v - 1)) := by
    rw [show fourMixedBudgetPoleProduct z x w v t 1 = (t : ℂ) * v * (v - 1) * (z - w) from
      fourMixedBudget_pole_product_values z x w v t 1]
    dsimp only [D]
    ring
  have hf₆ : fourMixedBudgetPoleProduct z x w v t 6 = -(z - v) * (w - 1) * f := by
    rw [show fourMixedBudgetPoleProduct z x w v t 6 = (z - v) * (1 - w) * f from
      fourMixedBudget_pole_product_values z x w v t 5]
    ring
  have hf₇ : fourMixedBudgetPoleProduct z x w v t 7 = (t : ℂ) * v * (z - v) * (w - 1) :=
    fourMixedBudget_pole_product_values z x w v t 6
  have hR6 : R 6 = (t : ℂ) * (v - 1) + (z - v) * (w - 1) * f / D := by
    change (fourMixedBudgetPoleProduct z x w v t 1 - fourMixedBudgetPoleProduct z x w v t 6) / D = _
    rw [hf₁, hf₆, sub_div, mul_div_cancel_left₀ _ hD]
    ring
  have hR7 : R 7 = (t : ℂ) * (v - 1) - (t : ℂ) * v * (z - v) * (w - 1) / D := by
    change (fourMixedBudgetPoleProduct z x w v t 1 - fourMixedBudgetPoleProduct z x w v t 7) / D = _
    rw [hf₁, hf₇, sub_div, mul_div_cancel_left₀ _ hD]
  have hRJ : R 7 + t = ((t : ℂ) * v / f) * J := by
    rw [hR7]
    dsimp only [J]
    rw [hR6]
    field_simp [hD, hf']
    dsimp only [f]
    ring
  have hJ : J = f * (z * (v + 1 - w) - v) / D := by
    dsimp only [J]
    rw [hR6]
    field_simp [hD]
    dsimp only [D, f]
    ring
  have hJI : J.im = 0 := by
    change (R 6).im = 0 at h6
    simp only [J, Complex.sub_im, Complex.ofReal_im, sub_self, h6]
  have hfactorI : ((t : ℂ) * v / f).im = t * x * v.im / Complex.normSq f := by
    rw [Complex.div_im]
    have hfI : f.im = -t * v.im := by simp [f, Complex.sub_im, Complex.mul_im, neg_mul]
    have hfR : f.re = x - t * v.re := by simp [f, Complex.sub_re, Complex.mul_re]
    rw [hfI, hfR]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
      zero_mul, add_zero, sub_zero]
    ring
  have hfactor : ((t : ℂ) * v / f).im ≠ 0 := by
    rw [hfactorI]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero ht hx) hvi) (Complex.normSq_pos.mpr hf').ne'
  have hJR : J.re = 0 := by
    have h := congrArg Complex.im hRJ
    change (R 7).im = 0 at h7
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, add_zero, h7, hJI, mul_zero, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hfactor
  have hzero : J = 0 := Complex.ext (by simpa using hJR) (by simpa using hJI)
  have hfz := (div_eq_zero_iff.mp (hJ.symm.trans hzero)).resolve_right hD
  have hz : z * (v + 1 - w) = v := sub_eq_zero.mp ((mul_eq_zero.mp hfz).resolve_left hf')
  have hnz : v + 1 - w ≠ 0 := by
    intro h
    rw [h, mul_zero] at hz
    exact hv hz.symm
  exact ⟨hnz, (eq_div_iff hnz).mpr hz⟩

end MOC

/-! Factored original-product ratios for the ordered-ratio pattern reciprocal obstruction. -/

namespace MOC

set_option maxHeartbeats 1400000 in
/-- Six ordered-ratio pattern ratios have expressions using only `w-1` and `w-v`. -/
theorem fourOrderedRatio_exact_pole_ratios (z x w v t : ℂ) (hv : v ≠ 0) (hw₁ : w ≠ 1)
    (hwv : w ≠ v) (hQ : v + 1 - w ≠ 0) (hz : z = v / (v + 1 - w)) :
    let R := fourOrderedRatioPoleRatio z x w v t
    let U := (t * v - 1) / (w - 1)
    let V := (v - x) / (w - v)
    let f := x - t * v
    R 10 = 1 - t - U ∧ R 11 = (1 - x) * R 10 + x * (1 - t) ∧
    R 13 = t * (x - 1 + V) ∧ R 19 = t * (x - 1) + (t - 1) * V ∧
    R 8 = x - t + f / (w - 1) ∧ R 12 = x - t - f / (w - v) := by
  intro R U V f
  let F := fourMixedBudgetPoleProduct z x w v t
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
    rw [show F 1 = t * v * (v - 1) * (z - w) from fourMixedBudget_pole_product_values z x w v t 1]
    dsimp only [D]
    ring
  have hF₈ : F 8 = -w * (z - v) * f := fourMixedBudget_pole_product_values z x w v t 7
  have hF₁₀ : F 10 = w * (z - v) * (t * v - 1) := fourMixedBudget_pole_product_values z x w v t 9
  have hF₁₁ : F 11 = -(z - v) * (x - w) * (t * v - 1) := fourMixedBudget_pole_product_values z x w v t 10
  have hF₁₂ : F 12 = v * W * f := fourMixedBudget_pole_product_values z x w v t 11
  have hF₁₃ : F 13 = t * v * (x - v) * W := fourMixedBudget_pole_product_values z x w v t 12
  have hF₁₉ : F 19 = (1 - w) * (x - v) * (z - t * v) := by
    have h0 : (fourPerm 19).symm 0 = 1 := by decide +kernel
    have h1 : (fourPerm 19).symm 1 = 3 := by decide +kernel
    have h3 : (fourPerm 19).symm 3 = 0 := by decide +kernel
    have hv0 : (![z, 1, 0, x] : Fin 4 → ℂ) 0 = z := rfl
    have hv1 : (![z, 1, 0, x] : Fin 4 → ℂ) 1 = 1 := rfl
    have hv3 : (![z, 1, 0, x] : Fin 4 → ℂ) 3 = x := rfl
    simp only [F, fourMixedBudgetPoleProduct, h0, h1, h3, hv0, hv1, hv3]
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

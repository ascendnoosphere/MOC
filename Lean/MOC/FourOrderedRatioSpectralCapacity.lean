import MOC.FourOrderedRatioCapacity
import MOC.FourOrderedRatioChart

/-! The original ordered-ratio pattern gap identities force the reciprocal capacity. -/

namespace MOC

set_option maxHeartbeats 1500000 in
/-- The ordered-ratio pattern projective chart satisfies the two-budget bound. A positive
defect forces nonreal `v` from the zeroth original gap. -/
theorem fourOrderedRatio_projective_capacity (x t : ℝ) (z w v η : ℂ)
    (hv : v ≠ 0) (hw₁ : w ≠ 1) (hwv : w ≠ v) (hzw : z ≠ w) (ht : t ≠ 0)
    (hf : (x : ℂ) - t * v ≠ 0) (hdir : (η * (v * (z - w))).re = 0) :
    let F := fourMixedBudgetPoleProduct z x w v t
    let g (i : Fin 24) := (η * (F 1 - F i)).re
    let d := g 0 - g 16
    (∀ i, 0 ≤ g i) → g 6 = 0 → g 7 = 0 → g 11 = g 10 + g 17 + d →
    g 19 = g 13 + g 22 + d → 0 < d → d ^ 2 ≤ g 10 * g 13 := by
  intro F g d hg h6 h7 h11 h19 hd
  let D := v * (z - w)
  let R := fourOrderedRatioPoleRatio z x w v t
  let μ := (η * D).im
  have hD : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hgR (i : Fin 24) : g i = -μ * (R i).im := by
    have he : η * (F 1 - F i) = (η * D) * R i := by
      change η * (F 1 - F i) = (η * D) * ((F 1 - F i) / D)
      field_simp [hD] <;> ring
    change (η * (F 1 - F i)).re = _
    rw [he, Complex.mul_re, show (η * D).re = 0 from hdir, zero_mul, zero_sub, neg_mul]
  have h0' : 0 < g 0 := by dsimp only [d] at hd; linarith only [hd, hg 16]
  have h0im : (R 0).im = x * v.im / Complex.normSq v := by
    change (fourOrderedRatioPoleRatio z x w v t 0).im = _
    rw [fourOrderedRatio_pole_ratio_zero _ _ _ _ _ hv hzw, Complex.sub_im, Complex.div_im]
    simp [Complex.ofReal_re, Complex.ofReal_im]
  have hμ : μ ≠ 0 := by
    intro he
    rw [hgR, he, neg_zero, zero_mul] at h0'
    exact (lt_irrefl _) h0'
  have hx : x ≠ 0 := by
    intro he
    rw [hgR, h0im, he, zero_mul, zero_div, mul_zero] at h0'
    exact (lt_irrefl _) h0'
  have hvi : v.im ≠ 0 := by
    intro he
    rw [hgR, h0im, he, mul_zero, zero_div, mul_zero] at h0'
    exact (lt_irrefl _) h0'
  have hRi (i : Fin 24) (hi : g i = 0) : (R i).im = 0 := by
    rw [hgR] at hi
    exact (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr hμ)
  obtain ⟨hQ, hz⟩ := fourOrderedRatio_pole_chart x t z w v hx ht hv hzw hf hvi (hRi 6 h6) (hRi 7 h7)
  obtain ⟨hR10, hR11, hR13, hR19, hR8, hR12⟩ := fourOrderedRatio_exact_pole_ratios z x w v t hv hw₁ hwv hQ hz
  let W := w - 1
  let Y := w - v
  let U := ((t : ℂ) * v - 1) / W
  let V := (v - (x : ℂ)) / Y
  let f := (x : ℂ) - (t : ℂ) * v
  have hW : W ≠ 0 := sub_ne_zero.mpr hw₁
  have hY : Y ≠ 0 := sub_ne_zero.mpr hwv
  change R 10 = 1 - (t : ℂ) - U at hR10
  change R 11 = (1 - (x : ℂ)) * R 10 + (x : ℂ) * (1 - (t : ℂ)) at hR11
  change R 13 = (t : ℂ) * ((x : ℂ) - 1 + V) at hR13
  change R 19 = (t : ℂ) * ((x : ℂ) - 1) + ((t : ℂ) - 1) * V at hR19
  change R 8 = (x : ℂ) - (t : ℂ) + f / W at hR8
  change R 12 = (x : ℂ) - (t : ℂ) - f / Y at hR12
  have hg10 : g 10 = μ * U.im := by rw [hgR, hR10]; simp [Complex.sub_im]
  have hg13 : g 13 = -t * (μ * V.im) := by
    rw [hgR, hR13]
    simp [Complex.mul_im, Complex.add_im, Complex.sub_im] <;> ring
  have hg11 : g 11 = (1 - x) * g 10 := by
    rw [hgR 11, hgR 10, hR11]
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im] <;> ring
  have hg19 : g 19 = (1 - t) * (μ * V.im) := by
    rw [hgR, hR19]
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im] <;> ring
  have hbprod : 0 < -x * g 10 := by linarith only [h11, hg11, hg 17, hd]
  have hx' : x < 0 := neg_pos.mp (pos_of_mul_pos_left hbprod (hg 10))
  have hb : 0 < g 10 := (mul_pos_iff_of_pos_left (neg_pos.mpr hx')).mp hbprod
  have htg : t * (g 22 + d) = -g 13 := by
    have h : t * g 19 = (t - 1) * g 13 := by rw [hg19, hg13]; ring
    linear_combination h - t * h19
  have he : 0 < g 22 + d := add_pos_of_nonneg_of_pos (hg 22) hd
  have ht' : t < 0 := by
    have h : t * (g 22 + d) ≤ 0 := htg.symm ▸ (neg_nonpos.mpr (hg 13))
    exact lt_of_le_of_ne (nonpos_of_mul_nonpos_left h he) ht
  have ha : 0 < g 13 := by
    have h := mul_neg_of_neg_of_pos ht' he
    rw [htg] at h
    exact neg_lt_zero.mp h
  have hUV : 0 < μ * U.im ∧ 0 < μ * V.im := by
    refine ⟨hg10 ▸ hb, ?_⟩
    exact (mul_pos_iff_of_pos_left (neg_pos.mpr ht')).mp (hg13 ▸ ha)
  let X := -x
  let T := -t
  let C := 1 + X
  let H := 1 + T
  let k := T * X - 1
  let D₁ := (C : ℂ) * U + k
  let D₂ := (k : ℂ) - (H : ℂ) * V
  let Z := ((T - X : ℝ) : ℂ) * U * V - ((H * X : ℝ) : ℂ) * U - ((T * C : ℝ) : ℂ) * V
  have hX : 0 < X := neg_pos.mpr hx'
  have hT : 0 < T := neg_pos.mpr ht'
  have hC : 0 < C := by dsimp only [C]; positivity
  have hH : 0 < H := by dsimp only [H]; positivity
  have hD₁ : D₁ ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [D₁, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      zero_mul, add_zero, Complex.zero_im] at hh
    have hz := (mul_eq_zero.mp hh).resolve_left hC.ne'
    exact hUV.1.ne' (by simp [hz])
  have hD₂ : D₂ ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [D₂, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      zero_mul, add_zero, zero_sub, neg_eq_zero, Complex.zero_im] at hh
    have hz := (mul_eq_zero.mp hh).resolve_left hH.ne'
    exact hUV.2.ne' (by simp [hz])
  have hZ₁ : Z / D₁ = f / Y := by
    apply (div_eq_div_iff hD₁ hY).mpr
    dsimp only [Z, D₁, U, V, f]
    field_simp [hW, hY]
    dsimp only [C, H, k, X, T, W, Y]
    push_cast
    ring
  have hZ₂ : Z / D₂ = f / W := by
    apply (div_eq_div_iff hD₂ hW).mpr
    dsimp only [Z, D₂, U, V, f]
    field_simp [hW, hY]
    dsimp only [C, H, k, X, T, W, Y]
    push_cast
    ring
  have hm : 0 ≤ μ * (Z / D₁).im := by
    have he : g 12 = μ * (f / Y).im := by rw [hgR, hR12]; simp [Complex.sub_im]
    rw [hZ₁, ← he]
    exact hg 12
  have hn : 0 ≤ -μ * (Z / D₂).im := by
    have he : g 8 = -μ * (f / W).im := by rw [hgR, hR8]; simp [Complex.add_im, Complex.sub_im]
    rw [hZ₂, ← he]
    exact hg 8
  have hXT : X ≤ T := fourOrderedRatio_parameter_order_of_quotients X T μ U V hX hT hUV.1 hUV.2 hm hn
  have hdb : d ≤ X * g 10 := by dsimp only [X]; linarith only [h11, hg11, hg 17]
  have hda : T * d ≤ g 13 := by
    dsimp only [T]
    linarith only [htg, mul_nonneg (neg_pos.mpr ht').le (hg 22)]
  simpa only [mul_comm] using fourOrderedRatio_two_budget_of_order hXT hb.le hd.le hdb hda

end MOC

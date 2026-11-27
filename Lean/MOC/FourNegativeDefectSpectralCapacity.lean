import MOC.FourNegativeDefectChart
import MOC.FourNegativeDefectCapacity
import MOC.FourNegativeDefectMinor

/-! The distinct negative-defect pattern source gaps satisfy the two-budget bound. -/

namespace MOC

set_option maxHeartbeats 2500000 in
private theorem negativeDefect_defect_ratio_identity
    (x t r u v f G L V W J C : ℂ) (hv : v ≠ 0) (hfnz : f ≠ 0) (hLnz : L ≠ 0)
    (hf : f = x - t * v) (hG : G = (u + t) * v - x) (hL : L = u - G)
    (hV : V = v - 1 - r) (hW : W = f - r * u) (hJ : J = u - t * G)
    (hC : C = 1 - t * v) :
    t * (-(x / v + (1 - x - t)) + r * u * (1 - t * v) / f +
      (-V * f / v + C) - (W * (v - 1) * J / (f * L) + C) +
      (W * (v - 1) * G / (v * L) + C)) -
      (t * V * (x - v) * G / (v * L) + C) =
        -r * t ^ 2 + r * t * u + r * t + t - 1 := by
  field_simp (discharger := simp [hv, hfnz, hLnz]) only [hv, hfnz, hLnz]
  rw [hW, hV, hJ, hL, hC, hf, hG]
  ring

set_option maxHeartbeats 2500000 in
private theorem negativeDefect_residue_ratio_identity
    (x t r u v f G L V W J C : ℂ) (hfnz : f ≠ 0) (hLnz : L ≠ 0)
    (hf : f = x - t * v) (hG : G = (u + t) * v - x) (hL : L = u - G)
    (hV : V = v - 1 - r) (hW : W = f - r * u) (hJ : J = u - t * G)
    (hC : C = 1 - t * v) :
    (t - x) * ((-W * (x - v) * J / (f * L) + C) -
      (V * ((1 - t) * u) / L + (1 - t * (1 + r)))) +
      x * (1 - t) * (r * u * (1 - t * v) / f) -
      (1 - x) * (-t - u) * (V * ((1 - t) * u) / L + (1 - t * (1 + r))) =
        t * (r * t * x - r * x + x ^ 2 - 2 * x + 1) := by
  field_simp (discharger := simp [hfnz, hLnz]) only [hfnz, hLnz]
  rw [hW, hV, hJ, hL, hC, hf, hG]
  ring

set_option maxHeartbeats 2500000 in
/-- The exact negative-defect pattern capacity on the normalized projective chart. -/
theorem fourNegativeDefect_projective_capacity (x t r u : ℝ) (z w v η : ℂ)
    (hv : v ≠ 0) (hzw : z ≠ w) (hf : (x : ℂ) - t * v ≠ 0) (ht : t ≠ 0)
    (hG : ((u : ℂ) + t) * v - x ≠ 0) (hK : z - 1 - r ≠ 0)
    (hz : z = (u : ℂ) * v / (((u : ℂ) + t) * v - x))
    (hw : w = (v * (z - 1) - (r : ℂ) * z) / (z - 1 - r))
    (hdir : (η * (v * (z - w))).re = 0) :
    let F := fourNegativeDefectPoleProduct z x w v t
    let g (i : Fin 24) := (η * (F i - F 0)).re
    (∀ i, 0 ≤ g i) → g 21 = g 9 + fourNegativeDefectMinorDefect g → fourNegativeDefectMinorDefect g < 0 →
      (fourNegativeDefectMinorDefect g) ^ 2 ≤ g 6 * g 22 := by
  classical
  intro F g hg h21 hA
  let D := v * (z - w)
  let R (i : Fin 24) := (F i - F 0) / D
  let P := η * D
  let ρ := P.im * v.im
  let f := (x : ℂ) - t * v
  let G := ((u : ℂ) + t) * v - x
  let L := (u : ℂ) - G
  let V := v - 1 - r
  let W := f - (r : ℂ) * u
  let J := (u : ℂ) - (t : ℂ) * G
  let C := 1 - (t : ℂ) * v
  obtain ⟨hL, hR4, hR6, hR9, hR10, hR12, hR13, hR14, hR18, hR20, hR22⟩ :=
    fourNegativeDefect_exact_pole_ratios x t r u z w v hv hzw hf hG hK hz hw
  have hL' : L ≠ 0 := hL
  have hf' : f ≠ 0 := hf
  have hD : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hgR (i : Fin 24) : g i = -P.im * (R i).im := by
    have h : η * (F i - F 0) = P * R i := by
      dsimp only [P, R]
      field_simp [hD] <;> ring
    change (η * (F i - F 0)).re = _
    rw [h, Complex.mul_re, show P.re = 0 from hdir, zero_mul, zero_sub, neg_mul]
  change R 4 = (x : ℂ) / v + (1 - (x : ℂ) - t) at hR4
  change R 6 = (r : ℂ) * u * (1 - (t : ℂ) * v) / f at hR6
  change R 9 = -(t : ℂ) * (f * (x - v) + (r : ℂ) * ((u : ℂ) * v - (x : ℂ) * G)) / f + C at hR9
  change R 10 = -V * f / v + C at hR10
  change R 12 = W * (v - 1) * J / (f * L) + C at hR12
  change R 13 = -W * (x - v) * J / (f * L) + C at hR13
  change R 14 = V * ((1 - (t : ℂ)) * u) / L + (1 - (t : ℂ) * (1 + r)) at hR14
  change R 18 = W * (v - 1) * G / (v * L) + C at hR18
  change R 20 = V * f * G / (v * L) + C at hR20
  change R 22 = (t : ℂ) * V * (x - v) * G / (v * L) + C at hR22
  have h4im : (R 4).im = -x * v.im / Complex.normSq v := by
    rw [hR4, Complex.add_im, Complex.div_im]
    simp [Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re, Complex.one_im, neg_mul] <;> ring
  have h4 : g 4 = ρ * x / Complex.normSq v := by rw [hgR, h4im]; dsimp only [ρ]; ring
  have hR6' : R 6 = ((r * u : ℝ) : ℂ) - ((r * u * (x - 1) : ℝ) : ℂ) / f := by
    rw [hR6]
    field_simp [hf']
    dsimp only [f]
    push_cast
    ring
  have h6im : (R 6).im = -(r * t * u * (x - 1)) * v.im / Complex.normSq f := by
    rw [hR6', Complex.sub_im, Complex.div_im]
    have hfi : f.im = -t * v.im := by simp [f, Complex.mul_im, Complex.sub_im, neg_mul]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, zero_sub, hfi]
    ring
  have h6 : g 6 = ρ * r * u * (t * (x - 1)) / Complex.normSq f := by
    rw [hgR, h6im]
    dsimp only [ρ]
    ring
  have hVL : (V / L).im = (x - t - r * (u + t)) * v.im / Complex.normSq L := by
    rw [Complex.div_im]
    have hVi : V.im = v.im := by simp [V, Complex.sub_im]
    have hVr : V.re = v.re - 1 - r := by simp [V, Complex.sub_re]
    have hLi : L.im = -(u + t) * v.im := by
      simp only [L, G, Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
        Complex.ofReal_re, Complex.add_im, Complex.add_re]
      ring
    have hLr : L.re = u - ((u + t) * v.re - x) := by simp [L, G, Complex.sub_re, Complex.mul_re]
    rw [hVi, hVr, hLi, hLr]
    ring
  have h14im : (R 14).im = (1 - t) * u * ((x - t - r * (u + t)) * v.im / Complex.normSq L) := by
    have h : R 14 = (((1 - t) * u : ℝ) : ℂ) * (V / L) + ((1 - t * (1 + r) : ℝ) : ℂ) := by
      rw [hR14]
      push_cast
      ring
    rw [h, Complex.add_im, Complex.mul_im, hVL]
    simp
  have heq14 : Complex.normSq L * g 14 = ρ * u * (t - 1) * (x - t - r * (u + t)) := by
    rw [hgR, h14im]
    field_simp [(Complex.normSq_pos.mpr hL').ne']
    dsimp only [ρ]
    ring
  have h9c : R 9 + (x : ℂ) * R 6 = ((-r * t * x + r * u - t * x + 1 : ℝ) : ℂ) := by
    rw [hR9, hR6]
    field_simp [hf']
    dsimp only [f, G, C]
    push_cast
    ring
  have h10c : R 10 - ((r + 1 : ℝ) : ℂ) * R 4 = ((r * (x - 1) : ℝ) : ℂ) := by
    rw [hR10, hR4]
    field_simp [hv]
    dsimp only [V, f, C]
    push_cast
    ring
  have hAc : (t : ℂ) * (-R 4 + R 6 + R 10 - R 12 + R 18) - R 22 =
      ((-r * t ^ 2 + r * t * u + r * t + t - 1 : ℝ) : ℂ) := by
    rw [hR4, hR6, hR10, hR12, hR18, hR22]
    simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_one] using
      negativeDefect_defect_ratio_identity (x : ℂ) t r u v f G L V W J C
        hv hf' hL' rfl rfl rfl rfl rfl rfl rfl
  have h22c : -R 22 - (t : ℂ) * R 14 + (t : ℂ) * R 20 =
      ((r * t + t - 1 : ℝ) : ℂ) := by
    rw [hR22, hR14, hR20]
    field_simp [hv, hL']
    dsimp only [V, L, f, G, C]
    push_cast
    ring
  have hJc : (((1 - t) * (u + x) : ℝ) : ℂ) * R 20 -
      (((1 - t) * x * (1 + r) : ℝ) : ℂ) * R 4 - ((u * (x - t) : ℝ) : ℂ) * R 14 =
      (((x - 1) * (r * t * u - r * t * x + r * x + t * u - u) : ℝ) : ℂ) := by
    rw [hR20, hR4, hR14]
    field_simp [hv, hL']
    dsimp only [V, L, f, G, C]
    push_cast
    ring
  have hFc : ((t - x : ℝ) : ℂ) * (R 13 - R 14) + ((x * (1 - t) : ℝ) : ℂ) * R 6 -
      (((1 - x) * (-t - u) : ℝ) : ℂ) * R 14 =
      ((t * (r * t * x - r * x + x ^ 2 - 2 * x + 1) : ℝ) : ℂ) := by
    rw [hR13, hR14, hR6]
    simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat] using
      negativeDefect_residue_ratio_identity (x : ℂ) t r u v f G L V W J C
        hf' hL' rfl rfl rfl rfl rfl rfl rfl
  have h9 : g 9 = -x * g 6 := by
    have h := congrArg Complex.im h9c
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero] at h
    simp only [hgR]
    linear_combination (-P.im) * h
  have h10 : g 10 = (1 + r) * g 4 := by
    have h := congrArg Complex.im h10c
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero] at h
    simp only [hgR]
    linear_combination (-P.im) * h
  have hAeq : t * (fourNegativeDefectMinorDefect g - g 13) = g 22 := by
    have h := congrArg Complex.im hAc
    simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, zero_mul, add_zero] at h
    simp only [fourNegativeDefectMinorDefect, hgR]
    linear_combination (-P.im) * h
  have h22 : (-t) * (g 14 - g 20) = g 22 := by
    have h := congrArg Complex.im h22c
    simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, zero_mul, add_zero] at h
    simp only [hgR]
    linear_combination (-P.im) * h
  have hJ : (1 - t) * (u + x) * g 20 = (1 - t) * x * (1 + r) * g 4 + u * (x - t) * g 14 := by
    have h := congrArg Complex.im hJc
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero] at h
    simp only [hgR]
    linear_combination (-P.im) * h
  have hF : (t - x) * (g 13 - g 14) = -x * (1 - t) * g 6 + (1 - x) * (-t - u) * g 14 := by
    have h := congrArg Complex.im hFc
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, zero_mul, add_zero] at h
    simp only [hgR]
    linear_combination (-P.im) * h
  have ht' : t < 0 := by
    by_contra! hn
    have htp := lt_of_le_of_ne hn ht.symm
    have hh := mul_neg_of_pos_of_neg htp (sub_neg.mpr (hA.trans_le (hg 13)))
    rw [hAeq] at hh
    exact (not_lt_of_ge (hg 22)) hh
  have h9' : 0 < g 9 := by linarith only [h21, hA, hg 21]
  have hprod : 0 < (-x) * g 6 := h9 ▸ h9'
  have hx' : x < 0 := neg_pos.mp (pos_of_mul_pos_left hprod (hg 6))
  have hb : 0 < g 6 := (mul_pos_iff_of_pos_left (neg_pos.mpr hx')).mp hprod
  have hρ₀ : ρ ≠ 0 := by
    intro h
    rw [h6, h, zero_mul, zero_mul, zero_mul, zero_div] at hb
    exact (lt_irrefl _) hb
  have hvN := Complex.normSq_pos.mpr hv
  have hfN := Complex.normSq_pos.mpr hf'
  have hLN := Complex.normSq_pos.mpr hL'
  have hρ : ρ < 0 := by
    by_contra! hn
    have hp := lt_of_le_of_ne hn hρ₀.symm
    have hh := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp hx') hvN
    exact (not_lt_of_ge (hg 4)) (h4.symm ▸ hh)
  have ha : 0 < g 4 := h4.symm ▸ div_pos (mul_pos_of_neg_of_neg hρ hx') hvN
  have hr : -1 ≤ r := by
    have h := (mul_nonneg_iff_of_pos_right ha).mp (h10 ▸ hg 10)
    linarith only [h]
  have hru : r * u < 0 := by
    have hp := (div_pos_iff_of_pos_right hfN).mp (h6 ▸ hb)
    have hx₁ : x - 1 < 0 := by linarith only [hx']
    have hh := (mul_pos_iff_of_pos_right (mul_pos_of_neg_of_neg ht' hx₁)).mp hp
    by_contra! hn
    rw [mul_assoc] at hh
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hρ.le hn)) hh
  have hAe : fourNegativeDefectMinorDefect g = g 13 - g 14 + g 20 := by
    have he : t * (fourNegativeDefectMinorDefect g - g 13) = t * (-(g 14 - g 20)) := by
      linear_combination hAeq - h22
    have hh := mul_left_cancel₀ ht he
    linarith only [hh]
  have hExceptional (hr' : r = -1) (hu' : u = -x) (hlt : -t < -x) : g 20 < 0 := by
    have hxt : x - t < 0 := by linarith only [hlt]
    have hxt' : (x : ℂ) - t ≠ 0 := by exact_mod_cast hxt.ne
    have hspecial : R 20 = ((-(x ^ 2) / (x - t) : ℝ) : ℂ) / v +
        (((2 * t * x - t - x ^ 2 + x) / (x - t) : ℝ) : ℂ) := by
      rw [hR20]
      dsimp only [V, f, G, L, C]
      rw [show (r : ℂ) = -1 by exact_mod_cast hr', show (u : ℂ) = -(x : ℂ) by exact_mod_cast hu']
      have hden : -(x : ℂ) - ((-(x : ℂ) + t) * v - x) = ((x : ℂ) - t) * v := by ring
      rw [hden]
      push_cast
      rw [div_div]
      field_simp [hv, hxt'] <;> ring
    have him : (R 20).im = x ^ 2 * v.im / ((x - t) * Complex.normSq v) := by
      rw [hspecial, Complex.add_im, Complex.div_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, zero_sub, add_zero]
      field_simp [hxt.ne, hvN.ne'] <;> ring
    have hj : g 20 = (-ρ) * x ^ 2 / ((x - t) * Complex.normSq v) := by
      rw [hgR, him]
      dsimp only [ρ]
      ring
    rw [hj]
    exact div_neg_of_pos_of_neg (mul_pos (neg_pos.mpr hρ) (sq_pos_of_ne_zero hx'.ne))
      (mul_neg_of_neg_of_pos hxt hvN)
  apply fourNegativeDefect_capacity_of_real_chart (X := -x) (T := -t) (r := r) (u := u) (q := -ρ)
    (neg_pos.mpr hx') (neg_pos.mpr ht') hr hru ha hb (hg 14) (hg 13) (hg 20) hLN
    (neg_pos.mpr hρ) hA hAe _ h22 _ _ _ hExceptional
  · rw [← h9, ← h21]
    exact hg 21
  · linear_combination heq14
  · linear_combination hJ
  · linear_combination hF

end MOC

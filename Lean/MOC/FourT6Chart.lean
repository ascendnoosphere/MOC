import MOC.FourT7Source
import MOC.FourT6Minor

/-! The four real parameters forced by the T6 contact set. -/

namespace MOC

private theorem t6_chord_ratios_real {κ x y : ℂ} (hκ : κ ≠ 0)
    (hx : (κ * x).re = 0) (hy : (κ * y).re = 0) : (x / y).im = 0 := by
  rw [← mul_div_mul_left x y hκ]
  simp [Complex.div_im, hx, hy]

private theorem t6_chart_chords (z w v r c : ℂ) :
    let F := fourT7ProjectiveProduct z ![w, v, r, c]
    F 0 - F 1 = v * (r - c) * (z - 1) ∧ F 2 - F 4 = z * (r - c) * (v - 1) ∧
    F 0 - F 2 = (z - c) * (r - v) ∧ F 0 - F 6 = (z - c) * (r - 1) * (v - w) ∧
    F 2 - F 8 = r * (z - c) * (v - w) ∧ F 6 - F 8 = (z - c) * (r - w) := by
  let F := fourT7ProjectiveProduct z ![w, v, r, c]
  have h0 : F 0 = -v * (1 - r) * (z - c) := rfl
  have h1 : F 1 = -v * (1 - c) * (z - r) := rfl
  have h2 : F 2 = -r * (1 - v) * (z - c) := rfl
  have h4 : F 4 = -c * (1 - v) * (z - r) := rfl
  have h6 : F 6 = -w * (1 - r) * (z - c) := rfl
  have h8 : F 8 = -r * (1 - w) * (z - c) := rfl
  change F 0 - F 1 = _ ∧ F 2 - F 4 = _ ∧ F 0 - F 2 = _ ∧
    F 0 - F 6 = _ ∧ F 2 - F 8 = _ ∧ F 6 - F 8 = _
  rw [h0, h1, h2, h4, h6, h8]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 1300000 in
/-- Every distinct T6 source has the normalized real-parameter projective
chart. Its solved denominators are nonzero even when `v` is real. -/
theorem fourT6_chart_real_parameters (z w v r c κ : ℂ) (H : ℝ) (hκ : κ ≠ 0)
    (hz : z ≠ 0) (hz₁ : z ≠ 1)
    (hinj : Function.Injective (![w, v, r, c] : Fin 4 → ℂ))
    (hsep : ∀ j, (![w, v, r, c] : Fin 4 → ℂ) j ≠ 0 ∧
      (![w, v, r, c] : Fin 4 → ℂ) j ≠ 1 ∧ (![w, v, r, c] : Fin 4 → ℂ) j ≠ z)
    (hc : ∀ i ∈ fourT6ContactIndices,
      (κ * fourT7ProjectiveProduct z ![w, v, r, c] i).re = H) :
    r.im = 0 ∧ (κ * ((z - c) * (v - r))).re = 0 ∧
    ∃ h t s : ℂ, h.im = 0 ∧ t.im = 0 ∧ s.im = 0 ∧ h ≠ 0 ∧ h ≠ 1 ∧
      t ≠ 0 ∧ t ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 ∧ w = r + s * (v - r) ∧
      1 + (h - 1) * v ≠ 0 ∧ v - r - t * (v - z) ≠ 0 ∧
      z = h * v / (1 + (h - 1) * v) ∧
      c = (z * (v - r) - t * r * (v - z)) / (v - r - t * (v - z)) := by
  let F := fourT7ProjectiveProduct z ![w, v, r, c]
  have hor (i j : Fin 24) (hi : i ∈ fourT6ContactIndices)
      (hj : j ∈ fourT6ContactIndices) : (κ * (F i - F j)).re = 0 := by
    simp only [F, mul_sub, Complex.sub_re, hc i hi, hc j hj, sub_self]
  obtain ⟨h01, h24, h02, h06, h28, h68⟩ := t6_chart_chords z w v r c
  change F 0 - F 1 = _ at h01
  change F 2 - F 4 = _ at h24
  change F 0 - F 2 = _ at h02
  change F 0 - F 6 = _ at h06
  change F 2 - F 8 = _ at h28
  change F 6 - F 8 = _ at h68
  have hv : v ≠ 0 := (hsep 1).1
  have hv₁ : v ≠ 1 := (hsep 1).2.1
  have hvz : v ≠ z := (hsep 1).2.2
  have hr : r ≠ 0 := (hsep 2).1
  have hzr : z ≠ r := (hsep 2).2.2.symm
  have hzc : z ≠ c := (hsep 3).2.2.symm
  have hrc : r ≠ c := hinj.ne (by decide : (2 : Fin 4) ≠ 3)
  have hvc : v ≠ c := hinj.ne (by decide : (1 : Fin 4) ≠ 3)
  have hvr : v ≠ r := hinj.ne (by decide : (1 : Fin 4) ≠ 2)
  have hvw : v ≠ w := hinj.ne (by decide : (1 : Fin 4) ≠ 0)
  have hwr : w ≠ r := hinj.ne (by decide : (0 : Fin 4) ≠ 2)
  have hri : r.im = 0 := by
    have heq : (F 0 - F 6) / (F 2 - F 8) = 1 - r⁻¹ := by
      rw [h06, h28]
      field_simp [hr, sub_ne_zero.mpr hzc, sub_ne_zero.mpr hvw] <;> ring
    have he := t6_chord_ratios_real hκ (hor 0 6 (by decide) (by decide)) (hor 2 8 (by decide) (by decide))
    rw [heq, Complex.sub_im, Complex.one_im, Complex.inv_im] at he
    simpa only [zero_sub, neg_eq_zero, neg_div, div_eq_zero_iff,
      (Complex.normSq_pos.mpr hr).ne', or_false] using he
  have hdir : (κ * ((z - c) * (v - r))).re = 0 := by
    have he := hor 0 2 (by decide) (by decide)
    rw [h02, show r - v = -(v - r) by ring, mul_neg, mul_neg, Complex.neg_re, neg_eq_zero] at he
    exact he
  let s := (w - r) / (v - r)
  let h := z * (v - 1) / (v * (z - 1))
  let t := (c - z) * (v - r) / ((c - r) * (v - z))
  have hsi : s.im = 0 := by
    have heq : s = (F 6 - F 8) / (F 0 - F 2) := by
      rw [h68, h02]
      dsimp only [s]
      field_simp [sub_ne_zero.mpr hzc, sub_ne_zero.mpr hvr, sub_ne_zero.mpr hvr.symm] <;> ring
    rw [heq]
    exact t6_chord_ratios_real hκ (hor 6 8 (by decide) (by decide)) (hor 0 2 (by decide) (by decide))
  have hh' : h - 1 = (v - z) / (v * (z - 1)) := by
    dsimp only [h]
    field_simp [hv, sub_ne_zero.mpr hz₁] <;> ring
  have hhi : h.im = 0 := by
    have heq : h = (F 2 - F 4) / (F 0 - F 1) := by
      rw [h24, h01]
      dsimp only [h]
      field_simp [hv, sub_ne_zero.mpr hrc, sub_ne_zero.mpr hz₁] <;> ring
    rw [heq]
    exact t6_chord_ratios_real hκ (hor 2 4 (by decide) (by decide)) (hor 0 1 (by decide) (by decide))
  have hti : t.im = 0 := by
    have heq : t = (-((F 0 - F 2) / (F 0 - F 1))) / (h - 1) := by
      rw [h02, h01, hh']
      dsimp only [t]
      rw [div_div_eq_mul_div]
      field_simp [hv, sub_ne_zero.mpr hrc, sub_ne_zero.mpr hrc.symm,
        sub_ne_zero.mpr hvz, sub_ne_zero.mpr hz₁] <;> ring
    rw [heq]
    have hh := t6_chord_ratios_real hκ (hor 0 2 (by decide) (by decide)) (hor 0 1 (by decide) (by decide))
    simp [Complex.div_im, Complex.sub_im, hhi, hh]
  have hh₀ : h ≠ 0 := div_ne_zero (mul_ne_zero hz (sub_ne_zero.mpr hv₁)) (mul_ne_zero hv (sub_ne_zero.mpr hz₁))
  have hh₁ : h ≠ 1 := sub_ne_zero.mp (hh'.symm ▸ div_ne_zero (sub_ne_zero.mpr hvz)
    (mul_ne_zero hv (sub_ne_zero.mpr hz₁)))
  have ht₀ : t ≠ 0 := div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hzc.symm) (sub_ne_zero.mpr hvr))
    (mul_ne_zero (sub_ne_zero.mpr hrc.symm) (sub_ne_zero.mpr hvz))
  have ht₁ : t ≠ 1 := by
    intro he
    have hp := (div_eq_iff (mul_ne_zero (sub_ne_zero.mpr hrc.symm) (sub_ne_zero.mpr hvz))).mp he
    have hzero : (z - r) * (c - v) = 0 := by linear_combination hp
    exact mul_ne_zero (sub_ne_zero.mpr hzr) (sub_ne_zero.mpr hvc.symm) hzero
  have hs₀ : s ≠ 0 := div_ne_zero (sub_ne_zero.mpr hwr) (sub_ne_zero.mpr hvr)
  have hs₁ : s ≠ 1 := by
    intro he
    have hp : w - r = 1 * (v - r) := (div_eq_iff (sub_ne_zero.mpr hvr)).mp he
    exact hvw (by linear_combination -hp)
  have hw : w = r + s * (v - r) := by
    dsimp only [s]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hvr)]
    ring
  have hzden : 1 + (h - 1) * v = (v - 1) / (z - 1) := by
    rw [hh']
    field_simp [hv, sub_ne_zero.mpr hz₁] <;> ring
  have hcden : v - r - t * (v - z) = (v - r) * (z - r) / (c - r) := by
    dsimp only [t]
    field_simp [sub_ne_zero.mpr hrc.symm, sub_ne_zero.mpr hvz] <;> ring
  have hzden₀ : 1 + (h - 1) * v ≠ 0 := by rw [hzden]; exact div_ne_zero (sub_ne_zero.mpr hv₁) (sub_ne_zero.mpr hz₁)
  have hcden₀ : v - r - t * (v - z) ≠ 0 := by
    rw [hcden]
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hvr) (sub_ne_zero.mpr hzr)) (sub_ne_zero.mpr hrc.symm)
  refine ⟨hri, hdir, h, t, s, hhi, hti, hsi, hh₀, hh₁, ht₀, ht₁, hs₀, hs₁, hw, hzden₀, hcden₀, ?_, ?_⟩
  · apply (eq_div_iff hzden₀).mpr
    rw [hzden]
    dsimp only [h]
    field_simp [hv, sub_ne_zero.mpr hz₁] <;> ring
  · apply (eq_div_iff hcden₀).mpr
    dsimp only [t]
    field_simp [sub_ne_zero.mpr hrc.symm, sub_ne_zero.mpr hvz] <;> ring

end MOC

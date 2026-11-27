import MOC.FourT7Source
import MOC.FourGeometricBudgetMinor

/-! The four real parameters forced by the geometric-budget pattern contact set. -/

namespace MOC

private theorem geometricBudget_chord_ratios_real {κ x y : ℂ} (hκ : κ ≠ 0)
    (hx : (κ * x).re = 0) (hy : (κ * y).re = 0) : (x / y).im = 0 := by
  rw [← mul_div_mul_left x y hκ]
  simp [Complex.div_im, hx, hy]

private theorem geometricBudget_chart_chords (z w v r c : ℂ) :
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
/-- Every distinct geometric-budget pattern source has the normalized real-parameter projective
chart. Its solved denominators are nonzero even when `v` is real. -/
theorem fourGeometricBudget_chart_real_parameters (z w v r c κ : ℂ) (H : ℝ) (hκ : κ ≠ 0)
    (hz : z ≠ 0) (hz₁ : z ≠ 1)
    (hinj : Function.Injective (![w, v, r, c] : Fin 4 → ℂ))
    (hsep : ∀ j, (![w, v, r, c] : Fin 4 → ℂ) j ≠ 0 ∧
      (![w, v, r, c] : Fin 4 → ℂ) j ≠ 1 ∧ (![w, v, r, c] : Fin 4 → ℂ) j ≠ z)
    (hc : ∀ i ∈ fourGeometricBudgetContactIndices,
      (κ * fourT7ProjectiveProduct z ![w, v, r, c] i).re = H) :
    r.im = 0 ∧ (κ * ((z - c) * (v - r))).re = 0 ∧
    ∃ h t s : ℂ, h.im = 0 ∧ t.im = 0 ∧ s.im = 0 ∧ h ≠ 0 ∧ h ≠ 1 ∧
      t ≠ 0 ∧ t ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 ∧ w = r + s * (v - r) ∧
      1 + (h - 1) * v ≠ 0 ∧ v - r - t * (v - z) ≠ 0 ∧
      z = h * v / (1 + (h - 1) * v) ∧
      c = (z * (v - r) - t * r * (v - z)) / (v - r - t * (v - z)) := by
  let F := fourT7ProjectiveProduct z ![w, v, r, c]
  have hor (i j : Fin 24) (hi : i ∈ fourGeometricBudgetContactIndices)
      (hj : j ∈ fourGeometricBudgetContactIndices) : (κ * (F i - F j)).re = 0 := by
    simp only [F, mul_sub, Complex.sub_re, hc i hi, hc j hj, sub_self]
  obtain ⟨h01, h24, h02, h06, h28, h68⟩ := geometricBudget_chart_chords z w v r c
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
    have he := geometricBudget_chord_ratios_real hκ (hor 0 6 (by decide) (by decide)) (hor 2 8 (by decide) (by decide))
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
    exact geometricBudget_chord_ratios_real hκ (hor 6 8 (by decide) (by decide)) (hor 0 2 (by decide) (by decide))
  have hh' : h - 1 = (v - z) / (v * (z - 1)) := by
    dsimp only [h]
    field_simp [hv, sub_ne_zero.mpr hz₁] <;> ring
  have hhi : h.im = 0 := by
    have heq : h = (F 2 - F 4) / (F 0 - F 1) := by
      rw [h24, h01]
      dsimp only [h]
      field_simp [hv, sub_ne_zero.mpr hrc, sub_ne_zero.mpr hz₁] <;> ring
    rw [heq]
    exact geometricBudget_chord_ratios_real hκ (hor 2 4 (by decide) (by decide)) (hor 0 1 (by decide) (by decide))
  have hti : t.im = 0 := by
    have heq : t = (-((F 0 - F 2) / (F 0 - F 1))) / (h - 1) := by
      rw [h02, h01, hh']
      dsimp only [t]
      rw [div_div_eq_mul_div]
      field_simp [hv, sub_ne_zero.mpr hrc, sub_ne_zero.mpr hrc.symm,
        sub_ne_zero.mpr hvz, sub_ne_zero.mpr hz₁] <;> ring
    rw [heq]
    have hh := geometricBudget_chord_ratios_real hκ (hor 0 2 (by decide) (by decide)) (hor 0 1 (by decide) (by decide))
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

/-! Exact factored quotients for the geometric-budget pattern projective support certificate. -/

namespace MOC

set_option maxHeartbeats 1800000 in
/-- The eight geometric-budget pattern pivot-related quotients in the real chart. The expression
`Q` is linear in `v` and its slope is allowed to vanish. -/
theorem fourGeometricBudget_exact_pole_ratios (h r s p z w v c : ℂ)
    (hv : v ≠ 0) (hv₁ : v ≠ 1) (hh : h ≠ 1) (hvr : v ≠ r) (hvz : v ≠ z)
    (hrz : r ≠ z) (hzc : z ≠ c) (hG : 1 + (h - 1) * v ≠ 0)
    (hP : p * (v - r) - (v - z) ≠ 0)
    (hz : z = h * v / (1 + (h - 1) * v)) (hw : w = r + s * (v - r))
    (hc : c = (p * z * (v - r) - r * (v - z)) / (p * (v - r) - (v - z))) :
    let F := fourT7ProjectiveProduct z ![w, v, r, c]
    let R (i : Fin 24) := (F i - F 0) / ((z - c) * (v - r))
    let Q := (h * r - h - r) * v + r
    let J := v * (v - 1) / Q
    Q ≠ 0 ∧ R 3 = ((h * r - h - p * r) * v + p * r) / Q ∧
    R 7 = (1 - s) * (1 - r) - p * s / (h - 1) + p * r * (s - 1) / ((h - 1) * v) ∧
    R 10 = 1 + r * (s - 1) - p * h * s / (h - 1) +
      p * h * (r - 1) * (s - 1) / ((h - 1) * (v - 1)) ∧
    R 12 = 1 + s * (v - 1) ∧ R 9 = R 7 + s * R 3 + p * s / (h - 1) ∧
    R 18 = R 7 - (p - 1) * w ∧
    R 19 = (1 - s) * R 3 - s * (p - 1) * (v + J) + p * r * (s - 1) ∧
    R 22 = (1 - s) * R 3 - s * (p - 1) * (v + h * J) + p * (r * s - r + s) := by
  intro F R Q J
  let G := 1 + (h - 1) * v
  let E := v - r
  let B := v - z
  let A := z - c
  let P := p * E - B
  let D := A * E
  let M := B / A
  have hE : E ≠ 0 := sub_ne_zero.mpr hvr
  have hB : B ≠ 0 := sub_ne_zero.mpr hvz
  have hA : A ≠ 0 := sub_ne_zero.mpr hzc
  have hD : D ≠ 0 := mul_ne_zero hA hE
  have hG' : G ≠ 0 := hG
  have hP' : P ≠ 0 := hP
  have hp : c * P = p * z * E - r * B := (eq_div_iff hP').mp hc
  have hAeq : A * P = (r - z) * B := by dsimp only [A, P] at hp ⊢; linear_combination -hp
  have hcreq : (c - r) * P = p * (z - r) * E := by
    dsimp only [P] at hp ⊢
    linear_combination hp
  have hcr : (c - r) * B = -p * D := by
    apply mul_right_cancel₀ hP'
    dsimp only [D]
    linear_combination B * hcreq + p * E * hAeq
  have hvceq : (v - c) * (z - r) = -(p - 1) * D := by
    dsimp only [A, P, D, E, B] at hAeq ⊢
    linear_combination hAeq
  have hz' : z = h * v / G := hz
  have hB' : B = (h - 1) * v * (v - 1) / G := by
    dsimp only [B]
    rw [hz']
    field_simp [hG'] <;> dsimp only [G] <;> ring
  have hz₁ : 1 - z = (1 - v) / G := by
    rw [hz']
    field_simp [hG'] <;> dsimp only [G] <;> ring
  have hrzQ : r - z = Q / G := by
    rw [hz']
    field_simp [hG'] <;> dsimp only [Q, G] <;> ring
  have hQ : Q ≠ 0 := by
    intro he
    exact sub_ne_zero.mpr hrz (by rw [hrzQ, he, zero_div])
  have hh' : h - 1 ≠ 0 := sub_ne_zero.mpr hh
  have hv₁' : v - 1 ≠ 0 := sub_ne_zero.mpr hv₁
  have hzB : z / B = h / ((h - 1) * (v - 1)) := by
    apply (div_eq_div_iff hB (mul_ne_zero hh' hv₁')).mpr
    rw [hz', hB']
    field_simp [hG'] <;> ring
  have hzB₁ : (1 - z) / B = -1 / ((h - 1) * v) := by
    apply (div_eq_div_iff hB (mul_ne_zero hh' hv)).mpr
    rw [hz₁, hB']
    field_simp [hG'] <;> ring
  have hM : M = (p * E * G - (h - 1) * v * (v - 1)) / Q := by
    have he : M = P / (r - z) := (div_eq_div_iff hA (sub_ne_zero.mpr hrz)).mpr (by
      linear_combination -hAeq)
    rw [he, hrzQ, div_div_eq_mul_div]
    dsimp only [P]
    rw [hB']
    field_simp [hG', hQ] <;> ring
  have hF₀ : F 0 = -v * (1 - r) * A := rfl
  have hF₃ : F 3 = -r * (1 - c) * (z - v) := rfl
  have hF₇ : F 7 = -w * (1 - c) * (z - r) := rfl
  have hF₉ : F 9 = -r * (1 - c) * (z - w) := rfl
  have hF₁₀ : F 10 = -c * (1 - w) * (z - r) := rfl
  have hF₁₂ : F 12 = -w * (1 - v) * A := rfl
  have hF₁₈ : F 18 = -w * (1 - v) * (z - r) := rfl
  have hF₁₉ : F 19 = -w * (1 - r) * (z - v) := rfl
  have hF₂₂ : F 22 = -r * (1 - w) * (z - v) := rfl
  have hFR₃ : F 3 = r * (1 - r) * B + r * p * D := by
    rw [hF₃]
    dsimp only [B] at hcr ⊢
    linear_combination -r * hcr
  have hR₃ : R 3 = ((h * r - h - p * r) * v + p * r) / Q := by
    have he : R 3 = r * p + (1 - r) * (r * M + v) / E := by
      change (F 3 - F 0) / D = _
      apply (div_eq_iff hD).mpr
      rw [hFR₃, hF₀]
      dsimp only [D, M]
      field_simp [hE, hA] <;> ring
    rw [he, hM]
    field_simp [hE, hQ] <;> dsimp only [E, G, Q] <;> ring
  have hR₇' : R 7 = (v - w) * (1 - r) / E + w * p * (1 - z) / B := by
    change (F 7 - F 0) / D = _
    apply (div_eq_iff hD).mpr
    rw [hF₇, hF₀]
    dsimp only [D]
    field_simp [hE, hB]
    dsimp only [D, E, A, B] at hcr ⊢
    linear_combination w * (z - 1) * (v - r) * hcr
  have hR₁₀' : R 10 = (v * (1 - r) - r * (1 - w)) / E + p * z * (1 - w) / B := by
    change (F 10 - F 0) / D = _
    apply (div_eq_iff hD).mpr
    rw [hF₁₀, hF₀]
    dsimp only [D]
    field_simp [hE, hB]
    dsimp only [D, E, A, B] at hcr ⊢
    linear_combination -z * (1 - w) * (v - r) * hcr
  have hR₇ : R 7 = (1 - s) * (1 - r) - p * s / (h - 1) + p * r * (s - 1) / ((h - 1) * v) := by
    rw [hR₇', show w * p * (1 - z) / B = w * p * ((1 - z) / B) by ring, hzB₁, hw]
    field_simp [hE, hv, hh']
    dsimp only [E]
    ring
  have hR₁₀ : R 10 = 1 + r * (s - 1) - p * h * s / (h - 1) +
      p * h * (r - 1) * (s - 1) / ((h - 1) * (v - 1)) := by
    rw [hR₁₀', show p * z * (1 - w) / B = p * (1 - w) * (z / B) by ring, hzB, hw]
    field_simp [hE, hv₁', hh']
    dsimp only [E]
    ring
  have hR₁₂ : R 12 = 1 + s * (v - 1) := by
    change (F 12 - F 0) / D = _
    apply (div_eq_iff hD).mpr
    rw [hF₁₂, hF₀, hw]
    dsimp only [D, E]
    ring
  have hRdiff (i j : Fin 24) : R i - R j = (F i - F j) / D := by dsimp only [R]; rw [sub_div]; ring
  have hR₉ : R 9 = R 7 + s * R 3 + p * s / (h - 1) := by
    have he : R 9 - R 7 = s * z * ((1 - r) * M + p * E) / B := by
      rw [hRdiff]
      apply (div_eq_div_iff hD hB).mpr
      rw [hF₉, hF₇, hw]
      dsimp only [M, D]
      field_simp [hA]
      dsimp only [E, B, A] at hcr ⊢
      linear_combination -s * z * (v - r) * (z - c) * hcr
    have he' : s * z * ((1 - r) * M + p * E) / B = s * R 3 + p * s / (h - 1) := by
      rw [show s * z * ((1 - r) * M + p * E) / B = s * ((1 - r) * M + p * E) * (z / B) by ring,
        hzB, hM, hR₃]
      field_simp [hQ, hh', hv₁']
      dsimp only [E, G, Q]
      ring
    rw [he'] at he
    linear_combination he
  have hR₁₈ : R 18 = R 7 - (p - 1) * w := by
    have he : R 18 - R 7 = -(p - 1) * w := by
      rw [hRdiff]
      apply (div_eq_iff hD).mpr
      rw [hF₁₈, hF₇]
      linear_combination w * hvceq
    linear_combination he
  have hR₁₉' : R 19 - R 3 = s * (1 - r) * M - r * p := by
    rw [hRdiff]
    apply (div_eq_iff hD).mpr
    rw [hF₁₉, hFR₃, hw]
    dsimp only [D, M]
    field_simp [hA] <;> dsimp only [B] <;> ring
  have hR₂₂' : R 22 - R 3 = -r * s * M - r * p := by
    rw [hRdiff]
    apply (div_eq_iff hD).mpr
    rw [hF₂₂, hFR₃, hw]
    dsimp only [D, M]
    field_simp [hA] <;> dsimp only [B] <;> ring
  refine ⟨hQ, hR₃, hR₇, hR₁₀, hR₁₂, hR₉, hR₁₈, ?_, ?_⟩
  · have he : s * (1 - r) * M - r * p = -s * R 3 - s * (p - 1) * (v + J) + p * r * (s - 1) := by
      rw [hM, hR₃]
      dsimp only [J]
      field_simp [hQ]
      dsimp only [E, G, Q]
      ring
    rw [he] at hR₁₉'
    linear_combination hR₁₉'
  · have he : -r * s * M - r * p = -s * R 3 - s * (p - 1) * (v + h * J) + p * (r * s - r + s) := by
      rw [hM, hR₃]
      dsimp only [J]
      field_simp [hQ]
      dsimp only [E, G, Q]
      ring
    rw [he] at hR₂₂'
    linear_combination hR₂₂'

end MOC

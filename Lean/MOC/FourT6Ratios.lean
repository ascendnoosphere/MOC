import MOC.FourT6Chart

/-! Exact factored quotients for the T6 projective support certificate. -/

namespace MOC

set_option maxHeartbeats 1800000 in
/-- The eight T6 pivot-related quotients in the real chart. The expression
`Q` is linear in `v` and its slope is allowed to vanish. -/
theorem fourT6_exact_pole_ratios (h r s p z w v c : ℂ)
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

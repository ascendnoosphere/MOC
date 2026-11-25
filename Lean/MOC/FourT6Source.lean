import MOC.FourT6Ratios
import MOC.FourT6Geometry

/-! The real spectral gap identities for the T6 chart. -/

namespace MOC

set_option maxHeartbeats 1800000 in
/-- The eight quotients determine the real T6 gaps, including `v.im = 0`. -/
theorem fourT6_projective_gap_identities (h r s p : ℝ) (z w v c κ : ℂ)
    (hv : v ≠ 0) (hv₁ : v ≠ 1) (hh : h ≠ 1) (hvr : v ≠ (r : ℂ)) (hvz : v ≠ z)
    (hrz : (r : ℂ) ≠ z) (hzc : z ≠ c) (hG : 1 + ((h : ℂ) - 1) * v ≠ 0)
    (hP : (p : ℂ) * (v - r) - (v - z) ≠ 0)
    (hz : z = (h : ℂ) * v / (1 + ((h : ℂ) - 1) * v)) (hw : w = (r : ℂ) + (s : ℂ) * (v - r))
    (hc : c = ((p : ℂ) * z * (v - r) - (r : ℂ) * (v - z)) / ((p : ℂ) * (v - r) - (v - z)))
    (hdir : (κ * ((z - c) * (v - r))).re = 0) :
    let F := fourT7ProjectiveProduct z ![w, v, r, c]
    let g (i : Fin 24) := (κ * (F i - F 0)).re
    let a := h * r - h - r
    let N := Complex.normSq v
    let O := Complex.normSq (v - 1)
    let D := Complex.normSq ((a : ℂ) * v + r)
    let ρ := (κ * ((z - c) * (v - r))).im * v.im
    let K := h * r * (r - 1) / D
    let J := (a * N + r * (2 * v.re - 1)) / D
    let L := r / ((h - 1) * N)
    let M := h * (r - 1) / ((h - 1) * O)
    let E := ρ * s * (p - 1)
    0 < D ∧ g 3 = ρ * K * (p - 1) ∧ g 7 = ρ * L * p * (s - 1) ∧
    g 10 = ρ * M * p * (s - 1) ∧ g 12 = -ρ * s ∧ g 9 = g 7 + s * g 3 ∧
    g 18 = g 7 + E ∧ g 19 = g 3 + E * (1 + J - K) ∧ g 22 = g 3 + E * (1 + h * J - K) := by
  intro F g a N O D ρ K J L M E
  let Z := (z - c) * (v - r)
  let R (i : Fin 24) := (F i - F 0) / Z
  let μ := (κ * Z).im
  let Q := (a : ℂ) * v + r
  let J₀ := v * (v - 1) / Q
  have hZ : Z ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hzc) (sub_ne_zero.mpr hvr)
  have hgR (i : Fin 24) : g i = -μ * (R i).im := by
    have he : κ * (F i - F 0) = (κ * Z) * R i := by dsimp only [R]; field_simp [hZ] <;> ring
    change (κ * (F i - F 0)).re = _
    rw [he, Complex.mul_re, show (κ * Z).re = 0 from hdir, zero_mul, zero_sub, neg_mul]
  have hh' : (h : ℂ) ≠ 1 := by exact_mod_cast hh
  obtain ⟨hQ, h3, h7, h10, h12, h9, h18, h19, h22⟩ :=
    fourT6_exact_pole_ratios h r s p z w v c hv hv₁ hh' hvr hvz hrz hzc hG hP hz hw hc
  have hQ' : Q ≠ 0 := by
    change ((a : ℂ) * v + r) ≠ 0
    dsimp only [a]
    push_cast
    exact hQ
  have hD : 0 < D := Complex.normSq_pos.mpr hQ'
  have hQc : (h : ℂ) * r - h - r = (a : ℂ) := by dsimp only [a]; push_cast; ring
  simp only [hQc] at h3 h19 h22
  change R 3 = (((h : ℂ) * r - h - (p : ℂ) * r) * v + (p : ℂ) * r) / Q at h3
  change R 7 = (1 - (s : ℂ)) * (1 - (r : ℂ)) - (p : ℂ) * s / ((h : ℂ) - 1) +
    (p : ℂ) * r * ((s : ℂ) - 1) / (((h : ℂ) - 1) * v) at h7
  change R 10 = 1 + (r : ℂ) * ((s : ℂ) - 1) - (p : ℂ) * h * s / ((h : ℂ) - 1) +
    (p : ℂ) * h * ((r : ℂ) - 1) * ((s : ℂ) - 1) / (((h : ℂ) - 1) * (v - 1)) at h10
  change R 12 = 1 + (s : ℂ) * (v - 1) at h12
  change R 9 = R 7 + (s : ℂ) * R 3 + (p : ℂ) * s / ((h : ℂ) - 1) at h9
  change R 18 = R 7 - ((p : ℂ) - 1) * w at h18
  change R 19 = (1 - (s : ℂ)) * R 3 - (s : ℂ) * ((p : ℂ) - 1) * (v + J₀) +
    (p : ℂ) * r * ((s : ℂ) - 1) at h19
  change R 22 = (1 - (s : ℂ)) * R 3 - (s : ℂ) * ((p : ℂ) - 1) * (v + (h : ℂ) * J₀) +
    (p : ℂ) * ((r : ℂ) * s - r + s) at h22
  have h3im : (R 3).im = -K * (p - 1) * v.im := by
    rw [h3, Complex.div_im]
    dsimp only [Q, K]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im, Complex.sub_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, zero_add,
      add_zero, sub_zero, sub_self]
    change _ / D - _ / D = _
    dsimp only [a]
    ring
  have hJim : J₀.im = J * v.im := by
    dsimp only [J₀]
    rw [Complex.div_im]
    dsimp only [Q, J]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      zero_mul, mul_zero, zero_add, add_zero, sub_zero]
    change _ / D - _ / D = _
    dsimp only [N]
    rw [Complex.normSq_apply]
    ring
  have h7c : R 7 = (((1 - s) * (1 - r) - p * s / (h - 1) : ℝ) : ℂ) +
      ((p * r * (s - 1) / (h - 1) : ℝ) : ℂ) / v := by
    rw [h7]
    push_cast
    rw [div_div]
  have h10c : R 10 = ((1 + r * (s - 1) - p * h * s / (h - 1) : ℝ) : ℂ) +
      ((p * h * (r - 1) * (s - 1) / (h - 1) : ℝ) : ℂ) / (v - 1) := by
    rw [h10]
    push_cast
    rw [div_div]
  have h7im : (R 7).im = -L * p * (s - 1) * v.im := by
    rw [h7c, Complex.add_im, Complex.div_im]
    simp only [Complex.ofReal_im, Complex.ofReal_re, zero_add, zero_mul, zero_div, zero_sub]
    dsimp only [L, N]
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  have h10im : (R 10).im = -M * p * (s - 1) * v.im := by
    rw [h10c, Complex.add_im, Complex.div_im]
    simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.sub_im, Complex.one_im, sub_zero,
      zero_add, zero_mul, zero_div, zero_sub]
    dsimp only [M, O]
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  have hρ : ρ = μ * v.im := rfl
  have h3r : g 3 = ρ * K * (p - 1) := by rw [hgR, h3im, hρ]; ring
  refine ⟨hD, h3r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgR, h7im, hρ]; ring
  · rw [hgR, h10im, hρ]; ring
  · rw [hgR, h12, hρ]
    simp [Complex.add_im, Complex.mul_im, Complex.sub_im, neg_mul]
  · rw [hgR 9, hgR 7, hgR 3, h9]
    have he : ((p : ℂ) * s / ((h : ℂ) - 1)).im = 0 := by
      rw [show (p : ℂ) * s / ((h : ℂ) - 1) = ((p * s / (h - 1) : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_im _
    simp only [Complex.add_im, he, add_zero, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    ring
  · have hiw : w.im = s * v.im := by rw [hw]; simp [Complex.add_im, Complex.mul_im, Complex.sub_im]
    rw [hgR 18, hgR 7, h18]
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.one_im,
      Complex.one_re, sub_self, zero_mul, mul_zero, add_zero, hiw]
    dsimp only [E]
    rw [hρ]
    ring
  · have he : g 19 = (1 - s) * g 3 + E * (1 + J) := by
      rw [hgR 19, hgR 3, h19]
      simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.one_re, Complex.one_im, sub_self, mul_zero, zero_mul, zero_add, add_zero, hJim]
      dsimp only [E]
      rw [hρ]
      ring
    dsimp only [E] at he ⊢
    linear_combination he - s * h3r
  · have he : g 22 = (1 - s) * g 3 + E * (1 + h * J) := by
      rw [hgR 22, hgR 3, h22]
      simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.one_re, Complex.one_im, sub_self, mul_zero, zero_mul, zero_add, add_zero, hJim]
      dsimp only [E]
      rw [hρ]
      ring
    dsimp only [E] at he ⊢
    linear_combination he - s * h3r

end MOC

import MOC.FourT5Ratios
import MOC.FourT5Signs

/-! Exact real parts of the original T5 pole ratios and their capacities. -/

namespace MOC

private theorem linear_fraction_im (v : ℂ) (a b c d : ℝ) :
    ((((a : ℂ) * v + b) / ((c : ℂ) * v + d))).im =
      (a * d - b * c) * v.im / Complex.normSq ((c : ℂ) * v + d) := by
  rw [Complex.div_im]
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero, sub_zero]
  ring

set_option maxHeartbeats 2000000 in
/-- All capacity relations for the original T5 matching products. The
affine residue for `D*A` avoids dividing by `t+u` or `D`. -/
theorem fourT5_projective_gap_identities (x t r u : ℝ) (z w v η : ℂ)
    (hv : v ≠ 0) (hu : u ≠ 0) (hzw : z ≠ w) (hf : (x : ℂ) - t * v ≠ 0)
    (hG : (x : ℂ) - ((t : ℂ) + u) * v ≠ 0) (hP : (x : ℂ) - ((t : ℂ) + u) * v - r ≠ 0)
    (hz : z = (r : ℂ) * v / ((x : ℂ) - ((t : ℂ) + u) * v))
    (hw : w = ((x : ℂ) - r - (t : ℂ) * v) / u) (hdir : (η * (v * (z - w))).re = 0) :
    let F := fourT5PoleProduct z x w v t
    let g (i : Fin 24) := (η * (F i - F 1)).re
    let ρ := -(η * (v * (z - w))).im * v.im
    let Ef := Complex.normSq ((x : ℂ) - t * v)
    let Ep := Complex.normSq ((x : ℂ) - ((t : ℂ) + u) * v - r)
    let τ := ρ / Ef
    let A := g 16 - g 0
    let L := x - r - t - u
    let H := -r * t + t * (x - 1) - u
    let W := t * (x - 1) - r - u
    let D := r * t + u * x
    let J := r + (t + u - 1) * x
    g 0 = -ρ * x / Complex.normSq v ∧ g 7 = -τ * t * x * (r + u) ∧
    g 10 = -τ * r * t * (x - 1) ∧ x * g 11 = (x - 1) * g 9 ∧
    g 12 = -(ρ / Ep) * r * u * L ∧ g 17 = A - τ * t * u * x * (x - 1) ∧
    H * g 13 = t * L * A + τ * t * u * x * (t - 1) * W ∧
    H * g 22 = (t - 1) * (x - r) * A + τ * r * t * x * (t - 1) * (x - r - u - 1) ∧
    D * A = τ * r * u * (x * t * (t - 1) * (x - 1)) - (ρ / Ep) * r * u * J * H := by
  intro F g ρ Ef Ep τ A L H W D J
  let Z := v * (z - w)
  let R (i : Fin 24) := (F i - F 1) / Z
  let f := (x : ℂ) - t * v
  let G := (x : ℂ) - ((t : ℂ) + u) * v
  let P := G - r
  let W₀ := f - r
  let V := W₀ - u
  let K := (u : ℂ) * x - W₀
  let C := (t : ℂ) * (1 - v)
  let A₀ := R 16 - R 0
  let μ := -(η * Z).im
  have hZ : Z ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hgR (i : Fin 24) : g i = μ * (R i).im := by
    have he : η * (F i - F 1) = (η * Z) * R i := by
      dsimp only [R]
      field_simp [hZ] <;> ring
    change (η * (F i - F 1)).re = _
    rw [he, Complex.mul_re, show (η * Z).re = 0 from hdir, zero_mul, zero_sub, neg_mul]
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  obtain ⟨h0, h7, h9, h10, h11, h12, h13, h16, h17, h22⟩ :=
    fourT5_exact_pole_ratios x t r u z w v hv hu' hzw hf hG hP hz hw
  change R 0 = (x : ℂ) / v - x at h0
  change R 7 = t - (t : ℂ) * v * (r + u) / f at h7
  change R 9 = t - (t : ℂ) * v * (r + (u : ℂ) * x) / f at h9
  change R 10 = (t : ℂ) - 1 + r - (r : ℂ) * ((x : ℂ) - 1) / f at h10
  change R 11 = -K * ((t : ℂ) * v - 1) / f + C at h11
  change R 12 = -((x : ℂ) - r - t - u) - (r : ℂ) * V / P at h12
  change R 13 = -(t : ℂ) * (x - v) * V * G / (f * P) + C at h13
  change R 16 = -W₀ * (x - v) * ((t : ℂ) * v - 1) * G / (v * f * P) + C at h16
  change R 17 = -K * ((t : ℂ) * v - 1) * G / (f * P) + C at h17
  change R 22 = W₀ * (x - v) * ((r : ℂ) - (t : ℂ) * G) / (f * P) + C at h22
  have hf' : f ≠ 0 := hf
  have hP' : P ≠ 0 := hP
  have hfEq : f = ((-t : ℝ) : ℂ) * v + x := by dsimp only [f]; push_cast; ring
  have hPEq : P = ((-(t + u) : ℝ) : ℂ) * v + ((x - r : ℝ) : ℂ) := by
    dsimp only [P, G]
    push_cast
    ring
  have hVEq : V = ((-t : ℝ) : ℂ) * v + ((x - r - u : ℝ) : ℂ) := by
    dsimp only [V, W₀, f]
    push_cast
    ring
  have hivf : (v / f).im = x * v.im / Ef := by
    have h := linear_fraction_im v 1 0 (-t) x
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, zero_add, add_zero, sub_zero] at h
    rw [← hfEq] at h
    exact h
  have hif : ((1 : ℂ) / f).im = t * v.im / Ef := by
    have h := linear_fraction_im v 0 1 (-t) x
    simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, zero_add, one_mul, zero_sub, neg_neg] at h
    rw [← hfEq] at h
    exact h
  have hiVP : (V / P).im = u * L * v.im / Ep := by
    have h := linear_fraction_im v (-t) (x - r - u) (-(t + u)) (x - r)
    rw [← hVEq, ← hPEq] at h
    change (V / P).im = _ at h
    convert h using 1 <;> dsimp only [L] <;> ring
  let q := D * ((x - 1) * (t * (t + u - 1) - u) - r * u)
  let b := r ^ 2 * ((x - 1) * (t ^ 2 - t - u) + t * u * x) +
    r * x * ((x - 1) * t * (1 - t) + u ^ 2) + u * x ^ 2 * (x - 1) * (1 - t)
  let B := ((q : ℂ) * v + b) / P
  have hiB : B.im = -r * u * J * H * v.im / Ep := by
    have h := linear_fraction_im v q b (-(t + u)) (x - r)
    rw [← hPEq] at h
    change B.im = _ at h
    convert h using 1 <;> dsimp only [q, b, J, H, D] <;> ring
  have hi0 : (R 0).im = -x * v.im / Complex.normSq v := by
    rw [h0, Complex.sub_im, Complex.div_im]
    simp [Complex.ofReal_re, Complex.ofReal_im, neg_mul] <;> ring
  have hi7 : (R 7).im = -(t * (r + u)) * (x * v.im / Ef) := by
    have he : R 7 = t - ((t * (r + u) : ℝ) : ℂ) * (v / f) := by rw [h7]; push_cast; ring
    rw [he, Complex.sub_im, Complex.mul_im, hivf]
    simp [neg_mul]
  have hi10 : (R 10).im = -(r * (x - 1)) * (t * v.im / Ef) := by
    have he : R 10 = ((t - 1 + r : ℝ) : ℂ) - ((r * (x - 1) : ℝ) : ℂ) * (1 / f) := by
      rw [h10]
      push_cast
      ring
    rw [he, Complex.sub_im, Complex.mul_im, hif]
    simp [neg_mul]
  have hi12 : (R 12).im = -r * (u * L * v.im / Ep) := by
    have he : R 12 = ((-L : ℝ) : ℂ) - (r : ℂ) * (V / P) := by
      rw [h12]
      dsimp only [L]
      push_cast
      ring
    rw [he, Complex.sub_im, Complex.mul_im, hiVP]
    simp [neg_mul]
  have h11c : (x : ℂ) * R 11 - ((x - 1 : ℝ) : ℂ) * R 9 = ((r + t + u * x - x : ℝ) : ℂ) := by
    rw [h11, h9]
    field_simp [hf']
    dsimp only [K, W₀, f, C]
    push_cast
    ring
  let denominator := v * (f * P)
  have hdenominator : denominator ≠ 0 := mul_ne_zero hv (mul_ne_zero hf' hP')
  have clear_v (a : ℂ) : a / v * denominator = a * (f * P) := by
    change a / v * (v * (f * P)) = _
    rw [← mul_assoc, div_mul_cancel₀ _ hv]
  have clear_f (a : ℂ) : a / f * denominator = a * (v * P) := by
    change a / f * (v * (f * P)) = _
    rw [← mul_assoc v f P, mul_comm v f, mul_assoc f v P, ← mul_assoc,
      div_mul_cancel₀ _ hf']
  have clear_fP (a : ℂ) : a / (f * P) * denominator = a * v := by
    change a / (f * P) * (v * (f * P)) = _
    rw [mul_comm v (f * P), ← mul_assoc, div_mul_cancel₀ _ (mul_ne_zero hf' hP')]
  have clear_denominator (a : ℂ) : a / (v * (f * P)) * denominator = a :=
    div_mul_cancel₀ a hdenominator
  have h17c : R 17 - A₀ = ((x * (t + u - 1) : ℝ) : ℂ) -
      ((u * x * (x - 1) : ℝ) : ℂ) * (1 / f) := by
    apply mul_right_cancel₀ hdenominator
    dsimp only [A₀]
    rw [h17, h16, h0]
    simp only [sub_mul, add_mul, mul_assoc, clear_v, clear_f, clear_fP, clear_denominator, one_mul]
    dsimp only [denominator, K, W₀, P, G, f, C]
    push_cast
    ring
  have h13c : (H : ℂ) * R 13 - ((t * L : ℝ) : ℂ) * A₀ =
      (((x - 1) * (r * t - t ^ 3 - t ^ 2 * u + 2 * t ^ 2 + 3 * t * u - t * x) - r * u - u ^ 2 : ℝ) : ℂ) +
        ((u * x * (t - 1) * W : ℝ) : ℂ) * (1 / f) := by
    apply mul_right_cancel₀ hdenominator
    dsimp only [A₀]
    rw [h13, h16, h0]
    simp only [sub_mul, add_mul, mul_assoc, clear_v, clear_f, clear_fP, clear_denominator, one_mul]
    dsimp only [denominator, H, L, W, W₀, V, P, G, f, C]
    push_cast
    ring
  have h22c : (H : ℂ) * R 22 - (((t - 1) * (x - r) : ℝ) : ℂ) * A₀ =
      (((x - 1) * (2 * r * t + t ^ 2 + t * u - 2 * t * x + x) - r * (r + u) : ℝ) : ℂ) +
        ((r * x * (t - 1) * (x - r - u - 1) : ℝ) : ℂ) * (1 / f) := by
    apply mul_right_cancel₀ hdenominator
    dsimp only [A₀]
    rw [h22, h16, h0]
    simp only [sub_mul, add_mul, mul_assoc, clear_v, clear_f, clear_fP, clear_denominator, one_mul]
    dsimp only [denominator, H, W₀, P, G, f, C]
    push_cast
    ring
  have hDAc : (D : ℂ) * A₀ = ((r * u * x * (t - 1) * (x - 1) : ℝ) : ℂ) * (1 / f) + B := by
    dsimp only [A₀, B]
    rw [h16, h0]
    field_simp [hv, hf', hP']
    dsimp only [q, b, D, W₀, P, G, f, C]
    push_cast
    ring
  have hiA : A = μ * A₀.im := by dsimp only [A, A₀]; rw [hgR, hgR, Complex.sub_im]; ring
  have hρ : ρ = μ * v.im := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgR, hi0, hρ]; ring
  · rw [hgR, hi7]; dsimp only [τ]; rw [hρ]; ring
  · rw [hgR, hi10]; dsimp only [τ]; rw [hρ]; ring
  · have him := congrArg Complex.im h11c
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero] at him
    simp only [hgR]
    linear_combination μ * him
  · rw [hgR, hi12, hρ]; ring
  · have him := congrArg Complex.im h17c
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero, hif] at him
    rw [hgR, hiA]
    dsimp only [τ]
    rw [hρ]
    linear_combination μ * him
  · have him := congrArg Complex.im h13c
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      zero_mul, add_zero, zero_add, hif] at him
    rw [hgR, hiA]
    dsimp only [τ]
    rw [hρ]
    linear_combination μ * him
  · have him := congrArg Complex.im h22c
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      zero_mul, add_zero, zero_add, hif] at him
    rw [hgR, hiA]
    dsimp only [τ]
    rw [hρ]
    linear_combination μ * him
  · have him := congrArg Complex.im hDAc
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      zero_mul, add_zero, hif, hiB] at him
    rw [hiA]
    dsimp only [τ]
    rw [hρ]
    linear_combination μ * him

set_option maxHeartbeats 2100000 in
/-- The supported T5 chart satisfies one of its two exact capacities. -/
theorem fourT5_projective_capacity (x t r u : ℝ) (z w v η : ℂ)
    (hv : v ≠ 0) (ht : t ≠ 0) (ht₁ : t ≠ 1) (hr : r ≠ 0) (hu : u ≠ 0) (hzw : z ≠ w)
    (hf : (x : ℂ) - t * v ≠ 0)
    (hG : (x : ℂ) - ((t : ℂ) + u) * v ≠ 0) (hP : (x : ℂ) - ((t : ℂ) + u) * v - r ≠ 0)
    (hz : z = (r : ℂ) * v / ((x : ℂ) - ((t : ℂ) + u) * v))
    (hw : w = ((x : ℂ) - r - (t : ℂ) * v) / u) (hdir : (η * (v * (z - w))).re = 0) :
    let F := fourT5PoleProduct z x w v t
    let g (i : Fin 24) := (η * (F i - F 1)).re
    let A := g 16 - g 0
    (∀ i, 0 ≤ g i) → g 11 = -g 7 + g 9 + g 10 → g 17 = A - g 7 + g 9 → A < 0 →
    A ^ 2 ≤ g 10 * g 13 ∨ A ^ 2 * (g 22 + g 17 + g 7 - A) ≤ g 22 * g 17 * (g 7 + A) := by
  intro F g A hg h11 h17 hA
  let ρ := -(η * (v * (z - w))).im * v.im
  let Ef := Complex.normSq ((x : ℂ) - t * v)
  let Ep := Complex.normSq ((x : ℂ) - ((t : ℂ) + u) * v - r)
  let τ := ρ / Ef
  let ratio := Ef / Ep
  let L := x - r - t - u
  let H := -r * t + t * (x - 1) - u
  let W := t * (x - 1) - r - u
  let D := r * t + u * x
  let J := r + (t + u - 1) * x
  obtain ⟨h0, h7, h10, hx11, h12, h17', h13, h22, hDA⟩ :=
    fourT5_projective_gap_identities x t r u z w v η hv hu hzw hf hG hP hz hw hdir
  have hEf : 0 < Ef := Complex.normSq_pos.mpr hf
  have hEp : 0 < Ep := Complex.normSq_pos.mpr hP
  have hratio_pos : 0 < ratio := div_pos hEf hEp
  have h0' : 0 < g 0 := by dsimp only [A] at hA; linarith only [hA, hg 16]
  have hρx : ρ * x < 0 := by
    have hp : 0 < -ρ * x := (div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hv)).mp (h0 ▸ h0')
    linarith only [hp]
  have hτx : τ * x < 0 := by
    dsimp only [τ]
    rw [div_mul_eq_mul_div]
    exact div_neg_of_neg_of_pos hρx hEf
  let S := |τ|
  have hS : 0 < S := abs_pos.mpr (left_ne_zero_of_mul hτx.ne)
  let σ := τ / S
  let q (i : Fin 24) := g i / S
  let a := A / S
  have hσ : |σ| = 1 := by
    dsimp only [σ, S]
    rw [abs_div, abs_abs, div_self hS.ne']
  have hσx : σ * x < 0 := by
    dsimp only [σ]
    rw [div_mul_eq_mul_div]
    exact div_neg_of_neg_of_pos hτx hS
  have hq (i : Fin 24) : 0 ≤ q i := div_nonneg (hg i) hS.le
  have h9' : 0 < g 9 := by linarith only [h17, hA, hg 17, hg 7]
  have h11' : 0 < g 11 := by linarith only [h11, h17, hA, hg 17, hg 10]
  have hτratio : τ * ratio = ρ / Ep := by
    dsimp only [τ, ratio]
    field_simp [hEf.ne', hEp.ne'] <;> ring
  have h12' : g 12 = ratio * (-τ * r * u * L) := by
    change g 12 = -(ρ / Ep) * r * u * L at h12
    linear_combination h12 + r * u * L * hτratio
  have h12'' : 0 ≤ -σ * r * u * L := by
    have hp := (mul_nonneg_iff_of_pos_left hratio_pos).mp (h12' ▸ hg 12)
    have h := div_nonneg hp hS.le
    dsimp only [σ]
    convert h using 1 <;> field_simp [hS.ne'] <;> ring
  have hDA' : D * A = τ * r * u * (x * t * (t - 1) * (x - 1) - J * H * ratio) := by
    change D * A = τ * r * u * (x * t * (t - 1) * (x - 1)) - (ρ / Ep) * r * u * J * H at hDA
    linear_combination hDA + r * u * J * H * hτratio
  have hx11' : x * q 11 = (x - 1) * q 9 := by
    change x * g 11 = (x - 1) * g 9 at hx11
    dsimp only [q]
    field_simp [hS.ne']
    linear_combination hx11
  have h7' : q 7 = -σ * t * x * (r + u) := by
    change g 7 = -τ * t * x * (r + u) at h7
    dsimp only [q, σ]
    field_simp [hS.ne']
    linear_combination h7
  have h10' : q 10 = -σ * r * t * (x - 1) := by
    change g 10 = -τ * r * t * (x - 1) at h10
    dsimp only [q, σ]
    field_simp [hS.ne']
    linear_combination h10
  have h17'' : q 17 = a - σ * t * u * x * (x - 1) := by
    change g 17 = A - τ * t * u * x * (x - 1) at h17'
    dsimp only [q, a, σ]
    field_simp [hS.ne']
    linear_combination h17'
  have h13' : H * q 13 = t * L * a + σ * t * u * x * (t - 1) * W := by
    change H * g 13 = t * L * A + τ * t * u * x * (t - 1) * W at h13
    dsimp only [q, a, σ]
    field_simp [hS.ne']
    linear_combination h13
  have h22' : H * q 22 = (t - 1) * (x - r) * a + σ * r * t * x * (t - 1) * (x - r - u - 1) := by
    change H * g 22 = (t - 1) * (x - r) * A + τ * r * t * x * (t - 1) * (x - r - u - 1) at h22
    dsimp only [q, a, σ]
    field_simp [hS.ne']
    linear_combination h22
  have hDA'' : D * a = σ * r * u * (x * t * (t - 1) * (x - 1) - J * H * ratio) := by
    dsimp only [a, σ]
    field_simp [hS.ne']
    linear_combination hDA'
  have h := fourT5_capacity_of_normalized_gaps x t r u σ ratio a q ht ht₁ hr hratio_pos
    (div_neg_of_neg_of_pos hA hS) hσ hσx hq (div_pos h9' hS) (div_pos h11' hS) hx11'
    h7' h10' h12'' h17'' h13' h22' hDA''
  rcases h with h | h
  · left
    dsimp only [a, q] at h
    rw [div_pow, div_mul_div_comm, ← pow_two] at h
    exact (div_le_div_iff_of_pos_right (pow_pos hS 2)).mp h
  · right
    dsimp only [a, q] at h
    have hleft : (A / S) ^ 2 * (g 22 / S + g 17 / S + g 7 / S - A / S) =
        (A ^ 2 * (g 22 + g 17 + g 7 - A)) / S ^ 3 := by
      rw [← add_div, ← add_div, ← sub_div, div_pow, div_mul_div_comm, ← pow_succ]
    have hright : g 22 / S * (g 17 / S) * (g 7 / S + A / S) =
        (g 22 * g 17 * (g 7 + A)) / S ^ 3 := by
      rw [← add_div, div_mul_div_comm, ← pow_two, div_mul_div_comm, ← pow_succ]
    rw [hleft, hright] at h
    exact (div_le_div_iff_of_pos_right (pow_pos hS 3)).mp h

end MOC

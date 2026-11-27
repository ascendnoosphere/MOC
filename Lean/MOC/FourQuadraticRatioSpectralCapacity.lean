import MOC.FourQuadraticRatioChart
import Mathlib.Tactic.Linarith

/-! The distinct quadratic-ratio pattern spectral chart satisfies the exact four-budget bound. -/

namespace MOC

private theorem quadraticRatio_budget_scale (a b c d s : ℝ) :
    (d / s) ^ 2 * (a / s + b / s + c / s + d / s) =
      (d ^ 2 * (a + b + c + d)) / s ^ 3 ∧
    (a / s) * (b / s) * (c / s - d / s) = (a * b * (c - d)) / s ^ 3 := by
  constructor <;> simp only [div_eq_mul_inv, ← inv_pow] <;> ring

set_option maxHeartbeats 4000000 in
/-- In the distinct quadratic-ratio pattern chart, nonnegative supporting gaps force the
four-budget capacity whenever `g₂ - g₁₃` is positive. -/
theorem fourQuadraticRatio_projective_capacity (x t r u : ℝ) (z w v η : ℂ)
    (hv : v ≠ 0) (hzw : z ≠ w) (ht : t ≠ 0) (hr : r ≠ 0) :
    let F := fourQuadraticRatioPoleProduct z x w v t
    let D := v * (z - w)
    let g (i : Fin 24) := (η * (F i - F 0)).re
    let d := g 2 - g 13
    let f := (t : ℂ) * v - x
    let T := (t : ℂ) * v - 1
    let W := -(r : ℂ) * f + (u : ℂ) * T
    let Z := f * T - v * W
    f ≠ 0 → T ≠ 0 → W ≠ 0 → Z ≠ 0 →
    z = (r : ℂ) * v * f / Z → w = -f * ((r : ℂ) + 1 - t * v) / W →
    (η * D).re = 0 → (∀ i, 0 ≤ g i) → 0 < d → g 9 = g 15 + d →
    d ^ 2 * (g 15 + g 19 + g 10 + d) < g 15 * g 19 * (g 10 - d) := by
  classical
  intro F D g d f T W Z hf hT hW hZ hz hw hdir hg hd h9
  let R (i : Fin 24) := (F i - F 0) / D
  let p := η * D
  let y := x - 1
  let h := 1 - t
  let H := h + u
  let E := H * (1 - t * x) - h * r * y
  let J := H * (1 - t * x) + h * y
  let Q := quadraticRatioQuadraticEval (quadraticRatioShiftedDen x t r u) f
  let B := quadraticRatioQuadraticEval (quadraticRatioShiftedNumB x t r u) f
  let N := quadraticRatioQuadraticEval (quadraticRatioShiftedNumD x t r u) f
  obtain ⟨hQ, hR2, hR6, hR10, hR9, hRN, hRB, hRC, hRE⟩ :=
    fourQuadraticRatio_exact_pole_ratios x t r u z w v hv hzw ht hf hT hW hZ hz hw
  have hD : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hgR (i : Fin 24) : g i = -p.im * (R i).im := by
    have heq : η * (F i - F 0) = p * R i := by
      dsimp only [p, R]
      field_simp [hD] <;> ring
    change (η * (F i - F 0)).re = _
    rw [heq, Complex.mul_re, show p.re = 0 from hdir, zero_mul, zero_sub, neg_mul]
  have h9real : g 9 = y * g 10 := by
    have him : (R 9).im = y * (R 10).im := by
      have he : R 9 = (y : ℂ) * R 10 + ((y ^ 2 - r * y + u : ℝ) : ℂ) := hR9
      rw [he]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
    rw [hgR 9, hgR 10, him]
    ring
  have hyc : 0 < y * g 10 := by linarith only [h9real, h9, hg 15, hd]
  have hy : 0 < y := pos_of_mul_pos_left hyc (hg 10)
  have hx : 1 < x := sub_pos.mp hy
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hpos_c : 0 < g 10 := (mul_pos_iff_of_pos_left hy).mp hyc
  let s := -p.im * v.im
  have hIm2 : (R 2).im = x * v.im / Complex.normSq v := by
    have he : R 2 = (t : ℂ) - (x : ℂ) / v := by
      rw [show R 2 = f / v from hR2]
      dsimp only [f]
      field_simp [hv] <;> ring
    rw [he, Complex.sub_im, Complex.ofReal_im, Complex.div_im]
    simp [Complex.ofReal_re, Complex.ofReal_im]
  have h2 : g 2 = s * (x / Complex.normSq v) := by rw [hgR, hIm2]; dsimp only [s]; ring
  have h2pos : 0 < g 2 := by
    have hd' : 0 < g 2 - g 13 := hd
    linarith only [hd', hg 13]
  have hs : 0 < s := (mul_pos_iff_of_pos_right (div_pos hx₀ (Complex.normSq_pos.mpr hv))).mp
    (h2 ▸ h2pos)
  have hvi : v.im ≠ 0 := right_ne_zero_of_mul hs.ne'
  have hpi : p.im ≠ 0 := fun he => by simp [s, he] at hs
  have hIm6 : (R 6).im = r * t * y * v.im / Complex.normSq T := by
    have he : R 6 = (r : ℂ) - ((r * y : ℝ) : ℂ) / T := by
      rw [show R 6 = (r : ℂ) * f / T from hR6]
      field_simp [hT]
      dsimp only [f, T, y]
      push_cast
      ring
    rw [he, Complex.sub_im, Complex.ofReal_im, Complex.div_im]
    dsimp only [T]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.mul_im,
      Complex.one_im, zero_mul, add_zero, sub_zero, zero_sub, neg_neg]
    ring
  have hIm10 : (R 10).im = -(t * u * x) * v.im / Complex.normSq f := by
    have he : R 10 = ((u - x : ℝ) : ℂ) + ((u * x : ℝ) : ℂ) / f := by
      rw [show R 10 = (t : ℂ) * v * u / f - x from hR10]
      field_simp [hf]
      dsimp only [f]
      push_cast
      ring
    rw [he, Complex.add_im, Complex.ofReal_im, Complex.div_im]
    dsimp only [f]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.mul_im,
      zero_mul, add_zero, sub_zero, zero_add, zero_sub]
    ring
  have h6 : g 6 = s * (r * t * y / Complex.normSq T) := by rw [hgR, hIm6]; dsimp only [s]; ring
  have h10 : g 10 = s * (-(t * u * x) / Complex.normSq f) := by rw [hgR, hIm10]; dsimp only [s]; ring
  have hrt : 0 < r * t := by
    have hp' := hg 6
    rw [h6] at hp'
    have hp := (mul_nonneg_iff_of_pos_left hs).mp hp'
    have hp₂ := mul_nonneg hp (Complex.normSq_nonneg T)
    rw [div_mul_cancel₀ _ (Complex.normSq_pos.mpr hT).ne'] at hp₂
    exact lt_of_le_of_ne ((mul_nonneg_iff_of_pos_right hy).mp hp₂) (mul_ne_zero hr ht).symm
  have htu : t * u < 0 := by
    have hp' := hpos_c
    rw [h10] at hp'
    have hp := (mul_pos_iff_of_pos_left hs).mp hp'
    have hn := neg_pos.mp ((div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hf)).mp hp)
    exact neg_of_mul_neg_left hn hx₀.le
  have hgC : g 16 = h * g 10 - t * (g 19 + d) := by
    have hi : (R 16).im - h * (R 10).im + t * ((R 19).im + ((R 2).im - (R 13).im)) = 0 := by
      have hh := congrArg Complex.im hRC
      simpa only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, add_zero] using hh
    dsimp only [d]
    simp only [hgR]
    linear_combination (-p.im) * hi
  have hgE : E * g 14 = t * y * H * g 19 - J * d := by
    have hi : E * (R 14).im - t * y * H * (R 19).im + J * ((R 2).im - (R 13).im) = 0 := by
      have hh := congrArg Complex.im hRE
      simpa only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, add_zero] using hh
    dsimp only [d]
    simp only [hgR]
    linear_combination (-p.im) * hi
  have hfi : f.im = t * v.im := by simp [f, Complex.sub_im, Complex.mul_im]
  have hfinonzero : f.im ≠ 0 := by rw [hfi]; exact mul_ne_zero ht hvi
  have hBnorm : g 19 / s = t * ((B / Q).im / f.im) := by
    rw [hgR, show R 19 = B / Q from hRB, hfi]
    dsimp only [s]
    field_simp [hpi, ht, hvi] <;> ring
  have hNnorm : d / s = t * ((N / Q).im / f.im) := by
    dsimp only [d]
    rw [hgR 2, hgR 13, ← mul_sub, ← Complex.sub_im, show R 2 - R 13 = N / Q from hRN, hfi]
    dsimp only [s]
    field_simp [hpi, ht, hvi] <;> ring
  have ha : g 15 / s = (x - 1) * (g 10 / s) - d / s := by
    field_simp [hs.ne']
    linear_combination h9real - h9
  have hk : g 16 / s = h * (g 10 / s) - t * (g 19 / s + d / s) := by
    field_simp [hs.ne']
    linear_combination hgC
  have he : E * (g 14 / s) = t * y * H * (g 19 / s) - J * (d / s) := by
    field_simp [hs.ne']
    linear_combination hgE
  have hcap := fourQuadraticRatio_capacity_of_quadratic_ratios (x := x) (t := t) (r := r) (u := u)
    f hx hrt htu (div_nonneg (hg 19) hs.le) (div_pos hpos_c hs) (div_pos hd hs)
    (div_nonneg (hg 14) hs.le) (div_nonneg (hg 16) hs.le) ha hfinonzero
    hQ hBnorm hNnorm hk he
  obtain ⟨hleft, hright⟩ := quadraticRatio_budget_scale (g 15) (g 19) (g 10) d s
  rw [hleft, hright] at hcap
  exact (div_lt_div_iff_of_pos_right (pow_pos hs 3)).mp hcap

end MOC

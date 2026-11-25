import MOC.FourT5Chart
import Mathlib.Tactic.FieldSimp

/-! The nonreal T15 pole chart, with its real parameter stratum detected
by the gap at index zero. -/

namespace MOC

/-- T15 uses the negative of the T5 original product convention. -/
noncomputable def fourT15PoleRatio (z x w v t : ℂ) (i : Fin 24) : ℂ :=
  (fourT5PoleProduct z x w v t 1 - fourT5PoleProduct z x w v t i) / (v * (z - w))

/-- Real `x` and `v` make the zeroth normalized T15 gap zero. -/
theorem fourT15_pole_ratio_zero (z x w v t : ℂ) (hv : v ≠ 0) (hzw : z ≠ w) :
    fourT15PoleRatio z x w v t 0 = x - x / v := by
  have h1 : fourT5PoleProduct z x w v t 1 = t * v * (v - 1) * (z - w) :=
    fourT5_pole_product_values z x w v t 1
  have h0 : fourT5PoleProduct z x w v t 0 = (1 - v) * (z - w) * (x - t * v) :=
    fourT5_pole_product_values z x w v t 0
  rw [fourT15PoleRatio, h1, h0]
  field_simp [hv, sub_ne_zero.mpr hzw] <;> ring

/-- The last two T15 contacts force `z = v/(v+1-w)` when `v` is nonreal.
The real-`v` branch is tested by `fourT15_pole_ratio_zero`. -/
theorem fourT15_pole_chart (x t : ℝ) (z w v : ℂ) (hx : x ≠ 0) (ht : t ≠ 0)
    (hv : v ≠ 0) (hzw : z ≠ w) (hf : (x : ℂ) - (t : ℂ) * v ≠ 0) (hvi : v.im ≠ 0)
    (h6 : (fourT15PoleRatio z x w v t 6).im = 0) (h7 : (fourT15PoleRatio z x w v t 7).im = 0) :
    v + 1 - w ≠ 0 ∧ z = v / (v + 1 - w) := by
  let D := v * (z - w)
  let f := (x : ℂ) - (t : ℂ) * v
  let R := fourT15PoleRatio z x w v t
  let J := (x : ℂ) - (t : ℂ) - R 6
  have hD : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hf' : f ≠ 0 := hf
  have hf₁ : fourT5PoleProduct z x w v t 1 = D * ((t : ℂ) * (v - 1)) := by
    rw [show fourT5PoleProduct z x w v t 1 = (t : ℂ) * v * (v - 1) * (z - w) from
      fourT5_pole_product_values z x w v t 1]
    dsimp only [D]
    ring
  have hf₆ : fourT5PoleProduct z x w v t 6 = -(z - v) * (w - 1) * f := by
    rw [show fourT5PoleProduct z x w v t 6 = (z - v) * (1 - w) * f from
      fourT5_pole_product_values z x w v t 5]
    ring
  have hf₇ : fourT5PoleProduct z x w v t 7 = (t : ℂ) * v * (z - v) * (w - 1) :=
    fourT5_pole_product_values z x w v t 6
  have hR6 : R 6 = (t : ℂ) * (v - 1) + (z - v) * (w - 1) * f / D := by
    change (fourT5PoleProduct z x w v t 1 - fourT5PoleProduct z x w v t 6) / D = _
    rw [hf₁, hf₆, sub_div, mul_div_cancel_left₀ _ hD]
    ring
  have hR7 : R 7 = (t : ℂ) * (v - 1) - (t : ℂ) * v * (z - v) * (w - 1) / D := by
    change (fourT5PoleProduct z x w v t 1 - fourT5PoleProduct z x w v t 7) / D = _
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

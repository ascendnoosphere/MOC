import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Schwarz–Pick for two positive real inputs of a holomorphic self-map of
the right half-plane, expressed in real and imaginary coordinates. -/

namespace MOC

/-- The change in imaginary part is bounded by the two real-part deficits
from the Schwarz–Pick estimate on the right half-plane. -/
theorem halfPlane_schwarz_pick_im_sq (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (hpos : ∀ z : ℂ, 0 < z.re → 0 < (f z).re)
    {t x : ℝ} (ht : 0 < t) (htx : t ≤ x) :
    ((f (x : ℂ)).im - (f (t : ℂ)).im) ^ 2 ≤
      (x * (f (t : ℂ)).re / t - (f (x : ℂ)).re) *
        ((f (x : ℂ)).re - t * (f (t : ℂ)).re / x) := by
  let D : Set ℂ := Metric.ball 0 1
  let H : Set ℂ := {z : ℂ | 0 < z.re}
  let v := f (t : ℂ)
  let d (z : ℂ) := (t : ℂ) * (1 + z) / (1 - z)
  let m (w : ℂ) := (w - v) / (w + star v)
  let g := m ∘ (f ∘ d)
  have hv : 0 < v.re := hpos (t : ℂ) (by simpa only [Complex.ofReal_re] using ht)
  have hdDen (z : ℂ) (hz : z ∈ D) : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hz' : z = 1 := (sub_eq_zero.mp h).symm
    have hn : ‖z‖ < 1 := by simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    simpa [hz'] using hn
  have hmDen (w : ℂ) (hw : w ∈ H) : w + star v ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at he
    change 0 < w.re at hw
    linarith only [hw, hv, he]
  have hdMap : Set.MapsTo d D H := by
    intro z hz
    have hn : ‖z‖ < 1 := by simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    have hs : Complex.normSq z < 1 := by
      simpa only [← Complex.normSq_eq_norm_sq, one_pow] using
        (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mpr hn
    have hre : (d z).re = t * (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
      simp only [d, Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
      rw [← add_div]
      congr 1 <;> ring
    change 0 < (d z).re
    rw [hre]
    exact div_pos (mul_pos ht (sub_pos.mpr hs)) (Complex.normSq_pos.mpr (hdDen z hz))
  have hmMap : Set.MapsTo m H D := by
    intro w hw
    have he : Complex.normSq (w + star v) - Complex.normSq (w - v) = 4 * w.re * v.re := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    have hw' : 0 < w.re := hw
    have hprod : 0 < 4 * w.re * v.re := by positivity
    have hlt : Complex.normSq (w - v) < Complex.normSq (w + star v) := by
      linarith only [he, hprod]
    change m w ∈ Metric.ball (0 : ℂ) 1
    rw [Metric.mem_ball, dist_zero_right]
    apply (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← Complex.normSq_eq_norm_sq, one_pow, show m w = (w - v) / (w + star v) from rfl,
      Complex.normSq_div]
    exact (div_lt_one (Complex.normSq_pos.mpr (hmDen w hw))).mpr hlt
  have hdDiff : DifferentiableOn ℂ d D := by
    change DifferentiableOn ℂ (fun z : ℂ => (t : ℂ) * (1 + z) / (1 - z)) D
    apply DifferentiableOn.div
    · fun_prop
    · fun_prop
    · exact hdDen
  have hmDiff : DifferentiableOn ℂ m H := by
    change DifferentiableOn ℂ (fun w : ℂ => (w - v) / (w + star v)) H
    apply DifferentiableOn.div
    · fun_prop
    · fun_prop
    · exact hmDen
  have hfMap : Set.MapsTo f H H := fun z hz => hpos z hz
  have hgDiff : DifferentiableOn ℂ g D :=
    hmDiff.comp (hf.comp hdDiff hdMap) (hfMap.comp hdMap)
  have hgMap : Set.MapsTo g D D := hmMap.comp (hfMap.comp hdMap)
  have hdZero : d 0 = (t : ℂ) := by simp [d]
  have hgZero : g 0 = 0 := by simp [g, m, hdZero, v]
  have hx : 0 < x := ht.trans_le htx
  have hxt : 0 < x + t := add_pos hx ht
  let q := (x - t) / (x + t)
  let u : ℂ := (q : ℂ)
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr htx) hxt.le
  have hqLt : q < 1 := (div_lt_one hxt).mpr (by linarith only [ht])
  have hu : ‖u‖ = q := by
    rw [show u = (q : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  have hdU : d u = (x : ℂ) := by
    have hreal : t * (1 + q) / (1 - q) = x := by
      apply (div_eq_iff (sub_ne_zero.mpr hqLt.ne.symm)).mpr
      dsimp only [q]
      field_simp [hxt.ne'] <;> ring
    simpa only [d, u, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_one] using congrArg (fun y : ℝ => (y : ℂ)) hreal
  have hgU : g u = m (f (x : ℂ)) := by simp only [g, Function.comp_apply, hdU]
  have huLt : ‖u‖ < 1 := hu.trans_lt hqLt
  have hn := Complex.norm_le_norm_of_mapsTo_ball_self hgDiff hgMap hgZero huLt
  rw [hgU, hu] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _) hq).mpr hn
  rw [← Complex.normSq_eq_norm_sq, show m (f (x : ℂ)) = (f (x : ℂ) - v) /
    (f (x : ℂ) + star v) from rfl, Complex.normSq_div, show q = (x - t) / (x + t) from rfl,
    div_pow] at hs
  have hfw : f (x : ℂ) ∈ H := hpos (x : ℂ) (by simpa only [Complex.ofReal_re] using hx)
  have hc := (div_le_div_iff₀ (Complex.normSq_pos.mpr (hmDen _ hfw)) (pow_pos hxt 2)).mp hs
  let a := (f (x : ℂ)).re
  let b := v.re
  let e := (f (x : ℂ)).im - v.im
  have hnum : Complex.normSq (f (x : ℂ) - v) = (a - b) ^ 2 + e ^ 2 := by
    simp only [a, b, e, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two]
  have hden : Complex.normSq (f (x : ℂ) + star v) = (a + b) ^ 2 + e ^ 2 := by
    simp only [a, b, e, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, pow_two, sub_eq_add_neg]
  rw [hnum, hden] at hc
  change e ^ 2 ≤ (x * b / t - a) * (a - t * b / x)
  apply (mul_le_mul_left (mul_pos hx ht)).mp
  have hprod : (x * t) * ((x * b / t - a) * (a - t * b / x)) =
      (x ^ 2 + t ^ 2) * (a * b) - (x * t) * (a ^ 2 + b ^ 2) := by
    field_simp [hx.ne', ht.ne'] <;> ring
  rw [hprod]
  nlinarith only [hc]

end MOC

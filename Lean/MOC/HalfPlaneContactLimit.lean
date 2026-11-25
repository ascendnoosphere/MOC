import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-! A positive-real holomorphic function has a nonnegative real linear
asymptote along the positive real axis. This is the radial case of the
classical Julia–Carathéodory boundary comparison; here it follows directly
from the Schwarz lemma, with no projective or meromorphic completion.
For the broader half-plane angular-derivative theorem, see Elliott and
Jury, Proposition 2.2 (DOI: 10.1112/blms/bdr110; preprint DOI:
10.48550/arXiv.0907.0350). -/

open Filter Set Metric
open scoped Topology

namespace MOC
noncomputable section

private def rightToDisk (z : ℂ) : ℂ := (z - 1) / (z + 1)
private def diskToRight (t : ℝ) (z : ℂ) : ℂ := (t : ℂ) * ((1 + z) / (1 - z))

private theorem rightToDisk_norm_lt {z : ℂ} (hz : 0 < z.re) :
    ‖rightToDisk z‖ < 1 := by
  have hne : z + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith
  have hsq : ‖z - 1‖ ^ 2 < ‖z + 1‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_add,
      Complex.normSq_one, map_one, mul_one]
    linarith
  rw [rightToDisk, norm_div, div_lt_iff₀ (norm_pos_iff.mpr hne), one_mul]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

private theorem diskToRight_re_pos {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : ‖z‖ < 1) :
    0 < (diskToRight t z).re := by
  have hn : 1 - z ≠ 0 := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    simp [he] at hz
  have hnorm : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have h₁ : ((1 + z) / (1 - z)).re = (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
    rw [Complex.div_re, Complex.normSq_apply z]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add,
      Complex.sub_re, Complex.sub_im, zero_sub]
    ring
  rw [diskToRight, Complex.re_ofReal_mul, h₁]
  exact mul_pos ht (div_pos (sub_pos.mpr hnorm) (Complex.normSq_pos.mpr hn))

private theorem halfPlane_radial_estimate (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z | 0 < z.re}) (hpos : ∀ z, 0 < z.re → 0 < (f z).re)
    {s x : ℝ} (hs : 0 < s) (hsx : s ≤ x) :
    ‖f (x : ℂ) - (f (s : ℂ)).im • Complex.I‖ ≤ x * ((f (s : ℂ)).re / s) := by
  let b := (f (s : ℂ)).im • Complex.I
  let a := (f (s : ℂ)).re
  have ha : 0 < a := hpos s (by simpa)
  let w (z : ℂ) := (f (diskToRight s z) - b) / (a : ℂ)
  have hb : b.re = 0 := by simp [b, Complex.real_smul, Complex.mul_re]
  have hw (z : ℂ) (hz : z ∈ ball 0 1) : 0 < (w z).re := by
    rw [mem_ball, dist_zero_right] at hz
    dsimp only [w]
    rw [Complex.div_ofReal_re, Complex.sub_re, hb, sub_zero]
    exact div_pos (hpos _ (diskToRight_re_pos hs hz)) ha
  have hwd : DifferentiableOn ℂ w (ball 0 1) := by
    have hp : DifferentiableOn ℂ (diskToRight s) (ball 0 1) := by
      dsimp only [diskToRight]
      apply (differentiableOn_const (s : ℂ)).mul
      apply ((differentiableOn_const (1 : ℂ)).add differentiableOn_id).div
        ((differentiableOn_const (1 : ℂ)).sub differentiableOn_id)
      intro z hz he
      change (1 : ℂ) - z = 0 at he
      have h : z = 1 := (sub_eq_zero.mp he).symm
      simp [h, mem_ball, dist_zero_right] at hz
    exact ((hf.comp hp (fun z hz => diskToRight_re_pos hs (by simpa [mem_ball, dist_zero_right] using hz))).sub
      (differentiableOn_const b)).div_const _
  have hmap : MapsTo (rightToDisk ∘ w) (ball 0 1) (ball 0 1) := by
    intro z hz
    simpa [mem_ball, dist_zero_right] using rightToDisk_norm_lt (hw z hz)
  have hdiff : DifferentiableOn ℂ (rightToDisk ∘ w) (ball 0 1) := by
    apply (hwd.sub (differentiableOn_const 1)).div (hwd.add (differentiableOn_const 1))
    intro z hz he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith only [hh, hw z hz]
  have hwzero : w 0 = 1 := by
    have hf' : f (s : ℂ) - b = (a : ℂ) := by
      apply Complex.ext <;> simp [a, b, Complex.real_smul, Complex.mul_re, Complex.mul_im]
    have hzero : diskToRight s 0 = s := by simp [diskToRight]
    dsimp only [w]
    rw [hzero, hf', div_self (Complex.ofReal_ne_zero.mpr ha.ne')]
  have hzero : (rightToDisk ∘ w) 0 = 0 := by simp [rightToDisk, hwzero]
  have hx : 0 < x := hs.trans_le hsx
  let r := (x - s) / (x + s)
  have hr₀ : 0 ≤ r := div_nonneg (sub_nonneg.mpr hsx) (add_pos hx hs).le
  have hr₁ : r < 1 := (div_lt_iff₀ (add_pos hx hs)).mpr (by linarith)
  have hrball : (r : ℂ) ∈ ball 0 1 := by
    simpa [mem_ball, dist_zero_right, abs_of_nonneg hr₀] using hr₁
  have hSch := Complex.norm_le_norm_of_mapsTo_ball_self hdiff hmap hzero (mem_ball_zero_iff.mp hrball)
  have hbd : ‖rightToDisk (w r)‖ ≤ r := by
    simpa [abs_of_nonneg hr₀, Function.comp_apply] using hSch
  have hden : w r + 1 ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith only [hh, hw r hrball]
  have hdiv : ‖w r - 1‖ ≤ r * ‖w r + 1‖ := by
    rw [rightToDisk, norm_div] at hbd
    exact (div_le_iff₀ (norm_pos_iff.mpr hden)).mp hbd
  have hupper : ‖w r + 1‖ ≤ ‖w r‖ + 1 := by simpa using norm_add_le (w r) 1
  have hlower : ‖w r‖ ≤ ‖w r - 1‖ + 1 := by
    simpa using norm_add_le (w r - 1) 1
  have hmul : (1 - r) * ‖w r‖ ≤ 1 + r := by
    have h := hdiv.trans (mul_le_mul_of_nonneg_left hupper hr₀)
    linarith only [h, hlower]
  have hrat : (1 + r) / (1 - r) = x / s := by
    dsimp only [r]
    field_simp [hs.ne', (add_pos hx hs).ne']
    ring
  have hval : diskToRight s r = x := by
    rw [diskToRight, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_sub,
      ← Complex.ofReal_div, hrat, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have hh : ‖w r‖ ≤ x / s := by
    rw [← hrat, le_div_iff₀ (sub_pos.mpr hr₁), mul_comm]
    exact hmul
  dsimp only [w] at hh
  rw [hval, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
    div_le_iff₀ ha] at hh
  convert hh using 1
  ring

/-- The complex linear coefficient at infinity is real and nonnegative.
Only positivity of the real part and holomorphy on a half-plane are used. -/
theorem tendsto_positiveReal_div_atTop (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z | 0 < z.re}) (hpos : ∀ z, 0 < z.re → 0 < (f z).re) :
    ∃ a : ℝ, 0 ≤ a ∧ Tendsto (fun x : ℝ => f (x : ℂ) / (x : ℂ)) atTop (𝓝 (a : ℂ)) := by
  let m (x : ℝ) := (f (max x 1 : ℝ)).re / max x 1
  have hm (x : ℝ) : 0 ≤ m x := by
    have hp : 0 < max x (1 : ℝ) := zero_lt_one.trans_le (le_max_right x 1)
    exact (div_pos (hpos _ (by simpa only [Complex.ofReal_re] using hp)) hp).le
  have hmono : Antitone m := by
    intro x y hxy
    let s := max x (1 : ℝ)
    let t := max y (1 : ℝ)
    have hs : 0 < s := zero_lt_one.trans_le (le_max_right x 1)
    have hst : s ≤ t := max_le_max_right _ hxy
    have ht : 0 < t := hs.trans_le hst
    have h := halfPlane_radial_estimate f hf hpos hs hst
    have ht' := Complex.re_le_norm (f (t : ℂ) - (f (s : ℂ)).im • Complex.I)
    have hb : ((f (s : ℂ)).im • Complex.I : ℂ).re = 0 := by
      simp [Complex.real_smul, Complex.mul_re]
    rw [Complex.sub_re, hb, sub_zero] at ht'
    exact (div_le_iff₀ ht).mpr (by simpa [mul_comm] using ht'.trans h)
  let a := ⨅ x, m x
  have hbelow : BddBelow (range m) := ⟨0, by rintro _ ⟨x, rfl⟩; exact hm x⟩
  have ha : 0 ≤ a := le_ciInf hm
  refine ⟨a, ha, ?_⟩
  let g (x : ℝ) := f (x : ℂ) / (x : ℂ)
  have hreal : Tendsto (fun x => (g x).re) atTop (𝓝 a) := by
    refine (tendsto_atTop_ciInf hmono hbelow).congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp [g, m, max_eq_left hx]
  have hn : Tendsto (fun x => ‖g x‖) atTop (𝓝 a) := by
    refine tendsto_order.mpr ⟨fun b hb => ?_, fun b hb => ?_⟩
    · filter_upwards [(tendsto_order.mp hreal).1 b hb] with x hx
      exact hx.trans_le (Complex.re_le_norm _)
    · obtain ⟨s, hs, hsm⟩ := ((eventually_ge_atTop (1 : ℝ)).and
        ((tendsto_order.mp hreal).2 b hb)).exists
      have hsp : 0 < s := zero_lt_one.trans_le hs
      let B := ‖(f (s : ℂ)).im • Complex.I‖
      have hconst : Tendsto (fun x : ℝ => B / x) atTop (𝓝 0) := by
        exact tendsto_const_nhds.div_atTop tendsto_id
      have hlim : Tendsto (fun x : ℝ => (g s).re + B / x) atTop (𝓝 (g s).re) := by
        simpa using tendsto_const_nhds.add hconst
      filter_upwards [eventually_ge_atTop s, (tendsto_order.mp hlim).2 b hsm] with x hx hxl
      have hxp : 0 < x := hsp.trans_le hx
      have h := halfPlane_radial_estimate f hf hpos hsp hx
      have he : ‖f (x : ℂ)‖ ≤ ‖f (x : ℂ) - (f (s : ℂ)).im • Complex.I‖ + B := by
        simpa [B] using norm_add_le (f (x : ℂ) - (f (s : ℂ)).im • Complex.I)
          ((f (s : ℂ)).im • Complex.I)
      apply lt_of_le_of_lt _ hxl
      dsimp only [g]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxp, Complex.div_ofReal_re]
      apply (div_le_iff₀ hxp).mpr
      calc
        _ ≤ x * ((f (s : ℂ)).re / s) + B := he.trans (add_le_add_right h B)
        _ = _ := by field_simp [hxp.ne']; ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : ∀ x, ‖g x - (a : ℂ)‖ ^ 2 = ‖g x‖ ^ 2 + a ^ 2 - 2 * (g x).re * a := by
    intro x
    rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq (g x),
      Complex.normSq_ofReal]
    simp [Complex.mul_re]
    ring
  have hpow : Tendsto (fun x => ‖g x - (a : ℂ)‖ ^ 2) atTop (𝓝 0) := by
    have he := ((hn.pow 2).add_const (a ^ 2)).sub ((hreal.const_mul 2).mul_const a)
    rw [show a ^ 2 + a ^ 2 - 2 * a * a = 0 by ring] at he
    exact he.congr (fun x => (hsq x).symm)
  have hs : Tendsto (fun x => Real.sqrt (‖g x - (a : ℂ)‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hpow
  rw [Real.sqrt_zero] at hs
  exact hs.congr (fun x => Real.sqrt_sq (norm_nonneg (g x - (a : ℂ))))

/-- Allowing zero real part leaves the same boundary conclusion. -/
theorem tendsto_nonnegativeReal_div_atTop (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z | 0 < z.re}) (hpos : ∀ z, 0 < z.re → 0 ≤ (f z).re) :
    ∃ a : ℝ, 0 ≤ a ∧ Tendsto (fun x : ℝ => f (x : ℂ) / (x : ℂ)) atTop (𝓝 (a : ℂ)) := by
  obtain ⟨a, ha, h⟩ := tendsto_positiveReal_div_atTop (fun z => f z + 1)
    (hf.add (differentiableOn_const 1)) (fun z hz => by
      simp only [Complex.add_re, Complex.one_re]
      linarith only [hpos z hz])
  have hinv : Tendsto (fun x : ℝ => (1 : ℂ) / (x : ℂ)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    rw [Complex.ofReal_zero] at hcast
    exact hcast.congr fun x => by rw [Complex.ofReal_inv, one_div]
  refine ⟨a, ha, ?_⟩
  have he := h.sub hinv
  rw [sub_zero] at he
  exact he.congr fun x => by rw [add_div, add_sub_cancel_right]

end
end MOC

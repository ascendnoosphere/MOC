import MOC.HalfPlaneSchwarz
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The normalized Schwarz–Pick inequality along a positive real ray
forces a nonnegative real asymptotic slope. -/

open Filter
open scoped Topology

namespace MOC

/-- The real coordinate of the normalized ray is decreasing, and the
imaginary coordinate tends to zero. -/
theorem exists_real_slope_of_ray_contraction (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (h : ∀ s n : ℕ, s ≤ n →
      (b n - (((s : ℝ) + 1) / ((n : ℝ) + 1)) * b s) ^ 2 ≤
        (a s - a n) * (a n - (((s : ℝ) + 1) / ((n : ℝ) + 1)) ^ 2 * a s)) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto a atTop (𝓝 L) ∧ Tendsto b atTop (𝓝 0) := by
  have hanti : Antitone a := by
    intro s n hsn
    have hr : 0 ≤ ((s : ℝ) + 1) / ((n : ℝ) + 1) := by positivity
    have hr' : ((s : ℝ) + 1) / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      exact add_le_add_right (by exact_mod_cast hsn) 1
    have hsq : (((s : ℝ) + 1) / ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hr hr' 2
    by_contra! hab
    have hm : (((s : ℝ) + 1) / ((n : ℝ) + 1)) ^ 2 * a s ≤ a s := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (ha s)
    have hh := h s n hsn
    exact (not_le_of_gt (mul_neg_of_neg_of_pos (sub_neg.mpr hab) (sub_pos.mpr (hm.trans_lt hab))))
      ((sq_nonneg _).trans hh)
  have hbelow : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; exact ha n⟩
  let L := ⨅ n, a n
  have hL : ∀ n, L ≤ a n := ciInf_le hbelow
  have hL₀ : 0 ≤ L := le_ciInf ha
  have hlim : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciInf hanti hbelow
  refine ⟨L, hL₀, hlim, Metric.tendsto_nhds.2 ?_⟩
  intro ε hε
  let δ := (ε / 2) ^ 2 / (a 0 + 1)
  have hM : 0 < a 0 + 1 := by linarith only [ha 0]
  have hδ : 0 < δ := div_pos (sq_pos_of_pos (by linarith)) hM
  have hsmall : ∀ᶠ n in atTop, a n - L < δ := by
    have hz := hlim.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => L) atTop (𝓝 L))
    rw [sub_self] at hz
    exact hz.eventually (Iio_mem_nhds hδ)
  obtain ⟨s, hs⟩ := hsmall.exists
  have hscore : (a s - L) * a s < (ε / 2) ^ 2 := by
    calc
      _ ≤ (a s - L) * (a 0 + 1) :=
        mul_le_mul_of_nonneg_left ((hanti (Nat.zero_le s)).trans (by linarith))
          (sub_nonneg.mpr (hL s))
      _ < δ * (a 0 + 1) := mul_lt_mul_of_pos_right hs hM
      _ = _ := div_mul_cancel₀ _ hM.ne'
  have htail : Tendsto (fun n : ℕ => ((s : ℝ) + 1) / ((n : ℝ) + 1) * b s) atTop (𝓝 0) := by
    have h0 := (tendsto_const_div_atTop_nhds_zero_nat (((s : ℝ) + 1) * b s)).comp
      (tendsto_add_atTop_nat 1)
    change Tendsto (fun n : ℕ => ((s : ℝ) + 1) * b s / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) at h0
    simpa only [Nat.cast_add, Nat.cast_one, div_mul_eq_mul_div] using h0
  have htail' := Metric.tendsto_nhds.1 htail (ε / 2) (by linarith)
  filter_upwards [eventually_ge_atTop s, htail'] with n hn ht
  have hsq := h s n hn
  have hbnd : (b n - ((s : ℝ) + 1) / ((n : ℝ) + 1) * b s) ^ 2 ≤ (a s - L) * a s := by
    calc
      _ ≤ _ := hsq
      _ ≤ (a s - a n) * a n := mul_le_mul_of_nonneg_left
        (sub_le_self _ (mul_nonneg (sq_nonneg _) (ha s))) (sub_nonneg.mpr (hanti hn))
      _ ≤ (a s - L) * a s := mul_le_mul (sub_le_sub_left (hL n) _) (hanti hn)
        (ha n) (sub_nonneg.mpr (hL s))
  have hd := abs_lt_of_sq_lt_sq (hbnd.trans_lt hscore) (by linarith : 0 ≤ ε / 2)
  rw [Real.dist_eq, sub_zero] at ht ⊢
  have hsum : b n = (b n - (((s : ℝ) + 1) / ((n : ℝ) + 1)) * b s) +
      (((s : ℝ) + 1) / ((n : ℝ) + 1)) * b s := by ring
  calc
    |b n| = |(b n - (((s : ℝ) + 1) / ((n : ℝ) + 1)) * b s) +
        (((s : ℝ) + 1) / ((n : ℝ) + 1)) * b s| := congrArg abs hsum
    _ ≤ |b n - (((s : ℝ) + 1) / ((n : ℝ) + 1)) * b s| +
        |(((s : ℝ) + 1) / ((n : ℝ) + 1)) * b s| := abs_add_le _ _
    _ < ε := by linarith

/-- A holomorphic map of the right half-plane into itself has a
nonnegative real slope along the positive integer ray. -/
theorem exists_real_slope_of_halfPlane_map (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (hpos : ∀ z : ℂ, 0 < z.re → 0 < (f z).re) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto
      (fun n : ℕ => f (((n : ℝ) + 1 : ℝ) : ℂ) / (((n : ℝ) + 1 : ℝ) : ℂ)) atTop (𝓝 (L : ℂ)) := by
  let x (n : ℕ) : ℝ := (n : ℝ) + 1
  let v (n : ℕ) : ℂ := f (x n)
  let a (n : ℕ) : ℝ := (v n).re / x n
  let b (n : ℕ) : ℝ := (v n).im / x n
  have hx (n : ℕ) : 0 < x n := by dsimp [x]; positivity
  have hmono : Monotone x := by
    intro s n hsn
    exact add_le_add_right (by exact_mod_cast hsn) 1
  have ha (n : ℕ) : 0 ≤ a n :=
    div_nonneg (hpos (x n) (by simpa only [Complex.ofReal_re] using hx n)).le (hx n).le
  have hineq (s n : ℕ) (hsn : s ≤ n) :
      (b n - (x s / x n) * b s) ^ 2 ≤
        (a s - a n) * (a n - (x s / x n) ^ 2 * a s) := by
    have hb := halfPlane_schwarz_pick_im_sq f hf hpos (hx s) (hmono hsn)
    calc
      _ = ((v n).im - (v s).im) ^ 2 / x n ^ 2 := by
        dsimp only [b]
        field_simp [(hx s).ne', (hx n).ne'] <;> ring
      _ ≤ ((x n * (v s).re / x s - (v n).re) *
          ((v n).re - x s * (v s).re / x n)) / x n ^ 2 :=
        div_le_div_of_nonneg_right hb (sq_nonneg _)
      _ = _ := by
        dsimp only [a]
        field_simp [(hx s).ne', (hx n).ne'] <;> ring
  obtain ⟨L, hL, hre, him⟩ := exists_real_slope_of_ray_contraction a b ha hineq
  have hre' := Complex.continuous_ofReal.continuousAt.tendsto.comp hre
  have him' := Complex.continuous_ofReal.continuousAt.tendsto.comp him
  have ht := hre'.add (him'.mul_const Complex.I)
  rw [Complex.ofReal_zero, zero_mul, add_zero] at ht
  refine ⟨L, hL, ht.congr' (Filter.Eventually.of_forall fun n => ?_)⟩
  change (a n : ℂ) + (b n : ℂ) * Complex.I = v n / (x n : ℂ)
  dsimp only [a, b]
  rw [← Complex.div_ofReal_re, ← Complex.div_ofReal_im]
  exact Complex.re_add_im _

end MOC

import MOC.Support
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators
open scoped Topology

namespace MOC

noncomputable section

/-- An indexed finite hull is exactly the set of means of probability weights. -/
theorem mem_complex_convexHull_iff_finite_probability {J : Type*} [Fintype J]
    (v : J → ℂ) (z : ℂ) :
    z ∈ convexHull ℝ (Set.range v) ↔ ∃ w : J → ℝ, (∀ j, 0 ≤ w j) ∧
      (∑ j, w j) = 1 ∧ (∑ j, w j • v j) = z := by
  classical
  constructor
  · intro hz
    rw [convexHull_range_eq_exists_affineCombination, Set.mem_setOf_eq] at hz
    obtain ⟨s, w, hw, hs, hsum⟩ := hz
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hsum
    let w' (i : J) := if i ∈ s then w i else 0
    refine ⟨w', fun i => by by_cases hi : i ∈ s <;> simp [w', hi, hw], ?_, ?_⟩
    · simpa only [w', Fintype.sum_ite_mem] using hs
    · simpa only [w', ite_smul, zero_smul, Fintype.sum_ite_mem] using hsum
  · rintro ⟨w, hw, hs, hsum⟩
    exact mem_convexHull_of_exists_fintype w v hw hs (fun j => Set.mem_range_self j) hsum

/-- The centered log-sum-exp of finitely many complex vertices in a real direction. -/
def spectralLogSumExp {J : Type*} [Fintype J]
    (v : J → ℂ) (z : ℂ) (L : ℂ →L[ℝ] ℝ) : ℝ :=
  Real.log (∑ j, Real.exp (L (v j - z)))

private theorem projection_le_spectralLogSumExp {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z w : ℂ) (hw : w ∈ convexHull ℝ (Set.range v))
    (L : ℂ →L[ℝ] ℝ) : L (w - z) ≤ spectralLogSumExp v z L := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun j => L (v j))
    (Finset.univ_nonempty : (Finset.univ : Finset J).Nonempty)
  have hle : L w ≤ L (v j) := by
    apply convexHull_min _ (convex_halfSpace_le L.isLinear _) hw
    rintro _ ⟨i, rfl⟩
    exact hj i (Finset.mem_univ i)
  have he : Real.exp (L (w - z)) ≤ Real.exp (L (v j - z)) :=
    Real.exp_le_exp.mpr (by simpa only [map_sub] using sub_le_sub_right hle (L z))
  have hs : Real.exp (L (v j - z)) ≤ ∑ i, Real.exp (L (v i - z)) :=
    Finset.single_le_sum (fun i _ => (Real.exp_pos (L (v i - z))).le) (Finset.mem_univ j)
  simpa only [Real.log_exp, spectralLogSumExp] using
    Real.log_le_log (Real.exp_pos _) (he.trans hs)

/-- A point of the finite hull has nonnegative centered log-sum-exp in every direction. -/
theorem spectralLogSumExp_nonneg {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) (hz : z ∈ convexHull ℝ (Set.range v))
    (L : ℂ →L[ℝ] ℝ) : 0 ≤ spectralLogSumExp v z L := by
  simpa only [sub_self, map_zero] using projection_le_spectralLogSumExp v z z hz L

/-- Separation gives a linear upper bound tending to negative infinity along a ray. -/
theorem spectralLogSumExp_le_of_not_mem {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) (hz : z ∉ convexHull ℝ (Set.range v)) :
    ∃ (L : ℂ →L[ℝ] ℝ) (ε : ℝ), 0 < ε ∧
      ∀ r : ℝ, 0 ≤ r →
        spectralLogSumExp v z (r • L) ≤ Real.log (Fintype.card J : ℝ) - r * ε := by
  classical
  obtain ⟨L, y, hv, hzy⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (Set.range v)) (Set.finite_range v).isClosed_convexHull hz
  have hε : 0 < L z - y := sub_pos.mpr hzy
  refine ⟨L, L z - y, hε, ?_⟩
  intro r hr
  have hvertex (j : J) : L (v j) ≤ y :=
    (hv (v j) (subset_convexHull ℝ _ ⟨j, rfl⟩)).le
  have hterm (j : J) : Real.exp ((r • L) (v j - z)) ≤ Real.exp (-r * (L z - y)) := by
    apply Real.exp_le_exp.mpr
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub, neg_mul]
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right (hvertex j) (L z)) hr).trans_eq
      (by ring)
  have hpos : 0 < ∑ j, Real.exp ((r • L) (v j - z)) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hsum : (∑ j, Real.exp ((r • L) (v j - z))) ≤
      (Fintype.card J : ℝ) * Real.exp (-r * (L z - y)) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j))
  have hcard : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold spectralLogSumExp
  calc
    _ ≤ Real.log ((Fintype.card J : ℝ) * Real.exp (-r * (L z - y))) :=
      Real.log_le_log hpos hsum
    _ = _ := by rw [Real.log_mul hcard (Real.exp_ne_zero _), Real.log_exp]; ring

/-- Membership, nonnegative log-sum-exp, and boundedness below are equivalent. -/
theorem mem_convexHull_iff_spectralLogSumExp {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) :
    z ∈ convexHull ℝ (Set.range v) ↔ ∀ L : ℂ →L[ℝ] ℝ, 0 ≤ spectralLogSumExp v z L := by
  constructor
  · intro hz L
    exact spectralLogSumExp_nonneg v z hz L
  · intro h
    by_contra hn
    obtain ⟨L, ε, hε, hbound⟩ := spectralLogSumExp_le_of_not_mem v z hn
    let c := Real.log (Fintype.card J : ℝ)
    let r := (|c| + 1) / ε
    have hr : 0 ≤ r := div_nonneg (by positivity) hε.le
    have he : r * ε = |c| + 1 := div_mul_cancel₀ _ hε.ne'
    have hh : spectralLogSumExp v z (r • L) ≤ c - r * ε := hbound r hr
    rw [he] at hh
    linarith only [h (r • L), hh, le_abs_self c]

theorem mem_convexHull_iff_bddBelow_spectralLogSumExp {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) :
    z ∈ convexHull ℝ (Set.range v) ↔ BddBelow (Set.range (spectralLogSumExp v z)) := by
  constructor
  · intro hz
    refine ⟨0, ?_⟩
    rintro _ ⟨L, rfl⟩
    exact spectralLogSumExp_nonneg v z hz L
  · rintro ⟨b, hb⟩
    by_contra hn
    obtain ⟨L, ε, hε, hbound⟩ := spectralLogSumExp_le_of_not_mem v z hn
    let c := Real.log (Fintype.card J : ℝ)
    let r := (|c - b| + 1) / ε
    have hr : 0 ≤ r := div_nonneg (by positivity) hε.le
    have he : r * ε = |c - b| + 1 := div_mul_cancel₀ _ hε.ne'
    have hlow : b ≤ spectralLogSumExp v z (r • L) := hb ⟨r • L, rfl⟩
    have hhigh : spectralLogSumExp v z (r • L) ≤ c - r * ε := hbound r hr
    rw [he] at hhigh
    linarith only [hlow, hhigh, le_abs_self (c - b)]

/-- A ball contained in the hull gives a linear coercivity bound on the potential. -/
theorem mul_norm_le_spectralLogSumExp_of_closedBall {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hb : Metric.closedBall z r ⊆ convexHull ℝ (Set.range v)) (L : ℂ →L[ℝ] ℝ) :
    r * ‖L‖ ≤ spectralLogSumExp v z L := by
  let ψ := spectralLogSumExp v z L
  have hz : z ∈ convexHull ℝ (Set.range v) := hb (Metric.mem_closedBall_self hr.le)
  have hψ : 0 ≤ ψ := spectralLogSumExp_nonneg v z hz L
  have hopen (w : ℂ) (hw : ‖w‖ ≤ r) : L w ≤ ψ := by
    have hmem : z + w ∈ Metric.closedBall z r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hw
    simpa only [add_sub_cancel_left] using projection_le_spectralLogSumExp v z (z + w) (hb hmem) L
  have hop : ‖L‖ ≤ ψ / r := by
    apply ContinuousLinearMap.opNorm_le_bound L (div_nonneg hψ hr.le)
    intro w
    by_cases hw : w = 0
    · simp [hw]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let t := r / ‖w‖
    have ht : 0 ≤ t := div_nonneg hr.le hwpos.le
    have htmul : t * ‖w‖ = r := div_mul_cancel₀ _ hwpos.ne'
    have hn : ‖t • w‖ = r := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, htmul]
    have h₁ := hopen (t • w) hn.le
    have h₂ := hopen (-(t • w)) (by rw [norm_neg, hn])
    have hp : ‖L (t • w)‖ ≤ ψ := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by rwa [map_neg, neg_le] at h₂, h₁⟩
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hp
    have hm : r * ‖L w‖ ≤ ψ * ‖w‖ :=
      (div_le_iff₀ hwpos).mp (by simpa only [t, div_mul_eq_mul_div] using hp)
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm ‖L w‖ r] using hm)
  simpa only [mul_comm ‖L‖ r] using (le_div_iff₀ hr).mp hop

/-- The centered potential attains its global minimum at an interior point of the hull. -/
theorem exists_minimizer_spectralLogSumExp_of_mem_interior {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) (hz : z ∈ interior (convexHull ℝ (Set.range v))) :
    ∃ L : ℂ →L[ℝ] ℝ, ∀ K : ℂ →L[ℝ] ℝ, spectralLogSumExp v z L ≤ spectralLogSumExp v z K := by
  classical
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hball : Metric.closedBall z r ⊆ convexHull ℝ (Set.range v) :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hb
  let ψ := spectralLogSumExp v z
  have hbound (L : ℂ →L[ℝ] ℝ) : r * ‖L‖ ≤ ψ L :=
    mul_norm_le_spectralLogSumExp_of_closedBall v z r hr hball L
  have hcont : Continuous ψ := by
    have hs : Continuous (fun L : ℂ →L[ℝ] ℝ => ∑ j, Real.exp (L (v j - z))) :=
      continuous_finset_sum _ fun j _ =>
        Real.continuous_exp.comp ((ContinuousLinearMap.apply ℝ ℝ (v j - z)).continuous)
    exact hs.log (fun L => (Finset.sum_pos (fun j _ => Real.exp_pos (L (v j - z)))
      Finset.univ_nonempty).ne')
  letI : FiniteDimensional ℝ (ℂ →L[ℝ] ℝ) :=
    FiniteDimensional.of_injective (ContinuousLinearMap.coeLM ℝ) ContinuousLinearMap.coe_injective
  let R := (ψ 0 + 1) / r
  have hψ0 : 0 ≤ ψ 0 := by simpa only [norm_zero, mul_zero] using hbound 0
  have hR : 0 ≤ R := div_nonneg (by linarith only [hψ0]) hr.le
  have hzero : (0 : ℂ →L[ℝ] ℝ) ∈ Metric.closedBall 0 R := Metric.mem_closedBall_self hR
  obtain ⟨L, _, hL⟩ := (isCompact_closedBall (0 : ℂ →L[ℝ] ℝ) R).exists_isMinOn
    ⟨0, hzero⟩ hcont.continuousOn
  refine ⟨L, fun K => ?_⟩
  by_cases hK : K ∈ Metric.closedBall 0 R
  · exact hL hK
  · have hK' : R < ‖K‖ := lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hK)
    have he : R * r = ψ 0 + 1 := div_mul_cancel₀ _ hr.ne'
    have hlt := mul_lt_mul_of_pos_right hK' hr
    have hKψ := hbound K
    rw [he, mul_comm ‖K‖ r] at hlt
    exact (hL hzero).trans (by linarith only [hlt, hKψ])

/-- The positive weights of a finite exponential family. -/
def spectralSoftmax {J : Type*} [Fintype J]
    (v : J → ℂ) (z : ℂ) (L : ℂ →L[ℝ] ℝ) (j : J) : ℝ :=
  Real.exp (L (v j - z)) / ∑ k, Real.exp (L (v k - z))

private theorem spectralLogSumExp_stationary {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ K : ℂ →L[ℝ] ℝ, spectralLogSumExp v z L ≤ spectralLogSumExp v z K)
    (G : ℂ →L[ℝ] ℝ) : (∑ j, Real.exp (L (v j - z)) * G (v j - z)) = 0 := by
  let f (t : ℝ) : ℝ := ∑ j, Real.exp (L (v j - z) + t * G (v j - z))
  have hpos (t : ℝ) : 0 < f t := Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hm : IsMinOn f Set.univ 0 := by
    intro t _
    apply (Real.log_le_log_iff (hpos 0) (hpos t)).mp
    simpa only [spectralLogSumExp, f, zero_mul, add_zero, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] using hL (L + t • G)
  have hd (j : J) : HasDerivAt (fun t : ℝ => Real.exp (L (v j - z) + t * G (v j - z)))
      (Real.exp (L (v j - z)) * G (v j - z)) 0 := by
    simpa only [one_mul, zero_mul, add_zero] using
      (((hasDerivAt_id' (0 : ℝ)).mul_const (G (v j - z))).const_add (L (v j - z))).exp
  exact (hm.isLocalMin (by simp)).hasDerivAt_eq_zero
    (HasDerivAt.sum (u := Finset.univ) (fun j _ => hd j))

/-- At a minimum, the exponential weights are a positive probability law
with mean equal to the point used to center the potential. -/
theorem spectralSoftmax_probability_of_minimizer {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ K : ℂ →L[ℝ] ℝ, spectralLogSumExp v z L ≤ spectralLogSumExp v z K) :
    (∀ j, 0 < spectralSoftmax v z L j) ∧ (∑ j, spectralSoftmax v z L j) = 1 ∧
      (∑ j, spectralSoftmax v z L j • v j) = z := by
  have hp : 0 < ∑ j, Real.exp (L (v j - z)) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hmass : (∑ j, spectralSoftmax v z L j) = 1 := by
    unfold spectralSoftmax
    rw [← Finset.sum_div, div_self hp.ne']
  have hmean (G : ℂ →L[ℝ] ℝ) : (∑ j, spectralSoftmax v z L j * G (v j - z)) = 0 := by
    unfold spectralSoftmax
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, spectralLogSumExp_stationary v z L hL G, zero_div]
  have hc : (∑ j, spectralSoftmax v z L j • (v j - z)) = 0 := by
    apply Complex.ext
    · change (∑ j, spectralSoftmax v z L j • (v j - z)).re = (0 : ℂ).re
      simpa only [Complex.re_sum, Complex.smul_re, smul_eq_mul, Complex.zero_re] using hmean Complex.reCLM
    · change (∑ j, spectralSoftmax v z L j • (v j - z)).im = (0 : ℂ).im
      simpa only [Complex.im_sum, Complex.smul_im, smul_eq_mul, Complex.zero_im] using hmean Complex.imCLM
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hmass, one_smul] at hc
  exact ⟨fun _ => div_pos (Real.exp_pos _) hp, hmass, sub_eq_zero.mp hc⟩

/-- Every interior point has a strictly positive exponential-family representation. -/
theorem exists_spectralSoftmax_of_mem_interior {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) (hz : z ∈ interior (convexHull ℝ (Set.range v))) :
    ∃ L : ℂ →L[ℝ] ℝ, (∀ j, 0 < spectralSoftmax v z L j) ∧
      (∑ j, spectralSoftmax v z L j) = 1 ∧ (∑ j, spectralSoftmax v z L j • v j) = z := by
  obtain ⟨L, hL⟩ := exists_minimizer_spectralLogSumExp_of_mem_interior v z hz
  exact ⟨L, spectralSoftmax_probability_of_minimizer v z L hL⟩

/-- Shannon entropy of finitely many real weights, with the zero term defined by continuity. -/
def finiteShannonEntropy {J : Type*} [Fintype J] (p : J → ℝ) : ℝ :=
  -∑ j, p j * Real.log (p j)

private theorem log_density_comparison {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x - y ≤ x * Real.log x - x * Real.log y ∧
      (x ≠ y → x - y < x * Real.log x - x * Real.log y) := by
  by_cases hx0 : x = 0
  · subst x
    simp only [zero_sub, zero_mul, sub_zero]
    exact ⟨neg_nonpos.mpr hy.le, fun _ => neg_lt_zero.mpr hy⟩
  have hx' : 0 < x := lt_of_le_of_ne hx hx0.symm
  have he : x * (y / x - 1) = y - x := by
    rw [mul_sub, mul_comm x (y / x), div_mul_cancel₀ y hx0, mul_one]
  have hl : Real.log (y / x) = Real.log y - Real.log x := Real.log_div hy.ne' hx0
  constructor
  · have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hy hx')) hx
    rw [he, hl] at h
    linarith only [h]
  · intro hxy
    have hne : y / x ≠ 1 := by
      intro h
      exact hxy (by simpa only [one_mul] using ((div_eq_iff hx0).mp h).symm)
    have h := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (div_pos hy hx') hne) hx'
    rw [he, hl] at h
    linarith only [h]

/-- The exponential-family law at a minimum strictly maximizes entropy
against every distinct probability law with the same mean. -/
theorem finiteShannonEntropy_lt_spectralSoftmax_of_ne {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ K : ℂ →L[ℝ] ℝ, spectralLogSumExp v z L ≤ spectralLogSumExp v z K)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) (hpmean : ∑ j, p j • v j = z)
    (hpne : p ≠ spectralSoftmax v z L) :
    finiteShannonEntropy p < finiteShannonEntropy (spectralSoftmax v z L) := by
  let w := spectralSoftmax v z L
  let s := ∑ j, Real.exp (L (v j - z))
  have hs : 0 < s := Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  obtain ⟨hw, hwsum, hwmean⟩ := spectralSoftmax_probability_of_minimizer v z L hL
  have hwlog (j : J) : Real.log (w j) = L (v j - z) - Real.log s := by
    change Real.log (Real.exp (L (v j - z)) / s) = _
    rw [Real.log_div (Real.exp_ne_zero _) hs.ne', Real.log_exp]
  have hcross (q : J → ℝ) (hsum : ∑ j, q j = 1) (hmean : ∑ j, q j • v j = z) :
      (∑ j, q j * Real.log (w j)) = -Real.log s := by
    have hcenter : ∑ j, q j • (v j - z) = 0 := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul, hmean, sub_self]
    have hcenter' : ∑ j, q j * L (v j - z) = 0 := by
      simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using congrArg L hcenter
    simp_rw [hwlog, mul_sub, Finset.sum_sub_distrib, hcenter', ← Finset.sum_mul, hsum, one_mul, zero_sub]
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ w j := by
    by_contra! h
    exact hpne (funext h)
  have hsum : (∑ j, (p j - w j)) < ∑ j, (p j * Real.log (p j) - p j * Real.log (w j)) :=
    Finset.sum_lt_sum (fun i _ => (log_density_comparison (hp i) (hw i)).1)
      ⟨j, Finset.mem_univ j, (log_density_comparison (hp j) (hw j)).2 hj⟩
  rw [Finset.sum_sub_distrib, hpsum, hwsum, sub_self, Finset.sum_sub_distrib,
    hcross p hpsum hpmean, ← hcross w hwsum hwmean] at hsum
  exact neg_lt_neg (sub_pos.mp hsum)

private theorem exists_nonzero_centered_score {J : Type*} [Fintype J]
    (v : J → ℂ) (z : ℂ) (hz : z ∈ interior (convexHull ℝ (Set.range v)))
    (G : ℂ →L[ℝ] ℝ) (hG : G ≠ 0) : ∃ j, G (v j - z) ≠ 0 := by
  by_contra! h
  have hv (j : J) : G (v j) = G z := sub_eq_zero.mp (by simpa only [map_sub] using h j)
  have hzero (w : ℂ) (hw : w ∈ convexHull ℝ (Set.range v)) : G (w - z) = 0 := by
    obtain ⟨p, _, hp, hmean⟩ := (mem_complex_convexHull_iff_finite_probability v w).mp hw
    rw [map_sub, ← hmean, map_sum]
    simp only [map_smul, smul_eq_mul, hv, ← Finset.sum_mul, hp, one_mul, sub_self]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  apply hG
  apply ContinuousLinearMap.ext
  intro w
  change G w = 0
  let t := r / (2 * (‖w‖ + 1))
  have hd : 0 < 2 * (‖w‖ + 1) := by positivity
  have ht : 0 < t := div_pos hr hd
  have he : ‖t • w‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    change r / (2 * (‖w‖ + 1)) * ‖w‖ < r
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    exact mul_lt_mul_of_pos_left (by linarith only [norm_nonneg w]) hr
  have hmem : z + t • w ∈ Metric.ball z r := by
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using he
  have hval := hzero (z + t • w) (hball hmem)
  rw [add_sub_cancel_left, map_smul, smul_eq_mul] at hval
  exact (mul_eq_zero.mp hval).resolve_left ht.ne'

/-- The minimum exponential parameter is unique in the interior regime. -/
theorem existsUnique_minimizer_spectralLogSumExp_of_mem_interior {J : Type*}
    [Fintype J] [Nonempty J] (v : J → ℂ) (z : ℂ)
    (hz : z ∈ interior (convexHull ℝ (Set.range v))) :
    ∃! L : ℂ →L[ℝ] ℝ, ∀ K, spectralLogSumExp v z L ≤ spectralLogSumExp v z K := by
  obtain ⟨L, hL⟩ := exists_minimizer_spectralLogSumExp_of_mem_interior v z hz
  refine ⟨L, hL, ?_⟩
  intro K hK
  by_contra hne
  obtain ⟨j, hj⟩ := exists_nonzero_centered_score v z hz (K - L) (sub_ne_zero.mpr hne)
  have hj' : K (v j - z) ≠ L (v j - z) := by
    simpa only [ContinuousLinearMap.sub_apply, sub_ne_zero] using hj
  let P (A : ℂ →L[ℝ] ℝ) := ∑ i, Real.exp (A (v i - z))
  let a : ℝ := 1 / 2
  have hₐ : 0 < a := by norm_num [a]
  have h₂ : a + a = 1 := by norm_num [a]
  have hpos (A : ℂ →L[ℝ] ℝ) : 0 < P A :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hmon (A B : ℂ →L[ℝ] ℝ) (h : spectralLogSumExp v z A ≤ spectralLogSumExp v z B) :
      P A ≤ P B := (Real.log_le_log_iff (hpos A) (hpos B)).mp h
  have he : P K = P L := le_antisymm (hmon K L (hK L)) (hmon L K (hL K))
  have hmid : P (a • K + a • L) < a * P K + a * P L := by
    have hpoint (i : J) :
        Real.exp (a * K (v i - z) + a * L (v i - z)) ≤
          a * Real.exp (K (v i - z)) + a * Real.exp (L (v i - z)) := by
      exact convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) hₐ.le hₐ.le h₂
    have hstrict : Real.exp (a * K (v j - z) + a * L (v j - z)) <
        a * Real.exp (K (v j - z)) + a * Real.exp (L (v j - z)) :=
      strictConvexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) hj' hₐ hₐ h₂
    simpa only [P, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] using
      (Finset.sum_lt_sum (fun i _ => hpoint i) ⟨j, Finset.mem_univ j, hstrict⟩)
  rw [he, ← add_mul, h₂, one_mul] at hmid
  exact (not_lt_of_ge (hmon L _ (hL _))) hmid

/-- The centered covariance of positive weights is positive in every nonzero direction. -/
theorem centered_covariance_pos_of_mem_interior {J : Type*} [Fintype J]
    (v : J → ℂ) (z : ℂ) (hz : z ∈ interior (convexHull ℝ (Set.range v)))
    (w : J → ℝ) (hw : ∀ j, 0 < w j) (G : ℂ →L[ℝ] ℝ) (hG : G ≠ 0) :
    0 < ∑ j, w j * (G (v j - z)) ^ 2 := by
  obtain ⟨j, hj⟩ := exists_nonzero_centered_score v z hz G hG
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i).le (sq_nonneg _))
    ⟨j, Finset.mem_univ j, mul_pos (hw j) (sq_pos_of_ne_zero hj)⟩

end

end MOC

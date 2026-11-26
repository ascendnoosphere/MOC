import MOC.HalfPlaneSlope
import MOC.MatchingContactCurve
import MOC.NormalizedContactLimit

/-! A deficit projection on a regular anchored chart cannot remain in
the strict inactive-gap chamber over an entire right half-plane. -/

open BigOperators Filter Matrix MvPolynomial Set
open scoped Topology

namespace MOC

variable {n : ℕ}

/-- Neither a bounded nor a divergent matching profile can occur along
a holomorphic half-plane section with positive deficit and fixed contacts. -/
theorem no_holomorphic_deficit_halfPlane_section
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (hU : IsUnitary U)
    (η : ℂ) (hη : η ≠ 0) (r : ContactMatching n) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ → MatchingChartVariable n → ℂ)
    (hreg : ∀ w : ℂ, R < w.re → eval (z w) (matchingChartRegularPolynomial n) ≠ 0)
    (hdef : ∀ w : ℂ, R < w.re → η * eval (z w) (matchingChartDeficitPolynomial U r) = w)
    (hhol : ∀ σ : ContactMatching n, DifferentiableOn ℂ
      (fun w => chartMatchingGap η r (z w) σ) {w : ℂ | R < w.re})
    (hgap : ∀ σ : ContactMatching n,
      (∀ w : ℂ, R < w.re → 0 < (chartMatchingGap η r (z w) σ).re) ∨
      ∃ v : ℂ, v.re = 0 ∧ ∀ w : ℂ, R < w.re → chartMatchingGap η r (z w) σ = v) : False := by
  classical
  let x (k : ℕ) : ℝ := (k : ℝ) + 1
  let t (k : ℕ) : ℝ := x k + R
  let P (k : ℕ) (σ : ContactMatching n) : ℂ := (η / (t k : ℂ)) * matchingChartCoordinate (z (t k)) σ
  let T (k : ℕ) (i j : Fin (n + 2)) : ℂ :=
    matchingChartLeft (z (t k)) i * matchingChartRight (z (t k)) j
  have hx (k : ℕ) : 0 < x k := by dsimp only [x]; positivity
  have ht (k : ℕ) : 0 < t k := add_pos_of_pos_of_nonneg (hx k) hR
  have htR (k : ℕ) : R < (t k : ℂ).re := by
    rw [Complex.ofReal_re]
    exact lt_add_of_pos_left _ (hx k)
  have hxi : Tendsto x atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hti : Tendsto t atTop atTop := tendsto_atTop_add_const_right _ _ hxi
  have hi : Tendsto (fun k => ((t k : ℂ))⁻¹) atTop (𝓝 0) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_inv_atTop_zero.comp hti)
    change Tendsto (fun k => Complex.ofReal ((t k)⁻¹)) atTop (𝓝 (Complex.ofReal 0)) at h
    simpa only [Complex.ofReal_inv, Complex.ofReal_zero] using h
  have hratio : Tendsto (fun k => (x k : ℂ) / (t k : ℂ)) atTop (𝓝 1) := by
    have h := (tendsto_inv_atTop_zero.comp hxi).const_mul R
    rw [mul_zero] at h
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hd := hconst.add h
    rw [add_zero] at hd
    have hp := hd.inv₀ one_ne_zero
    rw [inv_one] at hp
    have h' := Complex.continuous_ofReal.continuousAt.tendsto.comp hp
    rw [Complex.ofReal_one] at h'
    refine h'.congr' (Filter.Eventually.of_forall fun k => ?_)
    change Complex.ofReal ((1 + R * (x k)⁻¹)⁻¹) = (x k : ℂ) / (t k : ℂ)
    rw [← Complex.ofReal_div]
    apply congrArg Complex.ofReal
    have he : (1 + R * (x k)⁻¹) * x k = t k := by
      dsimp only [t]
      field_simp [(hx k).ne'] <;> ring
    have hne : 1 + R * (x k)⁻¹ ≠ 0 := by
      intro hh
      rw [hh, zero_mul] at he
      exact (ht k).ne' he.symm
    rw [eq_div_iff (ht k).ne', ← he, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hdiff (k : ℕ) (σ : ContactMatching n) :
      P k r - P k σ = chartMatchingGap η r (z (t k)) σ / (t k : ℂ) := by
    dsimp only [P, chartMatchingGap]
    ring
  have hslope (σ : ContactMatching n) : ∃ L : ℝ, 0 ≤ L ∧
      Tendsto (fun k => P k r - P k σ) atTop (𝓝 (L : ℂ)) := by
    rcases hgap σ with hp | ⟨v, _, hv⟩
    · let f (w : ℂ) := chartMatchingGap η r (z (w + (R : ℂ))) σ
      have hf : DifferentiableOn ℂ f {w : ℂ | 0 < w.re} := by
        apply (hhol σ).comp (differentiable_id.add_const (R : ℂ)).differentiableOn
        intro w hw
        change R < (w + (R : ℂ)).re
        rw [Complex.add_re, Complex.ofReal_re]
        exact lt_add_of_pos_left _ hw
      have hfp (w : ℂ) (hw : 0 < w.re) : 0 < (f w).re := by
        apply hp
        rw [Complex.add_re, Complex.ofReal_re]
        exact lt_add_of_pos_left _ hw
      obtain ⟨L, hL, hlim⟩ := exists_real_slope_of_halfPlane_map f hf hfp
      refine ⟨L, hL, ?_⟩
      have h := hlim.mul hratio
      rw [mul_one] at h
      refine h.congr' (Filter.Eventually.of_forall fun k => ?_)
      change _ = P k r - P k σ
      rw [hdiff]
      change f (x k) / (x k : ℂ) * ((x k : ℂ) / (t k : ℂ)) =
        chartMatchingGap η r (z (t k)) σ / (t k : ℂ)
      have he : f (x k) = chartMatchingGap η r (z (t k)) σ := by
        simp only [f, t, Complex.ofReal_add]
      rw [he]
      have hn : (x k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hx k).ne'
      have ht' : (t k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ht k).ne'
      field_simp [hn, ht'] <;> ring
    · refine ⟨0, le_rfl, ?_⟩
      change Tendsto (fun k => P k r - P k σ) atTop (𝓝 (0 : ℂ))
      have h := hi.const_mul v
      rw [mul_zero] at h
      refine h.congr' (Filter.Eventually.of_forall fun k => ?_)
      change _ = P k r - P k σ
      rw [hdiff, hv _ (htR k), div_eq_mul_inv]
  choose c hc hlim using hslope
  have hcoord (k : ℕ) (σ : ContactMatching n) : P k σ =
      anchoredMatchingCoordinate ((η / (t k : ℂ)) * z (t k) (.inl ()))
        (matchingChartLeft (z (t k))) (matchingChartRight (z (t k))) σ := by
    simp only [P, matchingChartCoordinate, anchoredMatchingCoordinate, mul_assoc]
  have hactual (k : ℕ) : ∃ a b : Fin (n + 2) → ℂ, matchingProduct a b = P k := by
    obtain ⟨a, b, hab⟩ := exists_spectra_of_anchoredMatchingCoordinate
      ((η / (t k : ℂ)) * z (t k) (.inl ())) (matchingChartLeft (z (t k))) (matchingChartRight (z (t k)))
    exact ⟨a, b, funext fun σ => (hab σ).trans (hcoord k σ).symm⟩
  have hnz (k : ℕ) (σ : ContactMatching n) : P k σ ≠ 0 :=
    mul_ne_zero (div_ne_zero hη (Complex.ofReal_ne_zero.mpr (ht k).ne'))
      (((eval_matchingChartRegularPolynomial_ne_zero _).mp (hreg _ (htR k))).2.1 σ)
  have hsum (k : ℕ) : (∑ σ, signedWeight U σ * P k σ) = P k r + 1 := by
    have hv : η * ((∑ σ, signedWeight U σ * matchingChartCoordinate (z (t k)) σ) -
        matchingChartCoordinate (z (t k)) r) = (t k : ℂ) := by
      simpa only [matchingChartDeficitPolynomial, map_sub, map_sum, map_mul, eval_C,
        eval_matchingChartPolynomial] using hdef _ (htR k)
    have hd : (∑ σ, signedWeight U σ * P k σ) - P k r = 1 := by
      have he : (∑ σ, signedWeight U σ * P k σ) =
          (η / (t k : ℂ)) * ∑ σ, signedWeight U σ * matchingChartCoordinate (z (t k)) σ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by dsimp only [P]; ring
      rw [he]
      change _ * _ - (η / (t k : ℂ)) * _ = 1
      rw [← mul_sub, div_mul_eq_mul_div, hv,
        div_self (Complex.ofReal_ne_zero.mpr (ht k).ne')]
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hd)
  apply no_positive_deficit_on_anchored_profile_sequence U hU r P T c hactual hnz hsum hc hlim
  · intro k
    refine ⟨(η / (t k : ℂ)) * z (t k) (.inl ()), fun σ => ?_⟩
    exact hcoord k σ
  · intro i j
    obtain ⟨π, τ, h⟩ := exists_anchored_coordinate_ratio_labels 0 0 i j
    refine ⟨π, τ, fun k => ?_⟩
    rw [hcoord k π, hcoord k τ]
    apply h _ _ _ rfl rfl
    rw [← hcoord k τ]
    exact hnz k τ

end MOC

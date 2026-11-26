import MOC.TracialLogInverseSquare
import MOC.TracialLogResolvent
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The derivative of the traced operator logarithm on the positive
invertible cone. Subtract a fixed resolvent before integration. -/

open Filter MeasureTheory Set
open scoped Topology Interval

namespace MOC

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem isUnit_positive_shift (X : A) (hX : IsSelfAdjoint X)
    (hp : ∀ x ∈ spectrum ℝ X, 0 < x) {t : ℝ} (ht : 0 ≤ t) :
    IsUnit (X + algebraMap ℝ A t) :=
  (spectrum.zero_not_mem_iff ℝ).mp
    (fun hz => (lt_irrefl (0 : ℝ)) (positive_shift_spectrum_of_strict X hX hp t ht 0 hz))

private theorem shifted_inverse_eq_cfc (X : A) (hX : IsSelfAdjoint X)
    (hp : ∀ x ∈ spectrum ℝ X, 0 < x) {t : ℝ} (ht : 0 ≤ t) :
    Ring.inverse (X + algebraMap ℝ A t) = cfc (fun x : ℝ => (x + t)⁻¹) X := by
  let U := (isUnit_positive_shift X hX hp ht).unit
  have hU : (U : A) = X + algebraMap ℝ A t := (isUnit_positive_shift X hX hp ht).unit_spec
  have hsa : IsSelfAdjoint (U : A) :=
    hU.symm ▸ hX.add (IsSelfAdjoint.algebraMap A (.all t))
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) ((fun x : ℝ => x + t) '' spectrum ℝ X) := by
    apply continuousOn_inv₀.mono
    rintro _ ⟨x, hx, rfl⟩
    exact (add_pos_of_pos_of_nonneg (hp x hx) ht).ne'
  rw [cfc_comp' (fun x : ℝ => x⁻¹) (fun x : ℝ => x + t) X hcont (by fun_prop) hX,
    cfc_add_const t (fun x : ℝ => x) X (by fun_prop) hX, cfc_id',
    ← hU, Ring.inverse_unit, cfc_inv_id (R := ℝ) U hsa]

private theorem shifted_inverse_continuousOn (X : A) (hX : IsSelfAdjoint X)
    (hp : ∀ x ∈ spectrum ℝ X, 0 < x) :
    ContinuousOn (fun t : ℝ => Ring.inverse (X + algebraMap ℝ A t)) (Ioi 0) := by
  intro t ht
  obtain ⟨U, hU⟩ := isUnit_positive_shift X hX hp (mem_Ioi.mp ht).le
  have hc : ContinuousAt (fun r : ℝ => X + algebraMap ℝ A r) t :=
    (continuous_const.add (algebraMapCLM ℝ A).continuous).continuousAt
  have hi : ContinuousAt Ring.inverse (X + algebraMap ℝ A t) :=
    hU ▸ NormedRing.inverse_continuousAt U
  exact (hi.comp hc).continuousWithinAt

private theorem shifted_inverse_difference (X Y : A) (t : ℝ)
    (hX : IsUnit (X + algebraMap ℝ A t)) (hY : IsUnit (Y + algebraMap ℝ A t)) :
    Ring.inverse (X + algebraMap ℝ A t) - Ring.inverse (Y + algebraMap ℝ A t) =
      Ring.inverse (X + algebraMap ℝ A t) * (Y - X) * Ring.inverse (Y + algebraMap ℝ A t) := by
  let x := X + algebraMap ℝ A t
  let y := Y + algebraMap ℝ A t
  have hxy : Y - X = y - x := by dsimp only [x, y]; abel
  change Ring.inverse x - Ring.inverse y = Ring.inverse x * (Y - X) * Ring.inverse y
  rw [hxy, mul_sub, sub_mul, mul_assoc (Ring.inverse x) y, Ring.mul_inverse_cancel _ hY,
    mul_one, Ring.inverse_mul_cancel _ hX, one_mul]

private theorem trace_shifted_difference_integrable
    (τ : A →L[ℂ] ℂ) (X Y : A) (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y)
    {m : ℝ} (hm : 0 < m) (hx : ∀ x ∈ spectrum ℝ X, m ≤ x) (hy : ∀ y ∈ spectrum ℝ Y, m ≤ y) :
    IntegrableOn (fun t => tracedResolvent τ X t - tracedResolvent τ Y t) (Ioi 0) := by
  have hxp : ∀ x ∈ spectrum ℝ X, 0 < x := fun x hx₀ => hm.trans_le (hx x hx₀)
  have hyp : ∀ y ∈ spectrum ℝ Y, 0 < y := fun y hy₀ => hm.trans_le (hy y hy₀)
  have htrace (Z : A) (hZ : IsSelfAdjoint Z) (hz : ∀ z ∈ spectrum ℝ Z, 0 < z) :
      ContinuousOn (tracedResolvent τ Z) (Ioi 0) := by
    have hc := Complex.continuous_re.comp_continuousOn
      (τ.continuous.comp_continuousOn (shifted_inverse_continuousOn Z hZ hz))
    exact hc.congr fun t ht => by rw [shifted_inverse_eq_cfc Z hZ hz (mem_Ioi.mp ht).le]; rfl
  refine ((integrableOn_shifted_inv_sq m hm).const_mul (‖τ‖ * ‖Y - X‖)).mono
    ((htrace X hX hxp).sub (htrace Y hY hyp)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht₀ : 0 ≤ t := (mem_Ioi.mp ht).le
  let Rₓ := Ring.inverse (X + algebraMap ℝ A t)
  let Rᵧ := Ring.inverse (Y + algebraMap ℝ A t)
  have hxb : ‖Rₓ‖ ≤ (m + t)⁻¹ := by
    rw [Rₓ, shifted_inverse_eq_cfc X hX hxp ht₀]
    exact norm_shifted_inverse_le_of_spectral_gap X m t hm ht₀ hx
  have hyb : ‖Rᵧ‖ ≤ (m + t)⁻¹ := by
    rw [Rᵧ, shifted_inverse_eq_cfc Y hY hyp ht₀]
    exact norm_shifted_inverse_le_of_spectral_gap Y m t hm ht₀ hy
  have htrace_eq : tracedResolvent τ X t - tracedResolvent τ Y t = (τ (Rₓ - Rᵧ)).re := by
    rw [map_sub, Complex.sub_re, Rₓ, Rᵧ, shifted_inverse_eq_cfc X hX hxp ht₀,
      shifted_inverse_eq_cfc Y hY hyp ht₀] <;> rfl
  have hn : 0 ≤ (m + t)⁻¹ := inv_nonneg.mpr (add_nonneg hm.le ht₀)
  rw [htrace_eq, Real.norm_eq_abs, shifted_inverse_difference X Y t
    (isUnit_positive_shift X hX hxp ht₀) (isUnit_positive_shift Y hY hyp ht₀)]
  calc
    _ ≤ ‖τ (Rₓ * (Y - X) * Rᵧ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖τ‖ * ‖Rₓ * (Y - X) * Rᵧ‖ := τ.le_opNorm _
    _ ≤ ‖τ‖ * ((‖Rₓ‖ * ‖Y - X‖) * ‖Rᵧ‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg τ)
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg Rᵧ))
    _ ≤ ‖τ‖ * (((m + t)⁻¹ * ‖Y - X‖) * (m + t)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg τ)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hxb (norm_nonneg _)) hyb
        (norm_nonneg _) (mul_nonneg hn (norm_nonneg _))
    _ = ‖(‖τ‖ * ‖Y - X‖) * ((m + t)⁻¹)^2‖ := by
      rw [Real.norm_of_nonneg (by positivity)]
      ring

private theorem shifted_trace_remainder_tendsto_zero [Nontrivial A]
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (X : A) (hX : IsSelfAdjoint X) (hx : ∀ x ∈ spectrum ℝ X, 0 < x) :
    Tendsto (fun R : ℝ => (τ (CFC.log (X + algebraMap ℝ A R))).re - Real.log R)
      atTop (𝓝 0) := by
  have hr : ∀ᶠ R : ℝ in atTop, 0 < R := eventually_gt_atTop 0
  refine squeeze_zero' (hr.mono fun R hR => sub_nonneg.mpr
    (trace_shifted_log_bounds τ hτ X hX hx R hR).1) ?_ ?_
  · filter_upwards [hr] with R hR
    have h₁ := (trace_shifted_log_bounds τ hτ X hX hx R hR).2
    have hnorm : 0 < ‖X‖ + R := add_pos_of_nonneg_of_pos (norm_nonneg X) hR
    have h₂ := Real.log_le_sub_one_of_pos (div_pos hnorm hR)
    rw [Real.log_div hnorm.ne' hR.ne', add_div, div_self hR.ne', add_sub_cancel_right] at h₂
    exact (sub_le_sub_right h₁ _).trans h₂
  · simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul ‖X‖

private theorem integral_traced_resolvent_sub [Nontrivial A]
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (X Y : A) (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y)
    {m : ℝ} (hm : 0 < m) (hx : ∀ x ∈ spectrum ℝ X, m ≤ x) (hy : ∀ y ∈ spectrum ℝ Y, m ≤ y) :
    (∫ t in Ioi (0 : ℝ), tracedResolvent τ X t - tracedResolvent τ Y t) =
      (τ (CFC.log Y)).re - (τ (CFC.log X)).re := by
  have hxp : ∀ x ∈ spectrum ℝ X, 0 < x := fun x hx₀ => hm.trans_le (hx x hx₀)
  have hyp : ∀ y ∈ spectrum ℝ Y, 0 < y := fun y hy₀ => hm.trans_le (hy y hy₀)
  have hi := trace_shifted_difference_integrable τ X Y hX hY hm hx hy
  have hlimit := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi
    (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  apply tendsto_nhds_unique hlimit
  have h := ((shifted_trace_remainder_tendsto_zero τ hτ X hX hxp).sub
    (shifted_trace_remainder_tendsto_zero τ hτ Y hY hyp)).add_const
      ((τ (CFC.log Y)).re - (τ (CFC.log X)).re)
  simp only [sub_self, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  obtain ⟨hiX, hvX⟩ := traced_resolvent_interval τ X hX hxp R hR
  obtain ⟨hiY, hvY⟩ := traced_resolvent_interval τ Y hY hyp R hR
  rw [intervalIntegral.integral_of_le hR.le, ← integral_subtype_comap measurableSet_Ioc,
    integral_sub hiX hiY, hvX, hvY]
  ring

/-- Along a continuously differentiable path of strictly positive
operators, the traced log has the cyclic inverse derivative. -/
theorem tracial_log_hasDerivAt (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (X : ℝ → A) (s : ℝ) (H : A) (hX : HasDerivAt X H s) (hC : ContDiff ℝ 1 X)
    (hpositive : ∀ᶠ u in 𝓝 s, IsSelfAdjoint (X u) ∧
      ∃ m : ℝ, 0 < m ∧ algebraMap ℝ A m ≤ X u) :
    HasDerivAt (fun u => (τ (CFC.log (X u))).re) (τ (H * Ring.inverse (X s))).re s := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · letI := hA
    have hone : (1 : A) = 0 := Subsingleton.elim _ _
    have hf := hτ.one
    rw [hone, map_zero] at hf
    exact (zero_ne_one hf).elim
  letI := hA
  obtain ⟨hsa, c, hc, hcX⟩ := hpositive.self_of_nhds
  let m := c / 2
  have hm : 0 < m := half_pos hc
  have hc₂ : c = m + m := by dsimp only [m]; ring
  have hclose : ∀ᶠ u in 𝓝 s, ‖X u - X s‖ < m := by
    have hn : ContinuousAt (fun u => ‖X u - X s‖) s :=
      (hC.continuous.sub continuous_const).norm.continuousAt
    have he : Tendsto (fun u => ‖X u - X s‖) (𝓝 s) (𝓝 0) := by
      simpa only [sub_self, norm_zero] using hn
    exact he.eventually (gt_mem_nhds hm)
  let B := ‖deriv X s‖ + 1
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) zero_le_one
  have hD : ∀ᶠ u in 𝓝 s, ‖deriv X u‖ < B := by
    have h := ((hC.continuous_deriv le_rfl).norm.continuousAt :
      Tendsto (fun u => ‖deriv X u‖) (𝓝 s) (𝓝 ‖deriv X s‖))
    exact h.eventually (gt_mem_nhds (lt_add_one _))
  have hgap : ∀ᶠ u in 𝓝 s,
      IsSelfAdjoint (X u) ∧ (∀ x ∈ spectrum ℝ (X u), m ≤ x) ∧ ‖deriv X u‖ ≤ B := by
    filter_upwards [hpositive, hclose, hD] with u hu huclose huD
    have hneg : -(algebraMap ℝ A m) ≤ X u - X s := by
      have hmap : algebraMap ℝ A ‖X u - X s‖ ≤ algebraMap ℝ A m := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        exact smul_le_smul_of_nonneg_right huclose.le zero_le_one
      exact (neg_le_neg hmap).trans (hu.1.sub hsa).neg_algebraMap_norm_le_self
    have huX : algebraMap ℝ A m ≤ X u := by
      have hle := add_le_add hcX hneg
      rw [hc₂, map_add, add_neg_cancel_right] at hle
      convert hle using 1 <;> abel
    exact ⟨hu.1, (algebraMap_le_iff_le_spectrum hu.1).mp huX, huD.le⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hgap
  have hpos (u : ℝ) (hu : u ∈ Metric.ball s ε) :
      ∀ x ∈ spectrum ℝ (X u), 0 < x := fun x hx => hm.trans_le ((hball u hu).2.1 x hx)
  have hs : s ∈ Metric.ball s ε := Metric.mem_ball_self hε
  let R (u t : ℝ) : A := Ring.inverse (X u + algebraMap ℝ A t)
  let F (u t : ℝ) : ℝ := (τ (R s t)).re - (τ (R u t)).re
  let D (u t : ℝ) : ℝ := (τ (deriv X u * (R u t)^2)).re
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hRcont (u : ℝ) (hu : u ∈ Metric.ball s ε) : ContinuousOn (R u) (Ioi 0) :=
    shifted_inverse_continuousOn (X u) (hball u hu).1 (hpos u hu)
  have hMeas : ∀ᶠ u in 𝓝 s, AEStronglyMeasurable (F u) μ := by
    filter_upwards [Metric.ball_mem_nhds s hε] with u hu
    have hcont : ContinuousOn (F u) (Ioi 0) :=
      (Complex.continuous_re.comp_continuousOn (τ.continuous.comp_continuousOn (hRcont s hs))).sub
        (Complex.continuous_re.comp_continuousOn (τ.continuous.comp_continuousOn (hRcont u hu)))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hi : Integrable (F s) μ := by
    simpa only [F, sub_self] using integrable_zero ℝ ℝ μ
  have hdMeas : AEStronglyMeasurable (D s) μ := by
    have hcont : ContinuousOn (D s) (Ioi 0) :=
      Complex.continuous_re.comp_continuousOn (τ.continuous.comp_continuousOn
        (continuousOn_const.mul ((hRcont s hs).pow 2)))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  let bound (t : ℝ) := (‖τ‖ * B) * ((m + t)⁻¹)^2
  have hbint : Integrable bound μ := (integrableOn_shifted_inv_sq m hm).const_mul (‖τ‖ * B)
  have hbound : ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball s ε, ‖D u t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht u hu
    have ht₀ : 0 ≤ t := (mem_Ioi.mp ht).le
    have hRn : ‖R u t‖ ≤ (m + t)⁻¹ := by
      rw [R, shifted_inverse_eq_cfc (X u) (hball u hu).1 (hpos u hu) ht₀]
      exact norm_shifted_inverse_le_of_spectral_gap (X u) m t hm ht₀ (hball u hu).2.1
    obtain ⟨U, hU⟩ := isUnit_positive_shift (X u) (hball u hu).1 (hpos u hu) ht₀
    have hRU : R u t = (↑U⁻¹ : A) := by rw [R, ← hU, Ring.inverse_unit]
    rw [D, Real.norm_eq_abs, hRU]
    calc
      _ ≤ ‖τ‖ * ‖deriv X u‖ * ‖(↑U⁻¹ : A)‖^2 :=
        norm_traced_inverse_square τ (deriv X u) U
      _ ≤ bound t := by
        rw [← hRU, bound]
        have hleft := mul_le_mul_of_nonneg_left (hball u hu).2.2 (norm_nonneg τ)
        have hright := pow_le_pow_left₀ (norm_nonneg _) hRn 2
        exact mul_le_mul hleft hright (sq_nonneg _) (mul_nonneg (norm_nonneg τ) hB)
  have hdiff : ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball s ε, HasDerivAt (F · t) (D u t) u := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht u hu
    have ht₀ : 0 ≤ t := (mem_Ioi.mp ht).le
    obtain ⟨U, hU⟩ := isUnit_positive_shift (X u) (hball u hu).1 (hpos u hu) ht₀
    have hg : HasDerivAt (fun a => X a + algebraMap ℝ A t) (deriv X u) u :=
      ((hC.differentiable le_rfl u).hasDerivAt).add_const _
    have hr := traced_ring_inverse_hasDerivAt τ hτ _ _ u U hU hg
    have he : R u t = (↑U⁻¹ : A) := by rw [R, ← hU, Ring.inverse_unit]
    rw [D, he]
    simpa only [F, neg_neg, R] using hr.const_sub ((τ (R s t)).re)
  have hInt := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hε hMeas hi hdMeas hbound hbint hdiff).2
  have hinter : (∫ t, D s t ∂μ) = (τ (H * Ring.inverse (X s))).re := by
    let L : A →L[ℝ] ℝ := Complex.reCLM.comp ((τ.restrictScalars ℝ).comp
      (ContinuousLinearMap.mulLeftRight ℝ A H 1))
    let G (t : ℝ) : A := cfc (fun x : ℝ => ((x + t)⁻¹)^2) (X s)
    have hGi : Integrable G μ := integrableOn_cfc_shifted_inv_sq (X s) hsa (hpos s hs)
    have hGval : (∫ t, G t ∂μ) = Ring.inverse (X s) :=
      integral_Ioi_cfc_shifted_inv_sq (X s) hsa (hpos s hs)
    calc
      _ = ∫ t, L (G t) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
        have hp := hpos s hs
        have ht₀ : 0 ≤ t := (mem_Ioi.mp ht).le
        have hg : ContinuousOn (fun x : ℝ => (x + t)⁻¹) (spectrum ℝ (X s)) :=
          (continuous_id.add continuous_const).continuousOn.inv₀
            (fun x hx => (add_pos_of_pos_of_nonneg (hp x hx) ht₀).ne')
        have hpow : G t = (R s t)^2 := by
          dsimp only [G, R]
          rw [cfc_pow _ 2 _ hg hsa, shifted_inverse_eq_cfc (X s) hsa hp ht₀]
        rw [hpow, D, hX.deriv]
        simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
          mul_one, ContinuousLinearMap.coe_restrictScalars', Complex.reCLM_apply]
      _ = L (∫ t, G t ∂μ) := L.integral_comp_comm hGi
      _ = _ := by
        rw [hGval]
        simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
          mul_one, ContinuousLinearMap.coe_restrictScalars', Complex.reCLM_apply]
  rw [hinter] at hInt
  apply (hInt.add_const ((τ (CFC.log (X s))).re)).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds s hε] with u hu
  have he : (∫ t, F u t ∂μ) = (τ (CFC.log (X u))).re - (τ (CFC.log (X s))).re := by
    rw [← integral_traced_resolvent_sub τ hτ (X s) (X u) hsa (hball u hu).1 hm
      (hball s hs).2.1 (hball u hu).2.1]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have ht₀ : 0 ≤ t := (mem_Ioi.mp ht).le
    simp only [F, R, tracedResolvent, shifted_inverse_eq_cfc (X s) hsa (hpos s hs) ht₀,
      shifted_inverse_eq_cfc (X u) (hball u hu).1 (hpos u hu) ht₀]
  rw [he, sub_add_cancel]

end

end MOC

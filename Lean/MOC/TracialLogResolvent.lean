import MOC.FugledeKadisonRegularization
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic.FieldSimp

/-! The traced operator logarithm is monotone on strictly positive
operators. The proof integrates inverses on a finite interval. -/

open MeasureTheory
open scoped Interval

namespace MOC

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private def resolventIntervalMeasure (R : ℝ) : Measure (Set.Ioc 0 R) :=
  Measure.comap Subtype.val volume

private theorem finite_resolventIntervalMeasure (R : ℝ) :
    IsFiniteMeasure (resolventIntervalMeasure R) := by
  have he : Subtype.val '' (Set.univ : Set (Set.Ioc (0 : ℝ) R)) = Set.Ioc 0 R := by
    ext x
    exact ⟨fun ⟨t, _, ht⟩ => ht ▸ t.property, fun hx => ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩⟩
  refine ⟨?_⟩
  rw [resolventIntervalMeasure,
    (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply, he, Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top

private theorem finite_scalar_resolvent_integral (x R : ℝ) (hx : 0 < x) (hR : 0 < R) :
    (∫ t : Set.Ioc 0 R, (x + t.val)⁻¹ ∂resolventIntervalMeasure R) =
      Real.log (x + R) - Real.log x := by
  rw [resolventIntervalMeasure, integral_subtype_comap measurableSet_Ioc (fun t : ℝ => (x + t)⁻¹),
    ← intervalIntegral.integral_of_le hR.le]
  have h := intervalIntegral.integral_comp_add_left (a := 0) (b := R)
    (fun s : ℝ => s⁻¹) x
  change (∫ t in 0..R, (x + t)⁻¹) = _ at h
  rw [add_zero, integral_inv_of_pos hx (add_pos hx hR),
    Real.log_div (add_pos hx hR).ne' hx.ne'] at h
  exact h

private theorem cfc_shift_on_positive_spectrum (X : A) (hX : IsSelfAdjoint X)
    (hXp : ∀ x ∈ spectrum ℝ X, 0 < x) (t : ℝ) (ht : 0 ≤ t)
    (f : ℝ → ℝ) (hf : ContinuousOn f ({0}ᶜ : Set ℝ)) :
    cfc (fun x : ℝ => f (x + t)) X = cfc f (X + algebraMap ℝ A t) := by
  have hcont : ContinuousOn f ((fun x : ℝ => x + t) '' spectrum ℝ X) := by
    apply hf.mono
    rintro _ ⟨x, hx, rfl⟩
    exact (add_pos_of_pos_of_nonneg (hXp x hx) ht).ne'
  rw [cfc_comp' f (fun x : ℝ => x + t) X hcont (by fun_prop) hX,
    cfc_add_const t (fun x : ℝ => x) X (by fun_prop) hX, cfc_id']

private def tracedResolvent (τ : A →L[ℂ] ℂ) (X : A) (t : ℝ) : ℝ :=
  (τ (cfc (fun x : ℝ => (x + t)⁻¹) X)).re

private theorem traced_resolvent_interval [Nontrivial A]
    (τ : A →L[ℂ] ℂ) (X : A) (hX : IsSelfAdjoint X)
    (hXp : ∀ x ∈ spectrum ℝ X, 0 < x) (R : ℝ) (hR : 0 < R) :
    Integrable (fun t : Set.Ioc 0 R => tracedResolvent τ X t.val) (resolventIntervalMeasure R) ∧
      (∫ t : Set.Ioc 0 R, tracedResolvent τ X t.val ∂resolventIntervalMeasure R) =
        (τ (CFC.log (X + algebraMap ℝ A R))).re - (τ (CFC.log X)).re := by
  let μ := resolventIntervalMeasure R
  letI : IsFiniteMeasure μ := finite_resolventIntervalMeasure R
  have hcompact : IsCompact (spectrum ℝ X) := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨m, hm, hmin⟩ := hcompact.exists_isMinOn hX.spectrum_nonempty continuousOn_id
  have hm₀ := hXp m hm
  have hpos (t : Set.Ioc 0 R) (x : spectrum ℝ X) : 0 < x.val + t.val :=
    add_pos (hXp x.val x.property) t.property.1
  have hcont : Continuous
      (fun p : Set.Ioc (0 : ℝ) R × spectrum ℝ X => (p.2.val + p.1.val)⁻¹) :=
    ((continuous_subtype_val.comp continuous_snd).add
      (continuous_subtype_val.comp continuous_fst)).inv₀
      (fun p => (hpos p.1 p.2).ne')
  let F (t : Set.Ioc 0 R) : C(spectrum ℝ X, ℝ) :=
    ⟨fun x => (x.val + t.val)⁻¹, hcont.uncurry_left t⟩
  have hF : Continuous F :=
    (ContinuousMap.curry (⟨_, hcont⟩ :
      C(Set.Ioc (0 : ℝ) R × spectrum ℝ X, ℝ))).continuous
  have hnorm (t : Set.Ioc (0 : ℝ) R) : ‖F t‖ ≤ ‖m⁻¹‖ := by
    rw [ContinuousMap.norm_le _ (norm_nonneg _)]
    intro x
    change ‖(x.val + t.val)⁻¹‖ ≤ ‖m⁻¹‖
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (hpos t x).le),
      Real.norm_of_nonneg (inv_nonneg.mpr hm₀.le)]
    exact (inv_le_inv₀ (hpos t x) hm₀).mpr
      ((show m ≤ x.val from hmin x.property).trans (le_add_of_nonneg_right t.property.1.le))
  have hFi : Integrable F μ :=
    ⟨hF.aestronglyMeasurable, (hasFiniteIntegral_const m⁻¹).mono (.of_forall hnorm)⟩
  let L : C(spectrum ℝ X, ℝ) →L[ℝ] ℝ :=
    Complex.reCLM.comp ((τ.restrictScalars ℝ).comp (cfcL hX))
  have hres (t : Set.Ioc 0 R) : L (F t) = tracedResolvent τ X t.val := by
    have hcont' : ContinuousOn (fun x : ℝ => (x + t.val)⁻¹) (spectrum ℝ X) :=
      (continuous_id.add continuous_const).continuousOn.inv₀ fun x hx =>
        (hpos t ⟨x, hx⟩).ne'
    unfold tracedResolvent
    rw [cfc_apply _ X hX hcont']
    rfl
  have hcont₀ : ContinuousOn Real.log (spectrum ℝ X) :=
    Real.continuousOn_log.mono fun x hx => (hXp x hx).ne'
  have hcont₁ : ContinuousOn (fun x : ℝ => Real.log (x + R)) (spectrum ℝ X) := by
    apply Real.continuousOn_log.comp (continuous_id.add continuous_const).continuousOn
    exact fun x hx => (add_pos (hXp x hx) hR).ne'
  let G₀ : C(spectrum ℝ X, ℝ) := ⟨_, hcont₀.restrict⟩
  let G₁ : C(spectrum ℝ X, ℝ) := ⟨_, hcont₁.restrict⟩
  have hvalues : (∫ t, F t ∂μ) = G₁ - G₀ := by
    ext x
    rw [ContinuousMap.integral_apply hFi]
    exact finite_scalar_resolvent_integral x.val R (hXp x.val x.property) hR
  have h₀ : L G₀ = (τ (CFC.log X)).re := by
    rw [CFC.log, cfc_apply _ X hX hcont₀]
    rfl
  have h₁ : L G₁ = (τ (CFC.log (X + algebraMap ℝ A R))).re := by
    unfold CFC.log
    rw [← cfc_shift_on_positive_spectrum X hX hXp R hR.le Real.log Real.continuousOn_log,
      cfc_apply _ X hX hcont₁]
    rfl
  constructor
  · simpa only [hres] using L.integrable_comp hFi
  · have hi := L.integral_comp_comm hFi
    rw [hvalues, map_sub, h₀, h₁] at hi
    simpa only [hres] using hi

private theorem positive_shift_spectrum_of_strict (X : A) (hX : IsSelfAdjoint X)
    (hXp : ∀ x ∈ spectrum ℝ X, 0 < x) (t : ℝ) (ht : 0 ≤ t) :
    ∀ x ∈ spectrum ℝ (X + algebraMap ℝ A t), 0 < x := by
  have he : cfc (fun x : ℝ => x + t) X = X + algebraMap ℝ A t := by
    rw [cfc_add_const t (fun x : ℝ => x) X (by fun_prop) hX, cfc_id']
  intro x hx
  rw [← he, cfc_map_spectrum (f := fun z : ℝ => z + t) hX (by fun_prop)] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  exact add_pos_of_pos_of_nonneg (hXp z hz) ht

private theorem trace_mono_of_positive (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    {U V : A} (h : U ≤ V) : (τ U).re ≤ (τ V).re := by
  have ht := hτ.positive (V - U) (sub_nonneg.mpr h)
  rw [map_sub, Complex.sub_re] at ht
  exact sub_nonneg.mp ht

private theorem traced_resolvent_antitone (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (X Y : A) (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y)
    (hXp : ∀ x ∈ spectrum ℝ X, 0 < x) (hYp : ∀ x ∈ spectrum ℝ Y, 0 < x)
    (hXY : X ≤ Y) (t : ℝ) (ht : 0 ≤ t) :
    tracedResolvent τ Y t ≤ tracedResolvent τ X t := by
  have hXs := positive_shift_spectrum_of_strict X hX hXp t ht
  have hYs := positive_shift_spectrum_of_strict Y hY hYp t ht
  obtain ⟨U, hU⟩ : IsUnit (X + algebraMap ℝ A t) :=
    (spectrum.zero_not_mem_iff ℝ).mp fun h => (lt_irrefl (0 : ℝ)) (hXs 0 h)
  obtain ⟨V, hV⟩ : IsUnit (Y + algebraMap ℝ A t) :=
    (spectrum.zero_not_mem_iff ℝ).mp fun h => (lt_irrefl (0 : ℝ)) (hYs 0 h)
  have hXsa : IsSelfAdjoint (X + algebraMap ℝ A t) :=
    hX.add (IsSelfAdjoint.algebraMap A (.all t))
  have hYsa : IsSelfAdjoint (Y + algebraMap ℝ A t) :=
    hY.add (IsSelfAdjoint.algebraMap A (.all t))
  have hUn : 0 ≤ (U : A) := by
    rw [hU]
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg _ hXsa).mpr (fun s hs => (hXs s hs).le)
  have hUV : (U : A) ≤ V := by
    rw [hU, hV]
    exact add_le_add_right hXY _
  have heX : cfc (fun x : ℝ => (x + t)⁻¹) X = (↑U⁻¹ : A) := by
    rw [cfc_shift_on_positive_spectrum X hX hXp t ht (fun x : ℝ => x⁻¹) continuousOn_inv₀,
      ← hU, cfc_inv_id (R := ℝ) U (hU.symm ▸ hXsa)]
  have heY : cfc (fun x : ℝ => (x + t)⁻¹) Y = (↑V⁻¹ : A) := by
    rw [cfc_shift_on_positive_spectrum Y hY hYp t ht (fun x : ℝ => x⁻¹) continuousOn_inv₀,
      ← hV, cfc_inv_id (R := ℝ) V (hV.symm ▸ hYsa)]
  change (τ (cfc (fun x : ℝ => (x + t)⁻¹) Y)).re ≤
    (τ (cfc (fun x : ℝ => (x + t)⁻¹) X)).re
  rw [heX, heY]
  exact trace_mono_of_positive τ hτ (CStarAlgebra.inv_le_inv hUn hUV)

private theorem trace_shifted_log_bounds [Nontrivial A]
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (X : A) (hX : IsSelfAdjoint X) (hXp : ∀ x ∈ spectrum ℝ X, 0 < x)
    (R : ℝ) (hR : 0 < R) :
    Real.log R ≤ (τ (CFC.log (X + algebraMap ℝ A R))).re ∧
      (τ (CFC.log (X + algebraMap ℝ A R))).re ≤ Real.log (‖X‖ + R) := by
  have hcont : ContinuousOn (fun x : ℝ => Real.log (x + R)) (spectrum ℝ X) := by
    apply Real.continuousOn_log.comp (continuous_id.add continuous_const).continuousOn
    exact fun x hx => (add_pos (hXp x hx) hR).ne'
  have hval (c : ℝ) : (τ (cfc (fun _ : ℝ => c) X)).re = c := by
    rw [cfc_const c X hX, Algebra.algebraMap_eq_smul_one,
      RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, hτ.one, smul_eq_mul, mul_one,
      Complex.ofReal_re]
  unfold CFC.log
  rw [← cfc_shift_on_positive_spectrum X hX hXp R hR.le Real.log Real.continuousOn_log]
  constructor
  · rw [← hval (Real.log R)]
    apply trace_mono_of_positive τ hτ
    exact cfc_mono (a := X) (fun x hx =>
      Real.log_le_log hR (le_add_of_nonneg_left (hXp x hx).le)) continuousOn_const hcont
  · rw [← hval (Real.log (‖X‖ + R))]
    apply trace_mono_of_positive τ hτ
    exact cfc_mono (a := X) (fun x hx => Real.log_le_log (add_pos (hXp x hx) hR)
      (add_le_add_right ((Real.le_norm_self x).trans (spectrum.norm_le_norm_of_mem hx)) R))
      hcont continuousOn_const

/-- The trace of the operator logarithm is monotone on self-adjoint
operators with strictly positive real spectra. -/
theorem tracial_log_mono (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (X Y : A) (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y)
    (hXp : ∀ x ∈ spectrum ℝ X, 0 < x) (hYp : ∀ x ∈ spectrum ℝ Y, 0 < x)
    (hXY : X ≤ Y) :
    (τ (CFC.log X)).re ≤ (τ (CFC.log Y)).re := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · letI := hA
    rw [Subsingleton.elim (CFC.log X) (CFC.log Y)]
  letI := hA
  by_contra! hfail
  let d := (τ (CFC.log X)).re - (τ (CFC.log Y)).re
  have hd : 0 < d := sub_pos.mpr hfail
  let R := (‖X‖ + 1) / d
  have hR : 0 < R := div_pos (add_pos_of_nonneg_of_pos (norm_nonneg X) zero_lt_one) hd
  obtain ⟨hiX, hvX⟩ := traced_resolvent_interval τ X hX hXp R hR
  obtain ⟨hiY, hvY⟩ := traced_resolvent_interval τ Y hY hYp R hR
  have hi := integral_mono hiY hiX (fun t : Set.Ioc (0 : ℝ) R =>
    traced_resolvent_antitone τ hτ X Y hX hY hXp hYp hXY t.val t.property.1.le)
  rw [hvY, hvX] at hi
  have hlo := (trace_shifted_log_bounds τ hτ Y hY hYp R hR).1
  have hhi := (trace_shifted_log_bounds τ hτ X hX hXp R hR).2
  have hgap : d ≤ Real.log (‖X‖ + R) - Real.log R := by
    dsimp only [d]
    linarith only [hi, hlo, hhi]
  have hXR : 0 < ‖X‖ + R := add_pos_of_nonneg_of_pos (norm_nonneg X) hR
  have hratio := Real.log_le_sub_one_of_pos (div_pos hXR hR)
  rw [Real.log_div hXR.ne' hR.ne', add_div, div_self hR.ne', add_sub_cancel_right] at hratio
  have hdR : d * R = ‖X‖ + 1 := by
    dsimp only [R]
    rw [mul_div_assoc, mul_comm d, mul_div_cancel_right₀ _ hd.ne']
  have hsmall : ‖X‖ / R < d := by
    rw [div_lt_iff₀ hR, hdR]
    linarith
  exact (not_lt_of_ge (hgap.trans hratio)) hsmall

/-- For positive left and right scaling, the strictly positive
conjugation identity is sufficient for the analytic determinant. -/
theorem fugledeKadisonLog_mul_of_strict_conjugation
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ) (L T : A) (hL : IsSelfAdjoint L)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hmL : algebraMap ℝ A m ≤ L * L) (hML : L * L ≤ algebraMap ℝ A M)
    (hconj : ∀ U : A, IsSelfAdjoint U → (∀ x ∈ spectrum ℝ U, 0 < x) →
      (τ (CFC.log (L * U * L))).re =
        2 * (τ (CFC.log L)).re + (τ (CFC.log U)).re) :
    fugledeKadisonLog τ (T * L) = fugledeKadisonLog τ T + ((τ (CFC.log L)).re : EReal) ∧
      fugledeKadisonLog τ (L * T) = fugledeKadisonLog τ T + ((τ (CFC.log L)).re : EReal) :=
  fugledeKadisonLog_mul_of_invertible_trace_log τ hτ L T hL m M hm hM hmL hML
    (tracial_log_mono τ hτ) hconj

/-- The traced inverse has the cyclic inverse-square derivative along
a differentiable path through an invertible operator. -/
theorem traced_ring_inverse_hasDerivAt
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (X : ℝ → A) (H : A) (s : ℝ) (U : Aˣ)
    (hU : (U : A) = X s) (hX : HasDerivAt X H s) :
    HasDerivAt (fun t => (τ (Ring.inverse (X t))).re)
      (-(τ (H * (↑U⁻¹ : A) ^ 2)).re) s := by
  let L : A →L[ℝ] ℝ := Complex.reCLM.comp (τ.restrictScalars ℝ)
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) U).comp_hasDerivAt_of_eq s hX hU
  have htrace := L.hasFDerivAt.comp_hasDerivAt s h
  have he : τ ((↑U⁻¹ : A) * H * (↑U⁻¹ : A)) = τ (H * (↑U⁻¹ : A) ^ 2) := by
    rw [mul_assoc, hτ.cyclic (↑U⁻¹ : A) (H * (↑U⁻¹ : A)), mul_assoc, pow_two]
  simpa only [L, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', Complex.reCLM_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    map_neg, Complex.neg_re, he] using htrace

/-- The norm bound on the cyclic inverse-square derivative. -/
theorem norm_traced_inverse_square (τ : A →L[ℂ] ℂ) (H : A) (U : Aˣ) :
    |(τ (H * (↑U⁻¹ : A) ^ 2)).re| ≤ ‖τ‖ * ‖H‖ * ‖(↑U⁻¹ : A)‖ ^ 2 := by
  calc
    _ ≤ ‖τ (H * (↑U⁻¹ : A) ^ 2)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖τ‖ * ‖H * (↑U⁻¹ : A) ^ 2‖ := τ.le_opNorm _
    _ ≤ ‖τ‖ * (‖H‖ * ‖(↑U⁻¹ : A)‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg τ)
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (norm_pow_le' _ (by decide : 0 < (2 : ℕ))) (norm_nonneg H))
    _ = _ := (mul_assoc _ _ _).symm

/-- A uniform positive spectral gap gives reciprocal decay of the
shifted inverse. -/
theorem norm_shifted_inverse_le_of_spectral_gap (X : A) (m t : ℝ)
    (hm : 0 < m) (ht : 0 ≤ t) (hX : ∀ x ∈ spectrum ℝ X, m ≤ x) :
    ‖cfc (fun x : ℝ => (x + t)⁻¹) X‖ ≤ (m + t)⁻¹ := by
  have hmt : 0 < m + t := add_pos_of_pos_of_nonneg hm ht
  apply norm_cfc_le (inv_nonneg.mpr hmt.le)
  intro x hx
  have hle : m + t ≤ x + t := add_le_add_right (hX x hx) _
  have hx₀ := hmt.trans_le hle
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hx₀.le)]
  exact (inv_le_inv₀ hx₀ hmt).mpr hle

/-! Prove the strict trace-log conjugation identity used by
`fugledeKadisonLog_mul_of_strict_conjugation`. Differentiate the
resolvent difference under the improper integral. Use the inverse
square bound to justify the derivative. -/

end

end MOC

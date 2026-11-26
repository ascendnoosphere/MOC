import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic.Linarith

/-! The regularized analytic trace logarithm and its trace upper bound. -/

namespace MOC

open MeasureTheory
open scoped CompactlySupported

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A normalized, positive and cyclic complex linear trace. -/
structure IsNormalizedTracialState (τ : A →L[ℂ] ℂ) : Prop where
  one : τ 1 = 1
  positive : ∀ x : A, 0 ≤ x → 0 ≤ (τ x).re
  cyclic : ∀ x y : A, τ (x * y) = τ (y * x)

/-- The analytic logarithm of the Fuglede–Kadison determinant, expressed
through the continuous regularizations of the logarithm of the Gram operator. -/
def fugledeKadisonLog (τ : A →L[ℂ] ℂ) (T : A) : EReal :=
  ⨅ ε : Set.Ioi (0 : ℝ),
    (((τ (cfc (fun t : ℝ => Real.log (t + ε.val)) (star T * T))).re / 2 : ℝ) : EReal)

private theorem trace_re_real_smul (τ : A →L[ℂ] ℂ) (r : ℝ) (X : A) :
    (τ (r • X)).re = r * (τ X).re := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, smul_eq_mul,
    Complex.re_ofReal_mul]

private theorem IsNormalizedTracialState.mono_re {τ : A →L[ℂ] ℂ}
    (hτ : IsNormalizedTracialState τ) {X Y : A} (h : X ≤ Y) :
    (τ X).re ≤ (τ Y).re := by
  have hh := hτ.positive (Y - X) (sub_nonneg.mpr h)
  rw [map_sub, Complex.sub_re] at hh
  exact sub_nonneg.mp hh

private def tracialSpectrumFunctional (τ : A →L[ℂ] ℂ) (X : A)
    (hX : IsSelfAdjoint X) : C_c(spectrum ℝ X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (τ (cfcHom hX f.toContinuousMap)).re
  map_add' f g := by
    have h : (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap := by
      ext x
      rfl
    change (τ (cfcHom hX (f + g).toContinuousMap)).re = _
    rw [h, map_add, map_add, Complex.add_re]
  map_smul' r f := by
    have h : (r • f).toContinuousMap = r • f.toContinuousMap := by
      ext x
      rfl
    change (τ (cfcHom hX (r • f).toContinuousMap)).re =
      r * (τ (cfcHom hX f.toContinuousMap)).re
    rw [h, map_smul, trace_re_real_smul]

private theorem tracialSpectrumFunctional_nonneg (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (X : A) (hX : IsSelfAdjoint X) :
    ∀ f, 0 ≤ f → 0 ≤ tracialSpectrumFunctional τ X hX f := by
  intro f hf
  apply hτ.positive
  have he : (0 : C(spectrum ℝ X, ℝ)) ≤ f.toContinuousMap := fun x => hf x
  have hm := cfcHom_mono hX he
  simpa only [map_zero] using hm

/-- The scalar spectral measure obtained by applying a tracial state to
the real continuous functional calculus of a self-adjoint operator. -/
def tracialSpectralMeasure (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (X : A) (hX : IsSelfAdjoint X) : Measure (spectrum ℝ X) :=
  RealRMK.rieszMeasure (tracialSpectrumFunctional_nonneg τ hτ X hX)

/-- Integration of a continuous function against the scalar spectral
measure agrees with the trace of the continuous functional calculus. -/
theorem integral_tracialSpectralMeasure (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (X : A) (hX : IsSelfAdjoint X)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ X)) :
    (∫ x : spectrum ℝ X, f x.val ∂tracialSpectralMeasure τ hτ X hX) =
      (τ (cfc f X)).re := by
  let F : C(spectrum ℝ X, ℝ) := ⟨_, hf.restrict⟩
  let g : C_c(spectrum ℝ X, ℝ) := CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported F
  change (∫ x, g x ∂tracialSpectralMeasure τ hτ X hX) = _
  unfold tracialSpectralMeasure
  rw [RealRMK.integral_rieszMeasure, cfc_apply f X hX hf]
  rfl

/-- The spectral measure of a normalized trace has total mass one. -/
theorem tracialSpectralMeasure_univ (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (X : A) (hX : IsSelfAdjoint X) :
    tracialSpectralMeasure τ hτ X hX Set.univ = 1 := by
  have h := integral_tracialSpectralMeasure τ hτ X hX (fun _ => 1) continuousOn_const
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def, cfc_const 1 X hX,
    map_one, hτ.one, Complex.one_re] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

/-- The Gram spectral measure gives the regularized integral formula
for the analytic trace logarithm. -/
theorem fugledeKadisonLog_eq_inf_spectral_integrals (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (T : A) :
    fugledeKadisonLog τ T =
      ⨅ ε : Set.Ioi (0 : ℝ),
        (((∫ x : spectrum ℝ (star T * T), Real.log (x.val + ε.val)
          ∂tracialSpectralMeasure τ hτ (star T * T) (IsSelfAdjoint.star_mul_self T)) / 2 : ℝ)
          : EReal) := by
  unfold fugledeKadisonLog
  congr 1
  funext ε
  rw [integral_tracialSpectralMeasure]
  apply Real.continuousOn_log.comp (continuous_id.add continuous_const).continuousOn
  intro t ht
  exact (add_pos_of_nonneg_of_pos (spectrum_star_mul_self_nonneg t ht) ε.property).ne'

/-- A scalar supporting line for logarithm gives the normalized trace
bound for continuous logarithmic regularization. -/
theorem tracial_regularized_log_le (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (X : A) (hX : 0 ≤ X)
    (ε : ℝ) (hε : 0 < ε) :
    (τ (cfc (fun t : ℝ => Real.log (t + ε)) X)).re ≤
      Real.log ((τ X).re + ε) := by
  let m := (τ X).re
  let c := m + ε
  have hc : 0 < c := add_pos_of_nonneg_of_pos (hτ.positive X hX) hε
  let k := Real.log c - c⁻¹ * m
  have hlog : ContinuousOn (fun t : ℝ => Real.log (t + ε)) (spectrum ℝ X) := by
    apply Real.continuousOn_log.comp (continuous_id.add continuous_const).continuousOn
    intro t ht
    exact (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hX ht) hε).ne'
  have hscalar (t : ℝ) (ht : t ∈ spectrum ℝ X) :
      Real.log (t + ε) ≤ k + c⁻¹ * t := by
    have htε := add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hX ht) hε
    have h := Real.log_le_sub_one_of_pos (div_pos htε hc)
    rw [Real.log_div htε.ne' hc.ne', div_eq_mul_inv] at h
    have hinv : c⁻¹ * (m + ε) = 1 := inv_mul_cancel₀ hc.ne'
    dsimp only [k]
    nlinarith only [h, hinv]
  have hoperator := cfc_mono (a := X) hscalar hlog
    (show ContinuousOn (fun t : ℝ => k + c⁻¹ * t) (spectrum ℝ X) from by fun_prop)
  have h := hτ.mono_re hoperator
  rw [cfc_const_add k (fun t : ℝ => c⁻¹ * t) X (by fun_prop) hX.isSelfAdjoint,
    cfc_const_mul_id c⁻¹ X hX.isSelfAdjoint, Algebra.algebraMap_eq_smul_one,
    map_add, Complex.add_re, trace_re_real_smul, trace_re_real_smul,
    hτ.one, Complex.one_re, mul_one] at h
  change _ ≤ Real.log c
  simpa only [k, sub_add_cancel, m] using h

/-- A positive upper bound for the trace of the Gram operator bounds the
analytic logarithm, even when that logarithm has value minus infinity. -/
theorem fugledeKadisonLog_le_log_trace_bound (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (T : A) (u : ℝ) (hu : 0 < u)
    (hT : (τ (star T * T)).re ≤ u) :
    fugledeKadisonLog τ T ≤ (Real.log u / 2 : ℝ) := by
  apply le_of_forall_gt_imp_ge_of_dense
  rw [EReal.forall]
  refine ⟨fun h => (not_lt_of_ge bot_le h).elim, fun _ => le_top, ?_⟩
  intro b hb
  have hbr := EReal.coe_lt_coe_iff.mp hb
  have hlt : u < Real.exp (2 * b) := by
    rw [← Real.exp_log hu, Real.exp_lt_exp]
    linarith only [hbr]
  let ε := Real.exp (2 * b) - u
  have hε : 0 < ε := sub_pos.mpr hlt
  have hlog := tracial_regularized_log_le τ hτ (star T * T)
    (star_mul_self_nonneg T) ε hε
  have hmu : 0 < (τ (star T * T)).re + ε :=
    add_pos_of_nonneg_of_pos (hτ.positive _ (star_mul_self_nonneg T)) hε
  have hsum : (τ (star T * T)).re + ε ≤ Real.exp (2 * b) := by
    dsimp only [ε]
    linarith only [hT]
  have hbound := hlog.trans (Real.log_le_log hmu hsum)
  rw [Real.log_exp] at hbound
  refine (iInf_le _ (⟨ε, hε⟩ : Set.Ioi (0 : ℝ))).trans (EReal.coe_le_coe_iff.mpr ?_)
  linarith only [hbound]

/-- A Gram operator of zero trace gives analytic logarithm minus infinity. -/
theorem fugledeKadisonLog_eq_bot_of_gram_trace_eq_zero (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (T : A) (hT : (τ (star T * T)).re = 0) :
    fugledeKadisonLog τ T = ⊥ := by
  apply le_antisymm _ bot_le
  apply le_of_forall_gt_imp_ge_of_dense
  rw [EReal.forall]
  refine ⟨fun h => (lt_irrefl _ h).elim, fun _ => le_top, ?_⟩
  intro b _
  have h := fugledeKadisonLog_le_log_trace_bound τ hτ T (Real.exp (2 * b))
    (Real.exp_pos _) (by rw [hT]; exact (Real.exp_pos _).le)
  rw [Real.log_exp] at h
  exact h.trans (EReal.coe_le_coe_iff.mpr (by linarith))

end

end MOC

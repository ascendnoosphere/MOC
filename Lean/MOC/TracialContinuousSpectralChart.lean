import MOC.TracialLogConjugation
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Tactic.Ring

/-! Tracial measures and finite sums of products from continuous spectral charts.
For a normal element, the continuous functional calculus on its complex
spectrum supplies the chart. -/

open MeasureTheory
open scoped BigOperators CompactlySupported CStarAlgebra

namespace MOC

noncomputable section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {A : Type*} [CStarAlgebra A]

/-- Regard a real continuous function as a complex continuous function. -/
def continuousMapOfReal : C(X, ℝ) →ₐ[ℝ] C(X, ℂ) :=
  Complex.ofRealAm.compLeftContinuous ℝ Complex.continuous_ofReal

@[simp]
theorem continuousMapOfReal_apply (f : C(X, ℝ)) (x : X) :
    continuousMapOfReal f x = (f x : ℂ) := rfl

/-- A real function is self-adjoint in the complex function algebra. -/
theorem continuousMapOfReal_selfAdjoint (f : C(X, ℝ)) :
    IsSelfAdjoint (continuousMapOfReal f) := by
  change star (continuousMapOfReal f) = continuousMapOfReal f
  apply ContinuousMap.ext
  intro x
  change star (f x : ℂ) = (f x : ℂ)
  rw [Complex.star_def, Complex.conj_ofReal]

/-- A chart sends a nonnegative real function to a nonnegative operator. -/
theorem continuousSpectralChart_nonneg [PartialOrder A] [StarOrderedRing A]
    (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ φ (continuousMapOfReal f) := by
  let g : C(X, ℝ) := ⟨fun x => Real.sqrt (f x), Real.continuous_sqrt.comp f.continuous⟩
  have hg : star (continuousMapOfReal g) * continuousMapOfReal g = continuousMapOfReal f := by
    rw [(continuousMapOfReal_selfAdjoint g).star_eq]
    apply ContinuousMap.ext
    intro x
    change (Real.sqrt (f x) : ℂ) * (Real.sqrt (f x) : ℂ) = (f x : ℂ)
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hf x)]
  rw [← hg, map_mul, map_star]
  exact star_mul_self_nonneg _

variable [CompactSpace X]

/-- A unital complex star algebra homomorphism is norm contractive. -/
theorem continuousSpectralChart_norm_le (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (f : C(X, ℂ)) :
    ‖φ f‖ ≤ ‖f‖ :=
  NonUnitalStarAlgHom.norm_apply_le φ f

/-- A chart preserves the sup norm bound for a real continuous function. -/
theorem continuousSpectralChart_norm_le_real (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (f : C(X, ℝ)) :
    ‖φ (continuousMapOfReal f)‖ ≤ ‖f‖ := by
  refine (continuousSpectralChart_norm_le φ _).trans ?_
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  rw [continuousMapOfReal_apply, Complex.norm_real]
  exact ContinuousMap.norm_coe_le_norm f x

section Measure

variable [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable [PartialOrder A] [StarOrderedRing A]

private def continuousSpectralFunctional (τ : A →L[ℂ] ℂ)
    (φ : C(X, ℂ) →⋆ₐ[ℂ] A) : C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (τ (φ (continuousMapOfReal f.toContinuousMap))).re
  map_add' f g := by
    have h : (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap :=
      ContinuousMap.ext fun _ => rfl
    change (τ (φ (continuousMapOfReal (f + g).toContinuousMap))).re = _
    simp only [h, map_add, Complex.add_re]
  map_smul' r f := by
    have h : (r • f).toContinuousMap = r • f.toContinuousMap :=
      ContinuousMap.ext fun _ => rfl
    change ((τ.restrictScalars ℝ) ((φ.restrictScalars ℝ)
      (continuousMapOfReal (r • f).toContinuousMap))).re =
      r • ((τ.restrictScalars ℝ) ((φ.restrictScalars ℝ)
        (continuousMapOfReal f.toContinuousMap))).re
    simp only [h, map_smul, Complex.smul_re]

private theorem continuousSpectralFunctional_nonneg (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (φ : C(X, ℂ) →⋆ₐ[ℂ] A) :
    ∀ f, 0 ≤ f → 0 ≤ continuousSpectralFunctional τ φ f :=
  fun f hf => hτ.positive _ (continuousSpectralChart_nonneg φ f.toContinuousMap fun x => hf x)

/-- The trace of a chart defines a measure on the chart space. -/
def continuousSpectralMeasure (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (φ : C(X, ℂ) →⋆ₐ[ℂ] A) : Measure X :=
  RealRMK.rieszMeasure (continuousSpectralFunctional_nonneg τ hτ φ)

/-- Integration against the chart measure gives the real part of the trace. -/
theorem integral_continuousSpectralMeasure (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (f : C(X, ℝ)) :
    (∫ x, f x ∂continuousSpectralMeasure τ hτ φ) = (τ (φ (continuousMapOfReal f))).re := by
  let g : C_c(X, ℝ) := CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported f
  change (∫ x, g x ∂continuousSpectralMeasure τ hτ φ) = _
  exact RealRMK.integral_rieszMeasure (continuousSpectralFunctional_nonneg τ hτ φ) g

/-- The measure of a normalized trace has total mass one. -/
theorem continuousSpectralMeasure_univ (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (φ : C(X, ℂ) →⋆ₐ[ℂ] A) :
    continuousSpectralMeasure τ hτ φ Set.univ = 1 := by
  have h := integral_continuousSpectralMeasure τ hτ φ (1 : C(X, ℝ))
  change (∫ _ : X, (1 : ℝ) ∂continuousSpectralMeasure τ hτ φ) = _ at h
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
    map_one, hτ.one, Complex.one_re] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

instance continuousSpectralMeasure_isProbabilityMeasure (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (φ : C(X, ℂ) →⋆ₐ[ℂ] A) :
    IsProbabilityMeasure (continuousSpectralMeasure τ hτ φ) :=
  ⟨continuousSpectralMeasure_univ τ hτ φ⟩

end Measure

/-- The complex continuous factor with value `exp (-u x / 2)` at `x`. -/
def continuousPotentialFactor (u : C(X, ℝ)) : C(X, ℂ) :=
  continuousMapOfReal ⟨fun x => Real.exp (-u x / 2),
    Real.continuous_exp.comp (u.continuous.neg.div_const 2)⟩

@[simp]
theorem continuousPotentialFactor_apply (u : C(X, ℝ)) (x : X) :
    continuousPotentialFactor u x = (Real.exp (-u x / 2) : ℂ) := rfl

private theorem continuousPotentialFactor_eq_exp (u : C(X, ℝ)) :
    continuousPotentialFactor u = NormedSpace.exp ℂ (continuousMapOfReal ((-(1 / 2) : ℝ) • u)) := by
  rw [NormedSpace.exp_continuousMap_eq]
  apply ContinuousMap.ext
  intro x
  change (Real.exp (-u x / 2) : ℂ) = NormedSpace.exp ℂ (((-(1 / 2) : ℝ) * u x : ℝ) : ℂ)
  rw [← NormedSpace.of_real_exp_ℝ_ℝ, ← Real.exp_eq_exp_ℝ]
  rw [show (-(1 / 2) : ℝ) * u x = -u x / 2 by ring]

private theorem continuousPotentialFactor_spectrum_pos (φ : C(X, ℂ) →⋆ₐ[ℂ] A)
    (u : C(X, ℝ)) : ∀ x ∈ spectrum ℝ (φ (continuousPotentialFactor u)), 0 < x := by
  intro x hx
  have hx' := AlgHom.spectrum_apply_subset (φ.restrictScalars ℝ) (continuousPotentialFactor u) hx
  rw [ContinuousMap.spectrum_eq_preimage_range] at hx'
  obtain ⟨y, hy⟩ := hx'
  change (Real.exp (-u y / 2) : ℂ) = (x : ℂ) at hy
  have h : Real.exp (-u y / 2) = x := Complex.ofReal_injective hy
  rw [← h]
  exact Real.exp_pos _

section Scale

variable [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable [PartialOrder A] [StarOrderedRing A]

/-- Multiplication by a chart's potential factor adds the integral of
the scaled potential to the determinant logarithm. -/
theorem fugledeKadisonLog_mul_continuousPotential (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (u : C(X, ℝ)) (T : A) :
    let L := φ (continuousPotentialFactor u)
    let c := -(∫ x, u x ∂continuousSpectralMeasure τ hτ φ) / 2
    fugledeKadisonLog τ (T * L) = fugledeKadisonLog τ T + (c : EReal) ∧
      fugledeKadisonLog τ (L * T) = fugledeKadisonLog τ T + (c : EReal) := by
  let L := φ (continuousPotentialFactor u)
  let v : C(X, ℝ) := (-(1 / 2) : ℝ) • u
  have hL : IsSelfAdjoint L := (continuousMapOfReal_selfAdjoint _).map φ
  have hv : IsSelfAdjoint (φ (continuousMapOfReal v)) := (continuousMapOfReal_selfAdjoint v).map φ
  have hlog : CFC.log L = φ (continuousMapOfReal v) := by
    rw [show L = φ (continuousPotentialFactor u) from rfl, continuousPotentialFactor_eq_exp,
      NormedSpace.map_exp ℂ φ (map_continuous φ), NormedSpace.exp_eq_exp ℂ ℝ A]
    exact CFC.log_exp _ hv
  have htrace : (τ (CFC.log L)).re = -(∫ x, u x ∂continuousSpectralMeasure τ hτ φ) / 2 := by
    rw [hlog, ← integral_continuousSpectralMeasure τ hτ φ v]
    change (∫ x, (-(1 / 2) : ℝ) • u x ∂continuousSpectralMeasure τ hτ φ) = _
    rw [integral_smul, smul_eq_mul]
    ring
  have h := fugledeKadisonLog_mul_of_strict_positive τ hτ L T hL
    (continuousPotentialFactor_spectrum_pos φ u)
  simpa only [htrace] using h

end Scale

variable {ι : Type*} [Fintype ι]

/-- Evaluate a finite sum of products in chart order. -/
def tracialContinuousKernel (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (ψ : C(Y, ℂ) →⋆ₐ[ℂ] A)
    (f : ι → C(X, ℂ)) (g : ι → C(Y, ℂ)) : A :=
  ∑ r, φ (f r) * ψ (g r)

/-- Multiplying the chart functions on each side gives the corresponding
left and right products in the target algebra. -/
theorem tracialContinuousKernel_scale (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (ψ : C(Y, ℂ) →⋆ₐ[ℂ] A)
    (f : ι → C(X, ℂ)) (g : ι → C(Y, ℂ)) (l : C(X, ℂ)) (r : C(Y, ℂ)) :
    φ l * tracialContinuousKernel φ ψ f g * ψ r =
      tracialContinuousKernel φ ψ (fun i => l * f i) (fun i => g i * r) := by
  unfold tracialContinuousKernel
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul, mul_assoc]

variable [CompactSpace Y] [T2Space X] [T2Space Y]
variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
variable [PartialOrder A] [StarOrderedRing A]

/-- Scaling the two chart functions by the potential factors adds the two
potential integrals, each multiplied by minus one half. -/
theorem fugledeKadisonLog_tracialContinuousKernel_scale (τ : A →L[ℂ] ℂ)
    (hτ : IsNormalizedTracialState τ) (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (ψ : C(Y, ℂ) →⋆ₐ[ℂ] A)
    (f : ι → C(X, ℂ)) (g : ι → C(Y, ℂ)) (u : C(X, ℝ)) (v : C(Y, ℝ)) :
    fugledeKadisonLog τ (tracialContinuousKernel φ ψ
      (fun i => continuousPotentialFactor u * f i) (fun i => g i * continuousPotentialFactor v)) =
      fugledeKadisonLog τ (tracialContinuousKernel φ ψ f g) +
        ((-(∫ x, u x ∂continuousSpectralMeasure τ hτ φ) / 2 : ℝ) : EReal) +
        ((-(∫ y, v y ∂continuousSpectralMeasure τ hτ ψ) / 2 : ℝ) : EReal) := by
  let T := tracialContinuousKernel φ ψ f g
  let L := φ (continuousPotentialFactor u)
  rw [← tracialContinuousKernel_scale φ ψ f g (continuousPotentialFactor u) (continuousPotentialFactor v)]
  rw [(fugledeKadisonLog_mul_continuousPotential τ hτ ψ v (L * T)).1,
    (fugledeKadisonLog_mul_continuousPotential τ hτ φ u T).2]

end

end MOC

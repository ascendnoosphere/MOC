import MOC.CompactTransportDuality
import MOC.CompactTransportLimit
import MOC.TracialContinuousKernel
import Mathlib.Data.Matrix.Notation

/-! Fuglede–Kadison transport for continuous finite-rank spectral kernels. -/

open BigOperators MeasureTheory Set
open scoped CStarAlgebra

namespace MOC

noncomputable section

variable {A X Y ρ : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Fintype ρ]

private theorem continuousKernelFunction_potential
    (f : ρ → C(X, ℂ)) (g : ρ → C(Y, ℂ)) (u : C(X, ℝ)) (v : C(Y, ℝ)) (p : X × Y) :
    continuousKernelFunction (fun r => continuousPotentialFactor u * f r)
      (fun r => g r * continuousPotentialFactor v) p =
      (continuousPotentialFactor u p.1) * continuousKernelFunction f g p *
        (continuousPotentialFactor v p.2) := by
  simp only [continuousKernelFunction_apply, ContinuousMap.mul_apply, Finset.mul_sum, Finset.sum_mul,
    mul_assoc]

/-- Any continuous additive majorant of a log truncation bounds the log determinant. -/
theorem fugledeKadisonLog_continuousKernel_le_potential
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (ψ : C(Y, ℂ) →⋆ₐ[ℂ] A)
    (f : ρ → C(X, ℂ)) (g : ρ → C(Y, ℂ)) (n : ℕ)
    (u : C(X, ℝ)) (v : C(Y, ℝ))
    (huv : ∀ p, compactLogTruncation (continuousKernelFunction f g) n p ≤ u p.1 + v p.2)
    (a : ℝ) (ha : (a : EReal) ≤ fugledeKadisonLog τ (tracialContinuousKernel φ ψ f g)) :
    a ≤ (∫ x, u x ∂continuousSpectralMeasure τ hτ φ) +
      ∫ y, v y ∂continuousSpectralMeasure τ hτ ψ := by
  let u₂ : C(X, ℝ) := (2 : ℝ) • u
  let v₂ : C(Y, ℝ) := (2 : ℝ) • v
  let f' (r : ρ) := continuousPotentialFactor u₂ * f r
  let g' (r : ρ) := g r * continuousPotentialFactor v₂
  let T := tracialContinuousKernel φ ψ f' g'
  have hnorm (p : X × Y) :
      Complex.normSq (continuousKernelFunction f' g' p) ≤ 1 := by
    have h := (Real.log_le_iff_le_exp
      (lt_of_lt_of_le (Real.exp_pos (-(n : ℝ))) (le_max_left _ _))).mp (huv p)
    have hn : ‖continuousKernelFunction f g p‖ ≤ Real.exp (u p.1 + v p.2) :=
      (le_max_right _ _).trans h
    have hf' : continuousPotentialFactor u₂ p.1 = (Real.exp (-u p.1) : ℂ) := by
      change ((Real.exp (-(2 * u p.1) / 2) : ℝ) : ℂ) = _
      congr 2
      ring
    have hg' : continuousPotentialFactor v₂ p.2 = (Real.exp (-v p.2) : ℂ) := by
      change ((Real.exp (-(2 * v p.2) / 2) : ℝ) : ℂ) = _
      congr 2
      ring
    have hscaled : ‖continuousKernelFunction f' g' p‖ ≤ 1 := by
      rw [f', g', continuousKernelFunction_potential, hf', hg', norm_mul, norm_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ (Real.exp (-u p.1) * Real.exp (u p.1 + v p.2)) * Real.exp (-v p.2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le) (Real.exp_pos _).le
        _ = 1 := by
          rw [← Real.exp_add, ← Real.exp_add, show -u p.1 + (u p.1 + v p.2) + -v p.2 = 0 by ring,
            Real.exp_zero]
    rw [Complex.normSq_eq_norm_sq]
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hscaled 2
  have hgram : (τ (star T * T)).re ≤ 1 :=
    tracialContinuousKernel_gram_trace_le τ hτ φ ψ f' g' 1 hnorm
  have hnonpos : fugledeKadisonLog τ T ≤ 0 := by
    simpa only [Real.log_one, zero_div, EReal.coe_zero] using
      fugledeKadisonLog_le_log_trace_bound τ hτ T 1 zero_lt_one hgram
  let c := -(∫ x, u₂ x ∂continuousSpectralMeasure τ hτ φ) / 2
  let d := -(∫ y, v₂ y ∂continuousSpectralMeasure τ hτ ψ) / 2
  have hscale : fugledeKadisonLog τ T =
      fugledeKadisonLog τ (tracialContinuousKernel φ ψ f g) + (c : EReal) + (d : EReal) :=
    fugledeKadisonLog_tracialContinuousKernel_scale τ hτ φ ψ f g u₂ v₂
  have hle : ((a + c + d : ℝ) : EReal) ≤ fugledeKadisonLog τ T := by
    rw [hscale, EReal.coe_add, EReal.coe_add]
    exact add_le_add_right (add_le_add_right ha _) _
  have hreal : a + c + d ≤ 0 := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [EReal.coe_zero] using hle.trans hnonpos
  have huc : c = -(∫ x, u x ∂continuousSpectralMeasure τ hτ φ) := by
    simp only [c, u₂, ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
    ring
  have hvd : d = -(∫ y, v y ∂continuousSpectralMeasure τ hτ ψ) := by
    simp only [d, v₂, ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
    ring
  rw [huc, hvd] at hreal
  linarith only [hreal]

/-- A single compact transport functional attains every truncation
bound for a finite lower bound of the determinant logarithm. -/
theorem exists_continuous_kernel_transport_functional
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (ψ : C(Y, ℂ) →⋆ₐ[ℂ] A)
    (f : ρ → C(X, ℂ)) (g : ρ → C(Y, ℂ)) (a : ℝ)
    (ha : (a : EReal) ≤ fugledeKadisonLog τ (tracialContinuousKernel φ ψ f g)) :
    let μ := continuousSpectralMeasure τ hτ φ
    let ν := continuousSpectralMeasure τ hτ ψ
    ∃ L, IsCompactTransportFunctional (compactTransportIntegral μ) (compactTransportIntegral ν) L ∧
      ∀ n, a ≤ L (compactLogTruncation (continuousKernelFunction f g) n) := by
  let μ := continuousSpectralMeasure τ hτ φ
  let ν := continuousSpectralMeasure τ hτ ψ
  letI : IsProbabilityMeasure μ := ⟨continuousSpectralMeasure_univ τ hτ φ⟩
  letI : IsProbabilityMeasure ν := ⟨continuousSpectralMeasure_univ τ hτ ψ⟩
  let k := continuousKernelFunction f g
  change ∃ L, IsCompactTransportFunctional (compactTransportIntegral μ) (compactTransportIntegral ν) L ∧
    ∀ n, a ≤ L (compactLogTruncation k n)
  refine exists_common_compact_transport_functional _ _ _ (compactLogTruncation_antitone k) a ?_
  intro n
  obtain ⟨L, hp, h1, hx, hy, hb⟩ := exists_compact_transport_functional
    (compactTransportIntegral μ) (compactTransportIntegral ν)
    (compactTransportIntegral_nonneg μ) (compactTransportIntegral_nonneg ν)
    (compactTransportIntegral_one μ) (compactTransportIntegral_one ν) (compactLogTruncation k n) a
    (fun u v huv => fugledeKadisonLog_continuousKernel_le_potential τ hτ φ ψ f g n u v huv a ha)
  exact ⟨L, ⟨hp, h1, hx, hy⟩, hb⟩

/-- A probability coupling has the two specified pushforward measures. -/
def IsSpectralTransportCoupling (μ : Measure X) (ν : Measure Y) (γ : Measure (X × Y)) : Prop :=
  γ univ = 1 ∧ γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν

/-- One probability coupling attains or exceeds each finite lower
bound for the continuous kernel determinant. -/
theorem exists_continuous_kernel_transport_coupling
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (ψ : C(Y, ℂ) →⋆ₐ[ℂ] A)
    (f : ρ → C(X, ℂ)) (g : ρ → C(Y, ℂ)) (a : ℝ)
    (ha : (a : EReal) ≤ fugledeKadisonLog τ (tracialContinuousKernel φ ψ f g)) :
    ∃ γ, IsSpectralTransportCoupling (continuousSpectralMeasure τ hτ φ)
      (continuousSpectralMeasure τ hτ ψ) γ ∧
      (a : EReal) ≤ compactLogModulusIntegral (continuousKernelFunction f g) γ := by
  let μ := continuousSpectralMeasure τ hτ φ
  let ν := continuousSpectralMeasure τ hτ ψ
  obtain ⟨L, hL, hcost⟩ := exists_continuous_kernel_transport_functional τ hτ φ ψ f g a ha
  let γ := compactTransportMeasure L hL.1
  have hγ : IsSpectralTransportCoupling μ ν γ :=
    compactTransportMeasure_marginals _ _ L hL μ ν
      (compactTransportIntegral_apply μ) (compactTransportIntegral_apply ν)
  letI : IsProbabilityMeasure γ := ⟨hγ.1⟩
  refine ⟨γ, hγ, le_compactLogModulusIntegral_of_truncations _ γ a (fun n => ?_)⟩
  simpa only [γ, integral_compactTransportMeasure L hL.1] using hcost n

/-- The log determinant of an ordered continuous finite-rank kernel is
bounded by the best log-modulus integral over its spectral couplings. -/
theorem fugledeKadisonLog_continuousKernel_le_log_transport
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (φ : C(X, ℂ) →⋆ₐ[ℂ] A) (ψ : C(Y, ℂ) →⋆ₐ[ℂ] A)
    (f : ρ → C(X, ℂ)) (g : ρ → C(Y, ℂ)) :
    fugledeKadisonLog τ (tracialContinuousKernel φ ψ f g) ≤
      sSup { h : EReal | ∃ γ, IsSpectralTransportCoupling (continuousSpectralMeasure τ hτ φ)
        (continuousSpectralMeasure τ hτ ψ) γ ∧ h = compactLogModulusIntegral (continuousKernelFunction f g) γ } := by
  let T := tracialContinuousKernel φ ψ f g
  by_cases hb : fugledeKadisonLog τ T = ⊥
  · change fugledeKadisonLog τ T ≤ _
    rw [hb]
    exact bot_le
  have ht : fugledeKadisonLog τ T ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (iInf_le _ (⟨1, zero_lt_one⟩ : Ioi (0 : ℝ))) (EReal.coe_lt_top _)
  let a := (fugledeKadisonLog τ T).toReal
  have he : (a : EReal) = fugledeKadisonLog τ T := EReal.coe_toReal ht hb
  obtain ⟨γ, hγ, hc⟩ := exists_continuous_kernel_transport_coupling τ hτ φ ψ f g a he.le
  calc
    _ = (a : EReal) := he.symm
    _ ≤ compactLogModulusIntegral (continuousKernelFunction f g) γ := hc
    _ ≤ _ := le_sSup ⟨γ, hγ, rfl⟩

/-- Continuous spectral transport on the spectra of two normal
operators in a tracial C-star algebra. -/
theorem fugledeKadisonLog_normalKernel_le_log_transport
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (U V : A) (hU : IsStarNormal U) (hV : IsStarNormal V)
    (f : ρ → C(spectrum ℂ U, ℂ)) (g : ρ → C(spectrum ℂ V, ℂ)) :
    let φ := cfcHom hU (R := ℂ)
    let ψ := cfcHom hV (R := ℂ)
    fugledeKadisonLog τ (∑ r, φ (f r) * ψ (g r)) ≤
      sSup { h : EReal | ∃ γ, IsSpectralTransportCoupling (continuousSpectralMeasure τ hτ φ)
        (continuousSpectralMeasure τ hτ ψ) γ ∧ h = compactLogModulusIntegral (continuousKernelFunction f g) γ } :=
  fugledeKadisonLog_continuousKernel_le_log_transport τ hτ (cfcHom hU) (cfcHom hV) f g

/-- The sum of two normal operators satisfies the transport bound for
the log modulus of the sum of two spectral values. -/
theorem fugledeKadisonLog_normalSum_le_log_transport
    (τ : A →L[ℂ] ℂ) (hτ : IsNormalizedTracialState τ)
    (U V : A) (hU : IsStarNormal U) (hV : IsStarNormal V) :
    let μ := continuousSpectralMeasure τ hτ (cfcHom hU (R := ℂ))
    let ν := continuousSpectralMeasure τ hτ (cfcHom hV (R := ℂ))
    let k : C(spectrum ℂ U × spectrum ℂ V, ℂ) :=
      ⟨fun p => p.1.val + p.2.val,
        (continuous_subtype_val.comp continuous_fst).add
          (continuous_subtype_val.comp continuous_snd)⟩
    fugledeKadisonLog τ (U + V) ≤
      sSup {h : EReal | ∃ γ, IsSpectralTransportCoupling μ ν γ ∧ h = compactLogModulusIntegral k γ} := by
  let f : Fin 2 → C(spectrum ℂ U, ℂ) :=
    ![(ContinuousMap.id ℂ).restrict (spectrum ℂ U), 1]
  let g : Fin 2 → C(spectrum ℂ V, ℂ) :=
    ![1, (ContinuousMap.id ℂ).restrict (spectrum ℂ V)]
  have hI : tracialContinuousKernel (cfcHom hU) (cfcHom hV) f g = U + V := by
    rw [tracialContinuousKernel, Fin.sum_univ_two]
    simp [f, g, cfcHom_id]
  have hK : continuousKernelFunction f g =
      (⟨fun p => p.1.val + p.2.val,
        (continuous_subtype_val.comp continuous_fst).add
          (continuous_subtype_val.comp continuous_snd)⟩ : C(spectrum ℂ U × spectrum ℂ V, ℂ)) := by
    ext p
    rw [continuousKernelFunction_apply, Fin.sum_univ_two]
    simp [f, g]
  simpa only [hI, hK] using
    fugledeKadisonLog_continuousKernel_le_log_transport τ hτ (cfcHom hU) (cfcHom hV) f g

end

end MOC

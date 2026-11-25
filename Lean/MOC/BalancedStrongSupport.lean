import MOC.SpectralGap
import MOC.StrongSupport

/-! A quadratic support penalty on a spectrally normalized violating orbit. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A strict violation yields balanced spectra that minimize the energy and
denominator expression along shifted Möbius changes. On these same spectra
there is a nonsingular nonnormal support maximizer with a quadratic penalty. -/
theorem exists_balanced_quadratic_support_frobenius_maximizer
    (a₀ b₀ : ι → ℂ) (U₀ : Matrix ι ι ℂ) (hU₀ : IsUnitary U₀)
    (hbad : ¬ Holds a₀ b₀ U₀) :
    ∃ (a b : ι → ℂ) (V : Matrix ι ι ℂ) (ξ : ℂ),
      IsUnitary V ∧ spectralEnergy a b = 1 ∧
      (∑ i, a i) = (∑ i, b i) ∧
      (∑ i, (Complex.normSq (a i) : ℂ) * a i) =
        (∑ i, (Complex.normSq (b i) : ℂ) * b i) ∧
      (∀ t s : ℂ, (∀ i, 1 - t * a i ≠ 0) → (∀ j, 1 + t * b j ≠ 0) →
        let E := spectralEnergy (fun i => mobiusSpectrum t a i + s)
          (fun j => mobiusSpectrum (-t) b j - s)
        0 < E → 1 ≤ E ^ Fintype.card ι * Complex.normSq (mobiusDenominator a b t)) ∧
      determinantValue a b V ≠ 0 ∧
      ¬ IsStarNormal (diagonal a + V * diagonal b * Vᴴ) ∧
      (∀ σ : Equiv.Perm ι,
        (ξ * matchingProduct a b σ).re < (ξ * determinantValue a b V).re) ∧
      (∀ W : Matrix ι ι ℂ, IsUnitary W →
        (ξ * (determinantValue a b W - determinantValue a b V)).re ≤
          -Complex.normSq (determinantValue a b W - determinantValue a b V) / 2) ∧
      ∀ W : Matrix ι ι ℂ, IsUnitary W →
        (ξ * determinantValue a b W).re = (ξ * determinantValue a b V).re →
        frobeniusSq (diagonal a + W * diagonal b * Wᴴ) ≤
          frobeniusSq (diagonal a + V * diagonal b * Vᴴ) := by
  obtain ⟨a, b, U, η, g, hU, henergy, hη, hg, htrace, hcubic, _, hgap, hglobal⟩ :=
    exists_balanced_support_gap_maximizer a₀ b₀ U₀ hU₀ hbad
  have hsep (σ : Equiv.Perm ι) :
      (η * matchingProduct a b σ).re < (η * determinantValue a b U).re := by
    simpa only [mul_sub, Complex.sub_re, sub_pos] using hg.trans_le (hgap σ)
  obtain ⟨V, ξ, hV, hstrict, hpenalty, htie⟩ :=
    exists_quadratic_support_frobenius_maximizer a b U hU η hsep
  have hfail : ¬ Holds a b V := by
    intro hh
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b V).mp hh ξ
    exact (not_lt_of_ge hσ) (hstrict σ)
  have hmax (W : Matrix ι ι ℂ) (hW : IsUnitary W) :
      (ξ * determinantValue a b W).re ≤ (ξ * determinantValue a b V).re := by
    have h := hpenalty W hW
    rw [mul_sub, Complex.sub_re] at h
    linarith only [h, Complex.normSq_nonneg (determinantValue a b W - determinantValue a b V)]
  refine ⟨a, b, V, ξ, hV, henergy, htrace, hcubic, ?_, ?_, ?_, hstrict, hpenalty, htie⟩
  · intro t s ha hb
    exact spectralEnergy_shifted_mobius_bound a b U hU η hη hg hgap
      (fun c d k hcd hk => hglobal c d U k hcd hU hk) t s ha hb
  · exact fun hzero => hfail (holds_of_singular a b hV hzero)
  · exact fun hnormal => hfail (holds_of_normal_support_frobenius_maximum a b hV ξ hnormal hmax htie)

end MOC

import MOC.GeneralizedSpectralCircles
import MOC.TwoExceptions

/-! The Hermitian-by-normal target and its equivalent circle-or-line formulation. -/

open Matrix

namespace MOC

/-- The determinant hull inclusion with one real spectrum and one arbitrary complex spectrum. -/
def HermitianByNormal (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (a : ι → ℝ) (b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
    Holds (fun i => (a i : ℂ)) b U

/-- In every finite dimension, the Hermitian-by-normal target is equivalent to
inclusion whenever either spectrum lies on a circle or line. -/
theorem hermitianByNormal_iff_generalized_circle {ι : Type*} [Fintype ι] [DecidableEq ι] :
    HermitianByNormal ι ↔ ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      SpectrumOnGeneralizedCircle a ∨ SpectrumOnGeneralizedCircle (fun i => -b i) →
      Holds a b U := by
  constructor
  · intro h a b U hU hc
    have hleft (x y : ι → ℂ) (V : Matrix ι ι ℂ) (hV : IsUnitary V)
        (hx : SpectrumOnGeneralizedCircle x) : Holds x y V := by
      obtain ⟨r, s, hrs⟩ := exists_real_spectrum_of_generalized_circle x y hx V hV
      exact hrs.mp (h r s V hV)
    rcases hc with ha | hb
    · exact hleft a b U hU ha
    · have hU' : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
      have hb' : SpectrumOnGeneralizedCircle b := by
        simpa only [neg_neg] using spectrumOnGeneralizedCircle_neg hb
      exact (holds_swap_iff a b hU).mp (hleft b a Uᴴ hU' hb')
  · intro h a b U hU
    exact h _ b U hU (Or.inl (spectrumOnGeneralizedCircle_of_line _
      0 1 0 (Or.inr one_ne_zero) (fun i => by simp)))

/-- Order four reduces to the Hermitian-by-normal target and the case of two
simple spectra each lying off every generalized circle. -/
theorem conjecture_four_iff_hermitianByNormal_and_noncircular :
    Conjecture (Fin 4) ↔ HermitianByNormal (Fin 4) ∧
      ∀ (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ), IsUnitary U →
        Function.Injective a → Function.Injective b →
        ¬ SpectrumOnGeneralizedCircle a → ¬ SpectrumOnGeneralizedCircle (fun i => -b i) →
        Holds a b U := by
  constructor
  · intro h
    exact ⟨fun a b U hU => h _ b U hU, fun a b U hU _ _ _ _ => h a b U hU⟩
  · rintro ⟨hreal, hnoncircular⟩ a b U hU
    by_cases hc : SpectrumOnGeneralizedCircle a ∨ SpectrumOnGeneralizedCircle (fun i => -b i)
    · exact hermitianByNormal_iff_generalized_circle.mp hreal a b U hU hc
    by_cases ha : Function.Injective a
    · by_cases hb : Function.Injective b
      · exact hnoncircular a b U hU ha hb (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))
      · exact holds_four_of_repeated_spectrum a b U hU (Or.inr hb)
    · exact holds_four_of_repeated_spectrum a b U hU (Or.inl ha)

end MOC

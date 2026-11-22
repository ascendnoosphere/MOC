import MOC.FiveNonreal
import MOC.TwoSpectralCircles

open Matrix

namespace MOC

/-- The nonreal labels of the spectrum lie on a single circle or affine line. -/
def NonrealSpectrumOnGeneralizedCircle {ι : Type*} (b : ι → ℂ) : Prop :=
  SpectrumOnGeneralizedCircle (fun i : {i // (b i).im ≠ 0} => b i)

private theorem nonrealSpectrumOnGeneralizedCircle_inv_sub_real {ι κ : Type*}
    {b : ι → ℂ} (hb : NonrealSpectrumOnGeneralizedCircle b) (e : κ → ι) (r : ℝ) :
    NonrealSpectrumOnGeneralizedCircle (fun i => (b (e i) - (r : ℂ))⁻¹) := by
  let f (i : κ) := (b (e i) - (r : ℂ))⁻¹
  change SpectrumOnGeneralizedCircle (fun i : {i // (f i).im ≠ 0} => f i)
  rcases isEmpty_or_nonempty {i // (f i).im ≠ 0} with hi | hi
  · letI := hi
    exact spectrumOnGeneralizedCircle_of_line _ 0 1 0 (Or.inr one_ne_zero) (fun i => isEmptyElim i)
  obtain ⟨q, u, v, c, hnonconstant, hcircle⟩ := hb
  let d := q * (r * r) - 2 * u * r + c
  have hf (i : {i // (f i).im ≠ 0}) :
      d * Complex.normSq (f i) - 2 * ((u - q * r) * (f i).re - v * (f i).im) + q = 0 := by
    let z := b (e i)
    let x := z - (r : ℂ)
    have hz₀ : z.im ≠ 0 := fun h => i.property ((inv_sub_real_im_eq_zero_iff z r).mpr h)
    have hx : x ≠ 0 := fun h => hz₀ (by
      simpa only [x, Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] using
        congrArg Complex.im h)
    have hz := hcircle ⟨e i, hz₀⟩
    change q * Complex.normSq z - 2 * (u * z.re + v * z.im) + c = 0 at hz
    have htranslated :
        q * Complex.normSq x - 2 * ((u - q * r) * x.re + v * x.im) + d = 0 := by
      dsimp only [x, d]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, sub_zero] at hz ⊢
      linear_combination hz
    change d * Complex.normSq x⁻¹ - 2 * ((u - q * r) * x⁻¹.re - v * x⁻¹.im) + q = 0
    rw [Complex.normSq_inv, Complex.inv_re, Complex.inv_im]
    field_simp [(Complex.normSq_pos.mpr hx).ne'] <;> linear_combination htranslated
  refine ⟨d, u - q * r, -v, q, ?_, fun i => ?_⟩
  · by_contra! h
    obtain ⟨hd, hu, hv⟩ := h
    have hv' : v = 0 := neg_eq_zero.mp hv
    obtain ⟨i⟩ := hi
    have hq : q = 0 := by
      simpa only [hd, hu, hv', zero_mul, mul_zero, sub_zero, zero_add] using hf i
    have hu' : u = 0 := by simpa only [hq, zero_mul, sub_zero] using hu
    rcases hnonconstant with hq' | hu'' | hv''
    · exact hq' hq
    · exact hu'' hu'
    · exact hv'' hv'
  · change d * Complex.normSq (f i) - 2 * ((u - q * r) * (f i).re + (-v) * (f i).im) + q = 0
    simpa only [neg_mul, sub_eq_add_neg] using hf i

/-- The determinant hull inclusion holds for a real first spectrum and a
partner whose nonreal labels lie on a single generalized circle. -/
theorem holds_of_nonreal_partner_on_generalized_circle {n : ℕ}
    (a : Fin n → ℝ) (b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) (hb : NonrealSpectrumOnGeneralizedCircle b) :
    Holds (fun i => (a i : ℂ)) b U := by
  induction n with
  | zero => exact conjecture_zero _ b U hU
  | succ n ih =>
    by_cases hreal : ∃ p, (b p).im = 0
    · obtain ⟨p, hp⟩ := hreal
      apply holds_of_real_pivot_of_transformed_partner a b U hU p hp
      intro r a' V hV
      exact ih a' _ V hV (nonrealSpectrumOnGeneralizedCircle_inv_sub_real hb p.succAbove r)
    · have hb' : SpectrumOnGeneralizedCircle b := by
        obtain ⟨q, u, v, c, h, hs⟩ := hb
        exact ⟨q, u, v, c, h, fun i => hs ⟨i, fun hi => hreal ⟨i, hi⟩⟩⟩
      exact holds_of_generalized_circular_spectra _ b
        (spectrumOnGeneralizedCircle_of_line _ 0 1 0 (Or.inr one_ne_zero) (fun i => by simp))
        (spectrumOnGeneralizedCircle_neg hb') U hU

end MOC

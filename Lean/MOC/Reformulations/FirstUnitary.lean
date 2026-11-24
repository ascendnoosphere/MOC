import MOC.TwoSpectralCircles

open Matrix

namespace MOC.Reformulations

/-- Atlas 005: the intrinsic restriction to unit-circle spectra. -/
theorem unitarySpectralHull {n : ℕ} (a b : Fin n → ℂ)
    (ha : ∀ i, Complex.normSq (a i) = 1) (hb : ∀ i, Complex.normSq (b i) = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  apply holds_of_circular_spectra a b 0 0 1 1 _ _ U hU
  · simpa using ha
  · simpa using hb

end MOC.Reformulations

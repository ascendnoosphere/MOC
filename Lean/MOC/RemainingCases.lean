import MOC.FourNonreal
import MOC.FullSupportReduction

/-! Remaining cases at orders four and five after the order-four circle theorem. -/

open Matrix

namespace MOC

/-- At order four, it suffices to check two noncircular spectra, with
distinct matching products, no zero pair sums and no zero unitary entries. -/
theorem conjecture_four_iff_noncircular_regular_full_support :
    Conjecture (Fin 4) ↔ ∀ (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ),
      IsUnitary U → (¬ SpectrumOnGeneralizedCircle a) → (¬ SpectrumOnGeneralizedCircle b) →
      (∀ i j, a i + b j ≠ 0) → Function.Injective (matchingProduct a b) →
      (∀ i j, U i j ≠ 0) → Holds a b U := by
  constructor
  · exact fun h a b U hU _ _ _ _ _ => h a b U hU
  · intro h
    apply conjecture_iff_regular_spectra_full_support.mpr
    intro a b U hU hs hi he
    by_cases ha : SpectrumOnGeneralizedCircle a
    · exact holds_four_of_generalized_circle a b U hU (Or.inl ha)
    by_cases hb : SpectrumOnGeneralizedCircle b
    · exact holds_four_of_generalized_circle a b U hU (Or.inr hb)
    exact h a b U hU ha hb hs hi he

/-- For a real first spectrum in order five, it suffices to treat partners
with five nonreal entries and unitaries with every entry nonzero. -/
theorem hermitianByNormal_five_iff_nonreal_full_support :
    HermitianByNormal (Fin 5) ↔ ∀ (a : Fin 5 → ℝ) (b : Fin 5 → ℂ)
      (U : Matrix (Fin 5) (Fin 5) ℂ), IsUnitary U → (∀ j, (b j).im ≠ 0) →
      (∀ i j, U i j ≠ 0) → Holds (fun i => (a i : ℂ)) b U := by
  constructor
  · exact fun h a b U hU _ _ => h a b U hU
  · intro h a b U hU
    by_cases hb : ∃ p, (b p).im = 0
    · obtain ⟨p, hp⟩ := hb
      exact holds_of_real_pivot_of_transformed_partner a b U hU p hp
        (fun _ a' V hV => hermitianByNormal_four a' _ V hV)
    · exact (holds_all_unitaries_iff_full_support _ _).mpr
        (fun V hV he => h a b V hV (fun j hj => hb ⟨j, hj⟩) he) U hU

end MOC

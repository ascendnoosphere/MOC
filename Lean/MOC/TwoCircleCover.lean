import MOC.HermitianByNormalGeneral

open Matrix

namespace MOC

/-- The first spectrum and a selected part of the negated second spectrum
lie on one circle or line. The remaining partner values lie on a second
circle or line. Both parts can have arbitrary size and multiplicities. -/
theorem holds_of_two_circle_cover {n : ℕ} (a b : Fin n → ℂ) (s : Set (Fin n))
    (hfirst : SpectrumOnGeneralizedCircle
      (Sum.elim a (fun i : s => -b i.val)))
    (hrest : SpectrumOnGeneralizedCircle (fun i : {i // i ∉ s} => -b i.val))
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  obtain ⟨x, f, hreal, hchart, hmap⟩ :=
    exists_real_chart_preserving_partner_circles a b (fun i => i ∈ s) hfirst U hU
  apply hchart.mp
  apply holds_of_nonreal_partner_on_generalized_circle x (f ∘ b) U hU
  have hother : SpectrumOnGeneralizedCircle (fun i : {i // i ∉ s} => b i.val) := by
    simpa only [neg_neg] using spectrumOnGeneralizedCircle_neg hrest
  have htrans := hmap sᶜ hother
  exact htrans.comp (fun i : {i // ((f ∘ b) i).im ≠ 0} =>
    ⟨i.val, fun hi => i.property (hreal i.val hi)⟩)

end MOC

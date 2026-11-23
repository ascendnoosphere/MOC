import MOC.WeightedDiamondComplete
import MOC.FiveNonreal

/-! Circle and line cases that follow from the order-four Hermitian-by-normal theorem. -/

open Matrix

namespace MOC

/-- In order four, either spectrum can lie on a circle or a line. -/
theorem holds_four_of_generalized_circle (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hc : SpectrumOnGeneralizedCircle a ∨ SpectrumOnGeneralizedCircle b) :
    Holds a b U := by
  apply hermitianByNormal_iff_generalized_circle.mp hermitianByNormal_four a b U hU
  rcases hc with h | h
  · exact Or.inl h
  · exact Or.inr (spectrumOnGeneralizedCircle_neg h)

/-- At most four nonreal partner entries suffice in every order. Count entries with multiplicity. -/
theorem hermitianByNormalAtMost_four (n : ℕ) : HermitianByNormalAtMost (Fin n) 4 := by
  refine (hermitianByNormalAtMost_iff_orders_le 4).mpr ?_ n
  intro m hm
  by_cases h : m ≤ 3
  · exact fun a b U hU => conjecture_le_three h _ b U hU
  have he : m = 4 := by omega
  subst m
  exact hermitianByNormal_four

/-- Up to four partner entries may lie outside the circle or line of the first spectrum. -/
theorem holds_of_common_generalized_circle_with_four_outliers {n : ℕ}
    (a b : Fin n → ℂ) (outliers : Finset (Fin n)) (hcard : outliers.card ≤ 4)
    (hc : SpectrumOnGeneralizedCircle
      (Sum.elim a (fun i : {i // i ∉ outliers} => -b i.val)))
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  classical
  obtain ⟨x, f, hf, hchart⟩ := exists_real_chart_of_common_generalized_circle
    a b (fun i => i ∉ outliers) hc U hU
  apply hchart.mp
  apply hermitianByNormalAtMost_four n x (f ∘ b) U hU
  unfold nonrealCount
  apply le_trans (Finset.card_le_card ?_) hcard
  intro i hi
  by_contra hout
  exact (Finset.mem_filter.mp hi).2 (hf i hout)

/-- In order five, one reflected partner entry on the circle or line suffices. -/
theorem holds_five_of_common_generalized_circle_contact (a b : Fin 5 → ℂ) (j : Fin 5)
    (hc : SpectrumOnGeneralizedCircle (Sum.elim a (fun _ : Unit => -b j)))
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) : Holds a b U := by
  refine holds_of_common_generalized_circle_with_four_outliers a b (Finset.univ.erase j)
    (by simp [Finset.card_erase_of_mem]) ?_ U hU
  obtain ⟨q, u, v, c, hn, hp⟩ := hc
  refine ⟨q, u, v, c, hn, ?_⟩
  rintro (i | i)
  · exact hp (.inl i)
  · have hi : i.val = j := by simpa using i.property
    simpa [hi] using hp (.inr ())

end MOC

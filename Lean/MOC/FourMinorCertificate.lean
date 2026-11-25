import MOC.ContactCensus
import MOC.Support
import MOC.TwoValues

/-! A nonnegative profile decomposition gives an order-four support bound. -/

namespace MOC

open BigOperators

noncomputable section

/-- A directional lower bound on the matching products also bounds the
determinant whenever the order-four inclusion has already been proved. -/
theorem four_lower_support_of_holds (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (h : Holds a b U)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re) :
    H ≤ (η * determinantValue a b U).re := by
  obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp h (-η)
  obtain ⟨i, hi⟩ := fourPerm_surjective σ.symm
  have hi' : (fourPerm i).symm = σ := by simp [hi]
  have he := hn i
  rw [hi'] at he
  simp only [neg_mul, Complex.neg_re, neg_le_neg_iff] at hσ
  exact he.trans hσ

/-- The determinant support gap of a signed subset-image decomposition is
the same linear combination of squared minors. -/
theorem four_gap_eq_minor_decomposition {κ : Type*} [Fintype κ]
    (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (r : Fin 24)
    (hr : (η * matchingProduct a b (fourPerm r).symm).re = H)
    (I J : κ → Finset (Fin 4)) (w : κ → ℝ)
    (hdecomp : ∀ i : Fin 24, (η * matchingProduct a b (fourPerm i).symm).re - H =
      ∑ k, if (J k).map (fourPerm i).symm.toEmbedding = I k then w k else 0) :
    (η * determinantValue a b U).re - H = ∑ k, w k * subsetMinorSq U (I k) (J k) := by
  apply gap_eq_minor_decomposition a b η H U hU I J w
  intro σ
  obtain ⟨i, hi⟩ := fourPerm_surjective σ.symm
  have hi' : (fourPerm i).symm = σ := by simp [hi]
  simpa only [hi'] using hdecomp i

/-- Each ordinary subset-image profile has nonnegative unitary signed mass.
Thus a nonnegative combination of such profiles certifies the prescribed
support inequality. -/
theorem four_support_of_minor_gap_decomposition {κ : Type*} [Fintype κ]
    (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (r : Fin 24)
    (hr : (η * matchingProduct a b (fourPerm r).symm).re = H)
    (I J : κ → Finset (Fin 4)) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hdecomp : ∀ i : Fin 24, (η * matchingProduct a b (fourPerm i).symm).re - H =
      ∑ k, if (J k).map (fourPerm i).symm.toEmbedding = I k then w k else 0) :
    H ≤ (η * determinantValue a b U).re := by
  apply sub_nonneg.mp
  rw [four_gap_eq_minor_decomposition a b η H U hU r hr I J w hdecomp]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hw k) (subsetMinorSq_nonneg U _ _))

end

end MOC

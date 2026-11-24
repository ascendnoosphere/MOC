import MOC.FullSupportReduction
import MOC.Reformulations.NativeLinksCTraceless

/-! The traceless reduction and the single-direction support test are
compatible: simultaneous scalar multiplication preserves both traces. -/

open BigOperators Matrix

namespace MOC.Reformulations

/-- To prove unrestricted MOC, it suffices to dominate the real part of
each traceless determinant by one permutation, in orders at least four
and with no zero entries in the relative unitary. -/
theorem moc_iff_traceless_real_bound :
    MOCIsTrue ↔ ∀ (n : ℕ), 4 ≤ n →
      ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
        (∀ i j, U i j ≠ 0) → ∑ i, a i = 0 → ∑ j, b j = 0 →
        ∃ σ : Equiv.Perm (Fin n), (determinantValue a b U).re ≤ (matchingProduct a b σ).re := by
  constructor
  · intro h n _ a b U hU _ _ _
    simpa using (holds_iff_directional a b U).mp (h n a b U hU) 1
  · intro h
    apply tracelessCartanForm_iff.mp
    intro n a b U hU ha hb
    by_cases hn : 4 ≤ n
    · apply (holds_all_unitaries_iff_full_support a b).mpr _ U hU
      intro V hV hfull
      apply (holds_iff_directional a b V).mpr
      intro k
      have hcard : Fintype.card (Fin n) ≠ 0 := by simp; omega
      let c : ℂ := k ^ ((Fintype.card (Fin n) : ℂ)⁻¹)
      have hc : c ^ Fintype.card (Fin n) = k := Complex.cpow_nat_inv_pow k hcard
      have ha' : ∑ i, c * a i = 0 := by rw [← Finset.mul_sum, ha, mul_zero]
      have hb' : ∑ j, c * b j = 0 := by rw [← Finset.mul_sum, hb, mul_zero]
      obtain ⟨σ, hσ⟩ := h n hn (fun i => c * a i) (fun j => c * b j) V hV hfull ha' hb'
      rw [determinantValue_scale, matchingProduct_scale, hc] at hσ
      exact ⟨σ, hσ⟩
    · exact conjecture_le_three (by omega) a b U hU

end MOC.Reformulations

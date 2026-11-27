import MOC.SpectralMinorDecomposition

open BigOperators

namespace MOC

/-- For each mixer and fixed spectra, one law works for every value of
one selected partner entry. Its support has at most five permutations. -/
def OneFreePartnerEntryLaw (n : ℕ) : Prop :=
  ∀ (a b : Fin n → ℂ) (j : Fin n) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U → ∃ k : ℕ, k ≤ 5 ∧
      ∃ (p : Fin k → Equiv.Perm (Fin n)) (w : Fin k → ℝ),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ∀ z : ℂ,
          (∑ i, (w i : ℂ) * matchingProduct a (Function.update b j z) (p i)) =
            determinantValue a (Function.update b j z) U

/-- The common-law test for one free entry is equivalent to the conjecture
in the same order, including order zero. -/
theorem oneFreePartnerEntryLaw_iff (n : ℕ) :
    OneFreePartnerEntryLaw n ↔ Conjecture (Fin n) := by
  constructor
  · intro h a b U hU
    by_cases hn : n = 0
    · subst n
      exact conjecture_zero a b U hU
    let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have h' := (one_free_partner_entry_iff_common_law a b j U hU).mpr
      (h a b j U hU) (b j)
    simpa only [Function.update_eq_self] using h'
  · intro h a b j U hU
    exact (one_free_partner_entry_iff_common_law a b j U hU).mp
      (fun z => h a (Function.update b j z) U hU)

end MOC

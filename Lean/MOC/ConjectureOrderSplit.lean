import MOC.Claim

namespace MOC

/-- The proved base orders leave exactly orders four, five, and at least six. -/
theorem mocIsTrue_iff_four_five_and_higher :
    MOCIsTrue ↔ Conjecture (Fin 4) ∧ Conjecture (Fin 5) ∧
      ∀ n, 6 ≤ n → Conjecture (Fin n) := by
  refine ⟨fun h => ⟨h 4, h 5, fun n _ => h n⟩, ?_⟩
  rintro ⟨h4, h5, hhi⟩
  apply mocIsTrue_iff_from_four.mpr
  intro n hn
  by_cases h : n = 4
  · subst n
    exact h4
  by_cases h : n = 5
  · subst n
    exact h5
  exact hhi n (by omega)

end MOC

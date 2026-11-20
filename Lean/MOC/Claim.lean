import MOC.Small

namespace MOC

/-- The unrestricted Marcus–de Oliveira conjecture in every finite order.
This proposition is the open target for the spectral formulation. -/
def MOCIsTrue : Prop :=
  ∀ n : ℕ, Conjecture (Fin n)

/-- Orders two and three, together with the subsingleton cases, give the exact
base range for the unrestricted conjecture. -/
theorem mocIsTrue_iff_from_four :
    MOCIsTrue ↔ ∀ n : ℕ, 4 ≤ n → Conjecture (Fin n) := by
  constructor
  · intro h n _
    exact h n
  · intro h n
    by_cases hn : 4 ≤ n
    · exact h n hn
    · exact conjecture_le_three (by omega)

/-- A counterexample of least order has size at least four, and every smaller
order satisfies the full spectral conjecture. -/
theorem exists_least_bad_order (h : ¬ MOCIsTrue) :
    ∃ n : ℕ, 4 ≤ n ∧ ¬ Conjecture (Fin n) ∧ ∀ m < n, Conjecture (Fin m) := by
  classical
  have hex : ∃ n : ℕ, ¬ Conjecture (Fin n) := not_forall.mp h
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · by_contra hn
    exact Nat.find_spec hex (conjecture_le_three (by omega))
  · intro m hm
    exact not_not.mp (Nat.find_min hex hm)

end MOC

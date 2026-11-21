import MOC.Small

open Matrix

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

/-- Independent row and column relabelings exhibit two nonempty square blocks. -/
def HasProperPairedBlocks {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (m k : ℕ) (eRow eCol : Fin m ⊕ Fin k ≃ Fin n)
    (V : Matrix (Fin m) (Fin m) ℂ) (W : Matrix (Fin k) (Fin k) ℂ),
    0 < m ∧ 0 < k ∧ U.submatrix eRow eCol = fromBlocks V 0 0 W

/-- A least-order counterexample has no proper paired block split. -/
theorem exists_least_bad_instance (h : ¬ MOCIsTrue) :
    ∃ n : ℕ, 4 ≤ n ∧ (∀ m < n, Conjecture (Fin m)) ∧
      ∃ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
        IsUnitary U ∧ ¬ Holds a b U ∧ ¬ HasProperPairedBlocks U := by
  obtain ⟨n, hn, hbad, hbelow⟩ := exists_least_bad_order h
  unfold Conjecture at hbad
  push_neg at hbad
  obtain ⟨a, b, U, hU, hbad⟩ := hbad
  refine ⟨n, hn, hbelow, a, b, U, hU, hbad, ?_⟩
  rintro ⟨m, k, eRow, eCol, V, W, hm, hk, hBlocks⟩
  have hcard := Fintype.card_congr eRow
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  exact hbad (holds_of_paired_blocks (hbelow m (by omega)) (hbelow k (by omega))
    eRow eCol a b U hU V W hBlocks)

/-- It suffices to prove the hull inclusion in order at least four for eigenbases
that admit no proper paired block split. -/
theorem mocIsTrue_iff_no_proper_paired_blocks :
    MOCIsTrue ↔ ∀ (n : ℕ), 4 ≤ n → ∀ (a b : Fin n → ℂ)
      (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U → ¬ HasProperPairedBlocks U →
        Holds a b U := by
  constructor
  · intro h n _ a b U hU _
    exact h n a b U hU
  · intro h
    by_contra hbad
    obtain ⟨n, hn, _, a, b, U, hU, hfail, hblocks⟩ := exists_least_bad_instance hbad
    exact hfail (h n hn a b U hU hblocks)

end MOC

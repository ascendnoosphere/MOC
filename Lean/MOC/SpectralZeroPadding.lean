import MOC.RankTwoOverlap

/-! Appending zero eigenvalues preserves the support sizes. Once the new
order reaches their sum minus two, the relative unitary is arbitrary. -/

open Matrix

namespace MOC

/-- Add `m` zero entries to the end of a spectral list. -/
def padSpectrumWithZeros {n : ℕ} (a : Fin n → ℂ) (m : ℕ) (i : Fin (n + m)) : ℂ :=
  if h : i.val < n then a ⟨i.val, h⟩ else 0

theorem padSpectrumWithZeros_zero {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    padSpectrumWithZeros a 0 i = a i := dif_pos i.isLt

theorem spectralSupport_pad_card_le {n : ℕ} (a : Fin n → ℂ) (m : ℕ) :
    (spectralSupport (padSpectrumWithZeros a m)).card ≤ (spectralSupport a).card := by
  classical
  let e : Fin n ↪ Fin (n + m) :=
    ⟨fun i => ⟨i.val, by omega⟩, fun _ _ h => Fin.ext (congrArg Fin.val h)⟩
  have sub : spectralSupport (padSpectrumWithZeros a m) ⊆ (spectralSupport a).map e := by
    intro i hi
    have hn : padSpectrumWithZeros a m i ≠ 0 := (Finset.mem_filter.mp hi).2
    by_cases h : i.val < n
    · let j : Fin n := ⟨i.val, h⟩
      have heq : padSpectrumWithZeros a m i = a j := dif_pos h
      exact Finset.mem_map.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq ▸ hn⟩, Fin.ext rfl⟩
    · exact (hn (by simp [padSpectrumWithZeros, h])).elim
  simpa only [Finset.card_map] using Finset.card_le_card sub

/-- An all-unitary result in order `n` extends to every larger order if
the combined support size at the initial order is at most `n + 3`. -/
theorem holds_all_zero_paddings {n : ℕ} (a b : Fin n → ℂ)
    (hsize : (spectralSupport a).card + (spectralSupport b).card ≤ n + 3)
    (hbase : ∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V → Holds a b V)
    (m : ℕ) (U : Matrix (Fin (n + m)) (Fin (n + m)) ℂ) (hU : IsUnitary U) :
    Holds (padSpectrumWithZeros a m) (padSpectrumWithZeros b m) U := by
  cases m with
  | zero =>
    have hpad (v : Fin n → ℂ) : padSpectrumWithZeros v 0 = v :=
      funext (padSpectrumWithZeros_zero v)
    simpa only [hpad] using hbase U hU
  | succ m =>
    apply holds_of_shifted_support_le_card_add_two _ _ U hU 0
    simp only [add_zero, sub_zero, Fintype.card_fin]
    have ha := spectralSupport_pad_card_le a (m + 1)
    have hb := spectralSupport_pad_card_le b (m + 1)
    omega

private theorem support_five_le_four (a : Fin 5 → ℂ) (i : Fin 5) (hi : a i = 0) :
    (spectralSupport a).card ≤ 4 := by
  classical
  have sub : spectralSupport a ⊆ Finset.univ.erase i := by
    intro j hj
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    exact (Finset.mem_filter.mp hj).2 hi
  calc
    _ ≤ _ := Finset.card_le_card sub
    _ = 4 := by simp

/-- A common zero in order five supplies the support bound needed for
unrestricted unitary mixing after any number of zero pads. -/
theorem holds_all_zero_paddings_five (a b : Fin 5 → ℂ) (i j : Fin 5)
    (ha : a i = 0) (hb : b j = 0)
    (hbase : ∀ V : Matrix (Fin 5) (Fin 5) ℂ, IsUnitary V → Holds a b V)
    (m : ℕ) (U : Matrix (Fin (5 + m)) (Fin (5 + m)) ℂ) (hU : IsUnitary U) :
    Holds (padSpectrumWithZeros a m) (padSpectrumWithZeros b m) U := by
  apply holds_all_zero_paddings a b _ hbase m U hU
  have h₁ := support_five_le_four a i ha
  have h₂ := support_five_le_four b j hb
  omega

end MOC

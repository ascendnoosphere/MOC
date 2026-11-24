import MOC.Core
import Mathlib.Tactic.NormNum

/-! The mixed indicator cost is nonnegative on every permutation, by injectivity. -/

namespace MOC

noncomputable section

/-- The four indicator coordinates of the mixed cost, written on a row-to-column permutation. -/
def permutationCost (σ : Equiv.Perm (Fin 4)) : ℝ :=
  (if σ 1 = 0 then 1 else 0) + (if σ 3 = 2 then 1 else 0) +
    (if (σ 2 = 0 ∧ σ 3 = 3) ∨ (σ 2 = 3 ∧ σ 3 = 0) then 1 else 0) -
    (if (σ 1 = 0 ∧ σ 2 = 1) ∨ (σ 1 = 1 ∧ σ 2 = 0) then 1 else 0)

theorem permutationCost_nonneg (σ : Equiv.Perm (Fin 4)) : 0 ≤ permutationCost σ := by
  have bit_nonneg (p : Prop) [Decidable p] : 0 ≤ (if p then (1 : ℝ) else 0) := by
    split <;> norm_num
  have hA := bit_nonneg (σ 1 = 0)
  have hB := bit_nonneg (σ 3 = 2)
  have hC := bit_nonneg ((σ 2 = 0 ∧ σ 3 = 3) ∨ (σ 2 = 3 ∧ σ 3 = 0))
  unfold permutationCost
  by_cases hneg : (σ 1 = 0 ∧ σ 2 = 1) ∨ (σ 1 = 1 ∧ σ 2 = 0)
  · rw [if_pos hneg]
    apply sub_nonneg.mpr
    rcases hneg with ⟨h10, _⟩ | ⟨h11, h20⟩
    · -- The first singleton indicator pays for the negative minor.
      rw [if_pos h10]
      exact (le_add_of_nonneg_right hB).trans (le_add_of_nonneg_right hC)
    · -- Injectivity leaves only columns 2 and 3 available in row 3.
      have h30 : σ 3 ≠ 0 := fun heq => by
        have h := σ.injective (heq.trans h20.symm)
        omega
      have h31 : σ 3 ≠ 1 := fun heq => by
        have h := σ.injective (heq.trans h11.symm)
        omega
      by_cases h32 : σ 3 = 2
      · rw [if_pos h32]
        simpa only [zero_add, add_zero] using
          add_le_add (add_le_add hA (le_refl (1 : ℝ))) hC
      · have h33 : σ 3 = 3 := by omega
        rw [if_pos (Or.inl ⟨h20, h33⟩)]
        simpa only [zero_add] using add_le_add (add_nonneg hA hB) (le_refl (1 : ℝ))
  · rw [if_neg hneg, sub_zero]
    exact add_nonneg (add_nonneg hA hB) hC

end

end MOC

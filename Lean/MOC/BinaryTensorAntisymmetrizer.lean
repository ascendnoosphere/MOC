import MOC.SegreConvexity
import Mathlib.Combinatorics.Enumerative.Catalan

/-! The antisymmetrizer on three binary tensor positions vanishes even
when arbitrary remaining positions are held fixed. -/

open BigOperators

namespace MOC.BinaryTensorAntisymmetrizer

noncomputable section

/-- The signed sum of the six permutations vanishes in every pair of binary
basis coordinates. Additional tensor factors are fixed by these permutations. -/
theorem three_position_antisymmetrizer {κ : Type*} [Fintype κ] [DecidableEq κ]
    (x y : Fin 3 ⊕ κ → Bool) :
    (∑ p : Equiv.Perm (Fin 3), (Equiv.Perm.sign p : ℤ) *
      (if ∀ j, x ((p.sumCongr (Equiv.refl κ)) j) = y j then 1 else 0)) = 0 := by
  classical
  have hlocal : ∀ a b : Fin 3 → Bool, (∑ p : Equiv.Perm (Fin 3),
      (Equiv.Perm.sign p : ℤ) * (if ∀ j, a (p j) = b j then 1 else 0)) = 0 := by
    decide +kernel
  by_cases hout : ∀ j : κ, x (.inr j) = y (.inr j)
  · have hsplit (p : Equiv.Perm (Fin 3)) :
        (∀ j, x ((p.sumCongr (Equiv.refl κ)) j) = y j) ↔
          ∀ j : Fin 3, x (.inl (p j)) = y (.inl j) := by
      constructor
      · exact fun h j => h (.inl j)
      · intro h j
        cases j with
        | inl j => exact h j
        | inr j => exact hout j
    simp_rw [hsplit]
    exact hlocal (fun j => x (.inl j)) (fun j => y (.inl j))
  · have hnone (p : Equiv.Perm (Fin 3)) :
        ¬ ∀ j, x ((p.sumCongr (Equiv.refl κ)) j) = y j :=
      fun h => hout fun j => h (.inr j)
    simp [hnone]

/-- The five Catalan numbers in the reported dimension table. -/
theorem catalan_table : catalan 3 = 5 ∧ catalan 4 = 14 ∧ catalan 5 = 42 ∧
    catalan 6 = 132 ∧ catalan 7 = 429 := by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

end

end MOC.BinaryTensorAntisymmetrizer

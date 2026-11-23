import MOC.Core
import Mathlib.Data.Fintype.Perm

/-! Lexicographic labels for the permutations of five entries. -/

namespace MOC.FivePermutations

set_option maxRecDepth 16000
set_option maxHeartbeats 16000000

abbrev Label := Fin 120
abbrev Perm := Equiv.Perm (Fin 5)

private def permutations5 : Array Perm :=
  #[
    1,
    Equiv.swap 3 4,
    Equiv.swap 2 3,
    Equiv.swap 2 4 * Equiv.swap 2 3,
    Equiv.swap 3 2 * Equiv.swap 2 4,
    Equiv.swap 2 4,
    Equiv.swap 1 2,
    Equiv.swap 3 4 * Equiv.swap 1 2,
    Equiv.swap 1 3 * Equiv.swap 1 2,
    Equiv.swap 1 4 * Equiv.swap 1 3 * Equiv.swap 1 2,
    Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 1 2,
    Equiv.swap 1 4 * Equiv.swap 1 2,
    Equiv.swap 2 1 * Equiv.swap 1 3,
    Equiv.swap 2 4 * Equiv.swap 2 1 * Equiv.swap 1 3,
    Equiv.swap 1 3,
    Equiv.swap 1 4 * Equiv.swap 1 3,
    Equiv.swap 2 4 * Equiv.swap 1 3,
    Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 1 3,
    Equiv.swap 3 2 * Equiv.swap 2 1 * Equiv.swap 1 4,
    Equiv.swap 2 1 * Equiv.swap 1 4,
    Equiv.swap 3 1 * Equiv.swap 1 4,
    Equiv.swap 1 4,
    Equiv.swap 2 1 * Equiv.swap 2 3 * Equiv.swap 1 4,
    Equiv.swap 2 3 * Equiv.swap 1 4,
    Equiv.swap 0 1,
    Equiv.swap 3 4 * Equiv.swap 0 1,
    Equiv.swap 2 3 * Equiv.swap 0 1,
    Equiv.swap 2 4 * Equiv.swap 2 3 * Equiv.swap 0 1,
    Equiv.swap 3 2 * Equiv.swap 2 4 * Equiv.swap 0 1,
    Equiv.swap 2 4 * Equiv.swap 0 1,
    Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.swap 3 4 * Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.swap 3 0 * Equiv.swap 0 4 * Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.swap 0 4 * Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.swap 2 0 * Equiv.swap 0 3 * Equiv.swap 0 1,
    Equiv.swap 2 4 * Equiv.swap 2 0 * Equiv.swap 0 3 * Equiv.swap 0 1,
    Equiv.swap 0 3 * Equiv.swap 0 1,
    Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 1,
    Equiv.swap 2 4 * Equiv.swap 0 3 * Equiv.swap 0 1,
    Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 0 3 * Equiv.swap 0 1,
    Equiv.swap 3 2 * Equiv.swap 2 0 * Equiv.swap 0 4 * Equiv.swap 0 1,
    Equiv.swap 2 0 * Equiv.swap 0 4 * Equiv.swap 0 1,
    Equiv.swap 3 0 * Equiv.swap 0 4 * Equiv.swap 0 1,
    Equiv.swap 0 4 * Equiv.swap 0 1,
    Equiv.swap 2 0 * Equiv.swap 2 3 * Equiv.swap 0 4 * Equiv.swap 0 1,
    Equiv.swap 2 3 * Equiv.swap 0 4 * Equiv.swap 0 1,
    Equiv.swap 1 0 * Equiv.swap 0 2,
    Equiv.swap 3 4 * Equiv.swap 1 0 * Equiv.swap 0 2,
    Equiv.swap 1 3 * Equiv.swap 1 0 * Equiv.swap 0 2,
    Equiv.swap 1 4 * Equiv.swap 1 3 * Equiv.swap 1 0 * Equiv.swap 0 2,
    Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 1 0 * Equiv.swap 0 2,
    Equiv.swap 1 4 * Equiv.swap 1 0 * Equiv.swap 0 2,
    Equiv.swap 0 2,
    Equiv.swap 3 4 * Equiv.swap 0 2,
    Equiv.swap 0 3 * Equiv.swap 0 2,
    Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2,
    Equiv.swap 3 0 * Equiv.swap 0 4 * Equiv.swap 0 2,
    Equiv.swap 0 4 * Equiv.swap 0 2,
    Equiv.swap 1 3 * Equiv.swap 0 2,
    Equiv.swap 1 4 * Equiv.swap 1 3 * Equiv.swap 0 2,
    Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 0 2,
    Equiv.swap 0 4 * Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 0 2,
    Equiv.swap 1 0 * Equiv.swap 0 4 * Equiv.swap 1 3 * Equiv.swap 0 2,
    Equiv.swap 0 4 * Equiv.swap 1 3 * Equiv.swap 0 2,
    Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 0 2,
    Equiv.swap 1 4 * Equiv.swap 0 2,
    Equiv.swap 3 0 * Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 0 2,
    Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 0 2,
    Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 0 2,
    Equiv.swap 0 1 * Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 0 2,
    Equiv.swap 2 1 * Equiv.swap 1 0 * Equiv.swap 0 3,
    Equiv.swap 2 4 * Equiv.swap 2 1 * Equiv.swap 1 0 * Equiv.swap 0 3,
    Equiv.swap 1 0 * Equiv.swap 0 3,
    Equiv.swap 1 4 * Equiv.swap 1 0 * Equiv.swap 0 3,
    Equiv.swap 2 4 * Equiv.swap 1 0 * Equiv.swap 0 3,
    Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 1 0 * Equiv.swap 0 3,
    Equiv.swap 2 0 * Equiv.swap 0 3,
    Equiv.swap 2 4 * Equiv.swap 2 0 * Equiv.swap 0 3,
    Equiv.swap 0 3,
    Equiv.swap 0 4 * Equiv.swap 0 3,
    Equiv.swap 2 4 * Equiv.swap 0 3,
    Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 0 3,
    Equiv.swap 1 0 * Equiv.swap 1 2 * Equiv.swap 0 3,
    Equiv.swap 1 4 * Equiv.swap 1 0 * Equiv.swap 1 2 * Equiv.swap 0 3,
    Equiv.swap 1 2 * Equiv.swap 0 3,
    Equiv.swap 0 4 * Equiv.swap 1 2 * Equiv.swap 0 3,
    Equiv.swap 1 4 * Equiv.swap 1 2 * Equiv.swap 0 3,
    Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 1 2 * Equiv.swap 0 3,
    Equiv.swap 2 1 * Equiv.swap 2 0 * Equiv.swap 1 4 * Equiv.swap 0 3,
    Equiv.swap 2 0 * Equiv.swap 1 4 * Equiv.swap 0 3,
    Equiv.swap 2 1 * Equiv.swap 1 4 * Equiv.swap 0 3,
    Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 4 * Equiv.swap 0 3,
    Equiv.swap 1 4 * Equiv.swap 0 3,
    Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 0 3,
    Equiv.swap 3 2 * Equiv.swap 2 1 * Equiv.swap 1 0 * Equiv.swap 0 4,
    Equiv.swap 2 1 * Equiv.swap 1 0 * Equiv.swap 0 4,
    Equiv.swap 3 1 * Equiv.swap 1 0 * Equiv.swap 0 4,
    Equiv.swap 1 0 * Equiv.swap 0 4,
    Equiv.swap 2 1 * Equiv.swap 2 3 * Equiv.swap 1 0 * Equiv.swap 0 4,
    Equiv.swap 2 3 * Equiv.swap 1 0 * Equiv.swap 0 4,
    Equiv.swap 3 2 * Equiv.swap 2 0 * Equiv.swap 0 4,
    Equiv.swap 2 0 * Equiv.swap 0 4,
    Equiv.swap 3 0 * Equiv.swap 0 4,
    Equiv.swap 0 4,
    Equiv.swap 2 0 * Equiv.swap 2 3 * Equiv.swap 0 4,
    Equiv.swap 2 3 * Equiv.swap 0 4,
    Equiv.swap 3 1 * Equiv.swap 1 0 * Equiv.swap 1 2 * Equiv.swap 0 4,
    Equiv.swap 1 0 * Equiv.swap 1 2 * Equiv.swap 0 4,
    Equiv.swap 3 0 * Equiv.swap 1 2 * Equiv.swap 0 4,
    Equiv.swap 1 2 * Equiv.swap 0 4,
    Equiv.swap 1 0 * Equiv.swap 1 3 * Equiv.swap 1 2 * Equiv.swap 0 4,
    Equiv.swap 1 3 * Equiv.swap 1 2 * Equiv.swap 0 4,
    Equiv.swap 2 0 * Equiv.swap 1 3 * Equiv.swap 0 4,
    Equiv.swap 1 2 * Equiv.swap 2 0 * Equiv.swap 1 3 * Equiv.swap 0 4,
    Equiv.swap 2 0 * Equiv.swap 2 1 * Equiv.swap 1 3 * Equiv.swap 0 4,
    Equiv.swap 2 1 * Equiv.swap 1 3 * Equiv.swap 0 4,
    Equiv.swap 1 0 * Equiv.swap 1 3 * Equiv.swap 0 4,
    Equiv.swap 1 3 * Equiv.swap 0 4]

def perm (p : Label) : Perm := permutations5.getD p.val 1

private def rank (σ : Perm) : Label :=
  let a := (σ 0).val
  let b := (σ 1).val
  let c := (σ 2).val
  let d := (σ 3).val
  let q := 24*a + 6*(b - if a < b then 1 else 0) +
    2*(c - (if a < c then 1 else 0) - (if b < c then 1 else 0)) +
    (d - (if a < d then 1 else 0) - (if b < d then 1 else 0) - (if c < d then 1 else 0))
  ⟨q % 120, Nat.mod_lt _ (by decide)⟩

private theorem rank_perm : Function.LeftInverse rank perm := by
  change ∀ p : Label, rank (perm p) = p
  decide +kernel

def permEquiv : Label ≃ Perm where
  toFun := perm
  invFun := rank
  left_inv := rank_perm
  right_inv := rank_perm.rightInverse_of_surjective
    ((Finite.injective_iff_surjective_of_equiv
        (Fintype.equivOfCardEq (show Fintype.card Label = Fintype.card Perm by
          change Fintype.card (Fin 120) = Fintype.card (Equiv.Perm (Fin 5))
          rw [Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
          decide))).mp rank_perm.injective)

theorem permEquiv_apply (i : Label) : permEquiv i = perm i := rfl

end MOC.FivePermutations

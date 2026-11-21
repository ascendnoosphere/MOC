import MOC.Obstruction
import Mathlib.Data.Fintype.Perm

/-! Finite permutation data for the six-contact reduction in order four.
The zero set below is the nonminor facet used to seed the exceptional contact classes
in Zheng's order-four argument. -/

namespace MOC

open Finset

abbrev FourPerm := Equiv.Perm (Fin 4)

/-- The permutations in lexicographic order of their one-line images. -/
def fourPerm (i : Fin 24) : FourPerm :=
  ![1,
    Equiv.swap 2 3,
    Equiv.swap 1 2,
    Equiv.swap 1 3 * Equiv.swap 1 2,
    Equiv.swap 2 1 * Equiv.swap 1 3,
    Equiv.swap 1 3,
    Equiv.swap 0 1,
    Equiv.swap 2 3 * Equiv.swap 0 1,
    Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1,
    Equiv.swap 2 0 * Equiv.swap 0 3 * Equiv.swap 0 1,
    Equiv.swap 0 3 * Equiv.swap 0 1,
    Equiv.swap 1 0 * Equiv.swap 0 2,
    Equiv.swap 1 3 * Equiv.swap 1 0 * Equiv.swap 0 2,
    Equiv.swap 0 2,
    Equiv.swap 0 3 * Equiv.swap 0 2,
    Equiv.swap 1 3 * Equiv.swap 0 2,
    Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 0 2,
    Equiv.swap 2 1 * Equiv.swap 1 0 * Equiv.swap 0 3,
    Equiv.swap 1 0 * Equiv.swap 0 3,
    Equiv.swap 2 0 * Equiv.swap 0 3,
    Equiv.swap 0 3,
    Equiv.swap 1 0 * Equiv.swap 1 2 * Equiv.swap 0 3,
    Equiv.swap 1 2 * Equiv.swap 0 3] i

/-- Lehmer rank in the same lexicographic order. -/
def fourPermIndex (σ : FourPerm) : Fin 24 :=
  let a := (σ 0).val
  let b := (σ 1).val
  let c := (σ 2).val
  let k := 6 * a + 2 * (b - if a < b then 1 else 0) +
    (c - (if a < c then 1 else 0) - (if b < c then 1 else 0))
  ⟨k % 24, Nat.mod_lt _ (by decide)⟩

theorem fourPermIndex_fourPerm : Function.LeftInverse fourPermIndex fourPerm := by
  change ∀ i : Fin 24, fourPermIndex (fourPerm i) = i
  decide +kernel

theorem fourPerm_surjective : Function.Surjective fourPerm := by
  apply (Finite.injective_iff_surjective_of_equiv
    (Fintype.equivOfCardEq (show Fintype.card (Fin 24) = Fintype.card FourPerm by
      rw [Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
      decide))).mp
  exact fourPermIndex_fourPerm.injective

/-- A computable bridge between the numerical census and the actual matching permutations. -/
def fourPermEquiv : Fin 24 ≃ FourPerm where
  toFun := fourPerm
  invFun := fourPermIndex
  left_inv := fourPermIndex_fourPerm
  right_inv := fourPermIndex_fourPerm.rightInverse_of_surjective fourPerm_surjective

/-- Twice the reference nonminor facet h_(id,−1) on a permutation.
The integer version avoids division in the finite checks. -/
def referenceNonminorFacetTwice (σ : FourPerm) : ℤ :=
  (∑ i : Fin 4, if σ i = i then 1 else 0) -
    ((if (σ 0 = 0 ∧ σ 1 = 2) ∨ (σ 0 = 2 ∧ σ 1 = 0) ∨
        (σ 0 = 1 ∧ σ 1 = 3) ∨ (σ 0 = 3 ∧ σ 1 = 1) then 1 else 0) -
      (if (σ 0 = 0 ∧ σ 2 = 1) ∨ (σ 0 = 1 ∧ σ 2 = 0) ∨
        (σ 0 = 2 ∧ σ 2 = 3) ∨ (σ 0 = 3 ∧ σ 2 = 2) then 1 else 0))

/-- The integer mixed cost in the row-to-column convention of the existing obstruction. -/
private def mixedPermutationCostInt (σ : FourPerm) : ℤ :=
  (if σ 1 = 0 then 1 else 0) + (if σ 3 = 2 then 1 else 0) +
    (if (σ 2 = 0 ∧ σ 3 = 3) ∨ (σ 2 = 3 ∧ σ 3 = 0) then 1 else 0) -
    (if (σ 1 = 0 ∧ σ 2 = 1) ∨ (σ 1 = 1 ∧ σ 2 = 0) then 1 else 0)

private theorem referenceNonminorFacetTwice_mixed_int (σ : FourPerm) :
    referenceNonminorFacetTwice (σ * (Equiv.swap 0 1 * Equiv.swap 2 3)) =
      2 * mixedPermutationCostInt σ := by
  obtain ⟨i, rfl⟩ := fourPerm_surjective σ
  have h : ∀ i : Fin 24,
      referenceNonminorFacetTwice (fourPerm i * (Equiv.swap 0 1 * Equiv.swap 2 3)) =
        2 * mixedPermutationCostInt (fourPerm i) := by decide +kernel
  exact h i

/-- The reference nonminor facet is the same mixed cost already used in the obstruction,
after right multiplication by the disjoint swaps (01)(23). -/
theorem referenceNonminorFacetTwice_eq_mixed (σ : FourPerm) :
    (referenceNonminorFacetTwice (σ * (Equiv.swap 0 1 * Equiv.swap 2 3)) : ℝ) =
      2 * permutationCost σ := by
  have h := congrArg (Int.cast : ℤ → ℝ) (referenceNonminorFacetTwice_mixed_int σ)
  simpa only [mixedPermutationCostInt, permutationCost, Int.cast_mul, Int.cast_ofNat,
    Int.cast_add, Int.cast_sub, apply_ite, Int.cast_one, Int.cast_zero] using h

/-- The exact reference facet profile in lexicographic order. -/
theorem referenceNonminorFacetTwice_profile (i : Fin 24) :
    referenceNonminorFacetTwice (fourPerm i) =
      ![4, 2, 2, 0, 2, 2, 2, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 2, 0, 0] i := by
  exact (by decide +kernel :
      ∀ j : Fin 24, referenceNonminorFacetTwice (fourPerm j) =
        ![4, 2, 2, 0, 2, 2, 2, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 2, 0, 0] j) i

/-- The thirteen permutations at which the reference facet vanishes. -/
def referenceNonminorFacetZeroIndices : Finset (Fin 24) :=
  {3, 7, 9, 10, 11, 12, 13, 16, 17, 18, 20, 22, 23}

theorem mem_referenceNonminorFacetZeroIndices (i : Fin 24) :
    i ∈ referenceNonminorFacetZeroIndices ↔ referenceNonminorFacetTwice (fourPerm i) = 0 := by
  exact (by decide +kernel :
    ∀ j : Fin 24,
      j ∈ referenceNonminorFacetZeroIndices ↔ referenceNonminorFacetTwice (fourPerm j) = 0) i

/-- There are 1716 six-element subsets of the zero set of one reference nonminor facet. -/
theorem referenceNonminorFacetSixSeeds :
    (referenceNonminorFacetZeroIndices.powersetCard 6).card = 1716 := by
  rw [Finset.card_powersetCard]
  have h : referenceNonminorFacetZeroIndices.card = 13 := by decide +kernel
  rw [h]
  decide

end MOC

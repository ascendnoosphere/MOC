import MOC.Claim
import MOC.SparseRow
import MOC.FullSupportReduction
import MOC.Reformulations.Contacts
import MOC.ContactIteration

/-! Order-five consequences of a contact transfer that fixes the mixer.
The transfer premise is explicit; none of the statements below asserts it. -/

open Matrix

namespace MOC

/-- Every proper block split of a five-by-five mixer is covered by
order four and the proved cases of order at most three. -/
theorem holds_five_of_proper_paired_blocks
    (hfour : Conjecture (Fin 4)) (a b : Fin 5 → ℂ)
    {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : IsUnitary U) (hs : HasProperPairedBlocks U) :
    Holds a b U := by
  obtain ⟨m, k, eRow, eCol, V, W, hm, hk, hBlocks⟩ := hs
  have hcard := Fintype.card_congr eRow
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hsmall (s : ℕ) (hs : s ≤ 4) : Conjecture (Fin s) := by
    by_cases h : s = 4
    · subst s
      exact hfour
    · exact conjecture_le_three (by omega)
  exact holds_of_paired_blocks (hsmall m (by omega)) (hsmall k (by omega))
    eRow eCol a b U hU V W hBlocks

/-- Two blocks of orders at most three need no order-four result. -/
theorem holds_five_of_small_paired_blocks {m k : ℕ} (hm : m ≤ 3) (hk : k ≤ 3)
    (eRow eCol : Fin m ⊕ Fin k ≃ Fin 5) (a b : Fin 5 → ℂ)
    {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : IsUnitary U)
    (V : Matrix (Fin m) (Fin m) ℂ) (W : Matrix (Fin k) (Fin k) ℂ)
    (hBlocks : U.submatrix eRow eCol = fromBlocks V 0 0 W) : Holds a b U :=
  holds_of_paired_blocks (conjecture_le_three hm) (conjecture_le_three hk)
    eRow eCol a b U hU V W hBlocks

/-- If order four holds, an order-five failure has no proper paired block
split and every row and column has at least three nonzero entries. -/
theorem order_five_failure_structure (hfour : Conjecture (Fin 4)) (a b : Fin 5 → ℂ)
    {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : IsUnitary U) (hfail : ¬ Holds a b U) :
    ¬ HasProperPairedBlocks U ∧
      (∀ i, 3 ≤ (supportColumns U {i}).card) ∧
      (∀ j, 3 ≤ (supportColumns Uᴴ {j}).card) := by
  refine ⟨fun h => hfail (holds_five_of_proper_paired_blocks hfour a b hU h), ?_, ?_⟩
  · intro i
    by_contra hi
    exact hfail (holds_of_row_degree_le_two hfour a b hU i (by omega))
  · intro j
    by_contra hj
    exact hfail (holds_of_column_degree_le_two hfour a b hU j (by omega))

/-- The order-five contact test for mixers whose entries are all nonzero.
The contacts count permutations, even if their matching products coincide. -/
def FullSupportEightContactTest : Prop :=
  ∀ (a b : Fin 5 → ℂ) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (η : ℂ) (p : Equiv.Perm (Fin 5)), IsUnitary U → (∀ i j, U i j ≠ 0) →
    (∀ q, (η * matchingProduct a b q).re ≤ (η * matchingProduct a b p).re) →
    8 ≤ (Finset.univ.filter fun q : Equiv.Perm (Fin 5) =>
      (η * matchingProduct a b q).re = (η * matchingProduct a b p).re).card →
    (η * determinantValue a b U).re ≤ (η * matchingProduct a b p).re

/-- A contact transfer that fixes the mixer turns the eight-contact test
into an exact order-five criterion. Full support is imposed before the
transfer, so no perturbation of the final contact equalities is needed. -/
theorem conjecture_five_iff_fullSupportEight_of_transfer
    (transfer : ∀ (U : Matrix (Fin 5) (Fin 5) ℂ), IsUnitary U →
      (∃ a b : Fin 5 → ℂ, ¬ Holds a b U) →
      ∃ (a b : Fin 5 → ℂ) (η : ℂ) (p : Equiv.Perm (Fin 5)),
        (∀ q, (η * matchingProduct a b q).re ≤ (η * matchingProduct a b p).re) ∧
        8 ≤ (Finset.univ.filter fun q : Equiv.Perm (Fin 5) =>
          (η * matchingProduct a b q).re = (η * matchingProduct a b p).re).card ∧
        (η * matchingProduct a b p).re < (η * determinantValue a b U).re) :
    Conjecture (Fin 5) ↔ FullSupportEightContactTest := by
  constructor
  · intro h a b U η p hU _ hmax hcount
    exact Reformulations.contactForm_of_conjecture h a b U η p hU hmax hcount
  · intro h a b U hU
    apply (holds_all_unitaries_iff_full_support a b).mpr _ U hU
    intro V hV hfull
    by_contra hbad
    obtain ⟨a', b', η, p, hmax, hcount, hstrict⟩ := transfer V hV ⟨a, b, hbad⟩
    exact (not_le_of_gt hstrict) (h a' b' V η p hV hfull hmax hcount)

/-- A failure on a proper block or on a mixer with a row or column of
degree at most two implies a failure in order four. -/
theorem not_conjecture_four_of_sparse_five_failure (a b : Fin 5 → ℂ)
    {U : Matrix (Fin 5) (Fin 5) ℂ} (hU : IsUnitary U) (hfail : ¬ Holds a b U)
    (hs : HasProperPairedBlocks U ∨ (∃ i, (supportColumns U {i}).card ≤ 2) ∨
      ∃ j, (supportColumns Uᴴ {j}).card ≤ 2) : ¬ Conjecture (Fin 4) := by
  intro hfour
  obtain ⟨hblocks, hrows, hcols⟩ := order_five_failure_structure hfour a b hU hfail
  rcases hs with h | ⟨i, hi⟩ | ⟨j, hj⟩
  · exact hblocks h
  · exact (not_le_of_gt (hrows i)) hi
  · exact (not_le_of_gt (hcols j)) hj

/-- It is enough to construct a single additional contact, and only for
mixers with no zero entries. The finite iteration is independent of the
geometric step. -/
theorem conjecture_five_iff_fullSupportEight_of_step
    (step : ∀ (U : Matrix (Fin 5) (Fin 5) ℂ), IsUnitary U →
      (∀ i j, U i j ≠ 0) → ∀ v : StrictMatchingSupport U, v.contacts.card < 8 →
        ∃ v' : StrictMatchingSupport U, v.contacts.card < v'.contacts.card) :
    Conjecture (Fin 5) ↔ FullSupportEightContactTest := by
  constructor
  · intro h a b U η p hU _ hmax hcount
    exact Reformulations.contactForm_of_conjecture h a b U η p hU hmax hcount
  · intro h a b U hU
    apply (holds_all_unitaries_iff_full_support a b).mpr _ U hU
    intro V hV hfull
    by_contra hbad
    obtain ⟨w⟩ := nonempty_strictMatchingSupport_of_failure a b hbad
    obtain ⟨v, hv⟩ := exists_strictMatchingSupport_at_least 8 w (step V hV hfull)
    apply (not_le_of_gt v.strict)
    exact h v.a v.b V v.η v.pivot hV hfull v.maximal hv

end MOC

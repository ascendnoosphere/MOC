import MOC.Claim
import MOC.SinglePortZeroCorner
import MOC.SupportBlocks

/-! A least-order counterexample must have additive-two support expansion. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem mem_compl_supportColumns_iff (U : Matrix ι ι ℂ)
    (R : Finset ι) (j : ι) :
    j ∈ (supportColumns U R)ᶜ ↔ ∀ i ∈ R, U i j = 0 := by
  classical
  simp [supportColumns]

/-- Every nonempty row set of size at most `n - 2` has at least two
more supporting columns than rows if and only if no nonempty zero
rectangle has row and column sizes summing to `n - 1`.
This equivalence does not require the matrix to be unitary. -/
theorem additiveTwoSupportExpansion_iff_no_zero_rectangle (U : Matrix ι ι ℂ) :
    (∀ R : Finset ι, R.Nonempty → R.card + 2 ≤ Fintype.card ι →
      R.card + 2 ≤ (supportColumns U R).card) ↔
    ¬ ∃ R C : Finset ι, R.Nonempty ∧ C.Nonempty ∧
      R.card + C.card = Fintype.card ι - 1 ∧ ∀ i ∈ R, ∀ j ∈ C, U i j = 0 := by
  constructor
  · intro h ⟨R, C, hR, hC, hsize, hzero⟩
    have hCpos := Finset.card_pos.mpr hC
    have hRbound : R.card + 2 ≤ Fintype.card ι := by omega
    have hN := h R hR hRbound
    have hCsub : C ⊆ (supportColumns U R)ᶜ := fun j hj =>
      (mem_compl_supportColumns_iff U R j).mpr fun i hi => hzero i hi j hj
    have hCbound := Finset.card_le_card hCsub
    rw [Finset.card_compl] at hCbound
    omega
  · intro h R hR hRbound
    by_contra! hN
    have hCbound : Fintype.card ι - 1 - R.card ≤ ((supportColumns U R)ᶜ).card := by
      rw [Finset.card_compl]
      omega
    obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hCbound
    have hC : C.Nonempty := Finset.card_pos.mp (by omega)
    exact h ⟨R, C, hR, hC, by omega, fun i hi j hj =>
      (mem_compl_supportColumns_iff U R j).mp (hCsub hj) i hi⟩

/-- For a failure in an order where all smaller orders satisfy the conjecture,
every nonempty row set with at least two rows outside it has at least two more
supporting columns than rows. -/
theorem additive_two_support_expansion_of_failure {n : ℕ}
    (hbelow : ∀ m < n, Conjecture (Fin m)) (a b : Fin n → ℂ)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U) (hfail : ¬ Holds a b U) :
    ∀ R : Finset (Fin n), R.Nonempty → R.card + 2 ≤ n →
      R.card + 2 ≤ (supportColumns U R).card := by
  have hnone := (additiveTwoSupportExpansion_iff_no_zero_rectangle U).mpr ?_
  · simpa only [Fintype.card_fin] using hnone
  rintro ⟨R, C, hR, hC, hsize, hz⟩
  rw [Fintype.card_fin] at hsize
  have hRpos := Finset.card_pos.mpr hR
  have hCpos := Finset.card_pos.mpr hC
  have hdim : R.card + C.card + 1 = Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  have hleft : C.card + 1 < n := by omega
  have hright : R.card + 1 < n := by omega
  exact hfail (holds_of_singlePort_zero_rectangle a b hU R C hdim hz
    (hbelow _ hleft) (hbelow _ hright))

/-- It suffices to prove the conjecture on mixers with additive-two support
expansion on nonempty row sets of size at most `n - 2`. -/
theorem mocIsTrue_iff_additive_two_support_expansion :
    MOCIsTrue ↔ ∀ (n : ℕ), 4 ≤ n → ∀ (a b : Fin n → ℂ)
      (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      (∀ R : Finset (Fin n), R.Nonempty → R.card + 2 ≤ n →
        R.card + 2 ≤ (supportColumns U R).card) → Holds a b U := by
  constructor
  · intro h n _ a b U hU _
    exact h n a b U hU
  · intro h
    by_contra hbad
    obtain ⟨n, hn, hbelow, a, b, U, hU, hfail, _⟩ := exists_least_bad_instance hbad
    exact hfail (h n hn a b U hU (additive_two_support_expansion_of_failure hbelow a b hU hfail))

end MOC

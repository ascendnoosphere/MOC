import MOC.SparseUnitary
import MOC.SupportCardinalityDeletion

/-! A bound on the total number of nonzero entries in a relative unitary
suffices for the Marcus–de Oliveira inclusion. -/

open Matrix BigOperators

namespace MOC

/-- Count the nonzero entries by their matrix positions. -/
theorem supportEntryCount_eq_card_nonzero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) : supportEntryCount U =
      (Finset.univ.filter (fun p : ι × ι => U p.1 p.2 ≠ 0)).card := by
  classical
  have h (i : ι) : (supportColumns U {i}).card =
      ∑ j, if U i j ≠ 0 then 1 else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext j
    simp [supportColumns]
  change (∑ i, (supportColumns U {i}).card) = _
  simp_rw [h]
  rw [← Fintype.sum_prod_type' (fun i j => if U i j ≠ 0 then 1 else 0)]
  rw [Finset.sum_boole]
  congr 1

private theorem holds_of_supportEntryCount_fin :
    ∀ n (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary U → supportEntryCount U ≤ n + 8 → Holds a b U := by
  intro n
  induction n with
  | zero => exact fun a b U hu _ => conjecture_zero a b U hu
  | succ n ih =>
    intro a b U hU hcount
    by_cases hs : n + 1 ≤ 3
    · exact conjecture_le_three hs a b U hU
    by_cases hlow : ∃ i, (supportColumns U {i}).card ≤ 2
    · obtain ⟨i, hi⟩ := hlow
      apply holds_of_row_degree_le_two_of_minors a b hU i hi
      intro p q hp hV
      apply ih _ _ _ hV
      have hdrop := supportEntryCount_normalizedSparseRowMinor_add_one_le i p q hp
      omega
    have hbase (i : Fin (n + 1)) : 3 ≤ (supportColumns U {i}).card := by
      have h : ¬ (supportColumns U {i}).card ≤ 2 := fun hi => hlow ⟨i, hi⟩
      omega
    apply holds_of_row_degree_le_three a b hU
    intro r
    by_contra! hr
    have ht : (∑ _ : Fin (n + 1), 3) < supportEntryCount U :=
      Finset.sum_lt_sum (fun i _ => hbase i) ⟨r, Finset.mem_univ _, hr⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at ht
    omega

/-- In every finite order, at most eight nonzero entries in excess of the
order suffice for the determinant inclusion. -/
theorem holds_of_supportEntryCount_le_card_add_eight
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℂ) {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hcount : supportEntryCount U ≤ Fintype.card ι + 8) :
    Holds a b U := by
  classical
  let e := (Fintype.equivFin ι).symm
  apply (holds_reindex_iff e e a b U).mp
  apply holds_of_supportEntryCount_fin _ _ _ _ (unitary_reindex e e hU)
  refine le_trans ?_ hcount
  rw [supportEntryCount_eq_card_nonzero, supportEntryCount_eq_card_nonzero]
  let ep := Equiv.prodCongr e e
  apply Finset.card_le_card_of_injOn ep _ ep.injective.injOn
  intro p hp
  simpa [ep, Matrix.submatrix_apply] using hp

/-- Four zero entries in any positions suffice in order four. -/
theorem four_holds_of_four_zero_entries
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hfour : Fintype.card ι = 4)
    (a b : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (hzero : 4 ≤ (Finset.univ.filter (fun p : ι × ι => U p.1 p.2 = 0)).card) :
    Holds a b U := by
  apply holds_of_supportEntryCount_le_card_add_eight a b hU
  rw [supportEntryCount_eq_card_nonzero, hfour]
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (ι × ι))) (fun p => U p.1 p.2 = 0)
  rw [Finset.card_univ, Fintype.card_prod, hfour] at h
  have heq : (Finset.univ.filter (fun p : ι × ι => U p.1 p.2 = 0)).card +
      (Finset.univ.filter (fun p : ι × ι => U p.1 p.2 ≠ 0)).card = 16 := by
    convert h using 1
  omega

end MOC

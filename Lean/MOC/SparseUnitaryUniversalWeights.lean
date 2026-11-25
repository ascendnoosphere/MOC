import MOC.PairedBlockUniversalWeights
import MOC.SparseRowUniversalWeights
import MOC.SparseSupportCardinality

/-! Universal matching distributions for sparse relative unitaries. -/

open Matrix BigOperators

namespace MOC

private theorem unitary_adjoint_of_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) : IsUnitary Uᴴ :=
  ⟨by simpa only [conjTranspose_conjTranspose] using hU.2,
   by simpa only [conjTranspose_conjTranspose] using hU.1⟩

/-- An order-four unitary of degree three has a matching law for all spectra. -/
theorem four_universalMatchingWeights_of_support_degrees_three
    {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (hr : ∀ i, (supportColumns U {i}).card = 3)
    (hc : ∀ j, (supportColumns Uᴴ {j}).card = 3) : HasUniversalMatchingWeights U := by
  obtain ⟨σ, hσ⟩ := four_exists_zero_permutation_of_support_degrees_three hr hc
  apply (hasUniversalMatchingWeights_reindex_iff (Equiv.refl _) σ U).mp
  let V := U.submatrix (Equiv.refl _) σ
  have hV : IsUnitary V := unitary_reindex (Equiv.refl _) σ hU
  apply hasUniversalMatchingWeights_of_nonneg_realSignedWeight hV
  apply four_realSignedWeight_nonneg_of_zero_diagonal_of_offDiagonal_ne_zero hV
  · intro i
    exact (hσ i _).mpr rfl
  · intro i j hne hz
    exact hne (σ.injective ((hσ i _).mp hz)).symm

private theorem universalMatchingWeights_of_row_degree_le_three_fin :
    ∀ n (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      (∀ r, (supportColumns U {r}).card ≤ 3) → HasUniversalMatchingWeights U := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U hU hdeg
    by_cases hsmall : n ≤ 3
    · exact hasUniversalMatchingWeights_of_card_le_three hU (by simpa using hsmall)
    cases n with
    | zero => omega
    | succ n =>
      by_cases hcol : ∃ j, (supportColumns Uᴴ {j}).card ≤ 2
      · obtain ⟨j, hj⟩ := hcol
        apply (hasUniversalMatchingWeights_adjoint_iff hU).mp
        apply hasUniversalMatchingWeights_of_row_degree_le_two_of_minors
          (unitary_adjoint_of_unitary hU) j hj
        intro p q _ hV
        apply (hasUniversalMatchingWeights_adjoint_iff hV).mp
        apply ih n (Nat.lt_succ_self n) _ (unitary_adjoint_of_unitary hV)
        intro s
        have hs := columnSupportDegree_normalizedSparseRowMinor_le (U := Uᴴ) j p q s
        rw [Matrix.conjTranspose_conjTranspose] at hs
        exact hs.trans (hdeg _)
      have hmin (j : Fin (n + 1)) : 3 ≤ (supportColumns Uᴴ {j}).card := by
        have hnot : ¬ (supportColumns Uᴴ {j}).card ≤ 2 := fun hj => hcol ⟨j, hj⟩
        omega
      obtain ⟨hr, hc⟩ := supportDegrees_eq_of_row_le_of_column_ge 3 hdeg hmin
      by_cases hblocks : HasProperPairedBlocks U
      · exact universal_matching_weights_of_proper_paired_blocks ih hU hdeg hblocks
      have hn := cubic_order_le_four_of_no_paired_blocks hU hr hc hblocks
      have heq : n = 3 := by omega
      subst n
      exact four_universalMatchingWeights_of_support_degrees_three hU hr hc

/-- One distribution represents every pair of spectra if each row has at
most three nonzero entries. -/
theorem hasUniversalMatchingWeights_of_row_degree_le_three
    {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hrows : ∀ r, (supportColumns U {r}).card ≤ 3) :
    HasUniversalMatchingWeights U := by
  classical
  let e := (Fintype.equivFin ι).symm
  apply (hasUniversalMatchingWeights_reindex_iff e e U).mp
  apply universalMatchingWeights_of_row_degree_le_three_fin _ _ (unitary_reindex e e hU)
  intro r
  refine le_trans ?_ (hrows (e r))
  apply Finset.card_le_card_of_injOn e _ e.injective.injOn
  intro j hj
  simpa [supportColumns, Matrix.submatrix_apply] using hj

/-- One distribution also suffices under the column degree bound alone. -/
theorem hasUniversalMatchingWeights_of_column_degree_le_three
    {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hcols : ∀ c, (supportColumns Uᴴ {c}).card ≤ 3) :
    HasUniversalMatchingWeights U :=
  (hasUniversalMatchingWeights_adjoint_iff hU).mp
    (hasUniversalMatchingWeights_of_row_degree_le_three (unitary_adjoint_of_unitary hU) hcols)

private theorem universalMatchingWeights_of_supportEntryCount_fin :
    ∀ n (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      supportEntryCount U ≤ n + 8 → HasUniversalMatchingWeights U := by
  intro n
  induction n with
  | zero => exact fun U hU _ => hasUniversalMatchingWeights_of_card_le_three hU (by decide)
  | succ n ih =>
    intro U hU hcount
    by_cases hs : n + 1 ≤ 3
    · exact hasUniversalMatchingWeights_of_card_le_three hU (by simpa using hs)
    by_cases hlow : ∃ i, (supportColumns U {i}).card ≤ 2
    · obtain ⟨i, hi⟩ := hlow
      apply hasUniversalMatchingWeights_of_row_degree_le_two_of_minors hU i hi
      intro p q hp hV
      apply ih _ hV
      have hdrop := supportEntryCount_normalizedSparseRowMinor_add_one_le i p q hp
      omega
    have hbase (i : Fin (n + 1)) : 3 ≤ (supportColumns U {i}).card := by
      have h : ¬ (supportColumns U {i}).card ≤ 2 := fun hi => hlow ⟨i, hi⟩
      omega
    apply hasUniversalMatchingWeights_of_row_degree_le_three hU
    intro r
    by_contra! hr
    have ht : (∑ _ : Fin (n + 1), 3) < supportEntryCount U :=
      Finset.sum_lt_sum (fun i _ => hbase i) ⟨r, Finset.mem_univ _, hr⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at ht
    omega

/-- A single matching law suffices if the number of nonzero entries
exceeds the order by at most eight. -/
theorem hasUniversalMatchingWeights_of_supportEntryCount_le_card_add_eight
    {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hcount : supportEntryCount U ≤ Fintype.card ι + 8) :
    HasUniversalMatchingWeights U := by
  classical
  let e := (Fintype.equivFin ι).symm
  apply (hasUniversalMatchingWeights_reindex_iff e e U).mp
  apply universalMatchingWeights_of_supportEntryCount_fin _ _ (unitary_reindex e e hU)
  refine le_trans ?_ hcount
  rw [supportEntryCount_eq_card_nonzero, supportEntryCount_eq_card_nonzero]
  let ep := Equiv.prodCongr e e
  apply Finset.card_le_card_of_injOn ep _ ep.injective.injOn
  intro p hp
  simpa [ep, Matrix.submatrix_apply] using hp

/-- In order four, four zero entries anywhere suffice for one matching
law that works for all spectra. -/
theorem four_hasUniversalMatchingWeights_of_four_zero_entries
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hfour : Fintype.card ι = 4)
    {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (hzero : 4 ≤ (Finset.univ.filter (fun p : ι × ι => U p.1 p.2 = 0)).card) :
    HasUniversalMatchingWeights U := by
  apply hasUniversalMatchingWeights_of_supportEntryCount_le_card_add_eight hU
  rw [supportEntryCount_eq_card_nonzero, hfour]
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (ι × ι))) (fun p => U p.1 p.2 = 0)
  rw [Finset.card_univ, Fintype.card_prod, hfour] at h
  have heq : (Finset.univ.filter (fun p : ι × ι => U p.1 p.2 = 0)).card +
      (Finset.univ.filter (fun p : ι × ι => U p.1 p.2 ≠ 0)).card = 16 := by
    convert h using 1
  omega

end MOC

import MOC.CubicSupportCut
import MOC.SparsePairedBlocks

/-! The Marcus–de Oliveira inclusion for unitary matrices with at most
three nonzero entries in every row or at most three in every column. -/

open Matrix

namespace MOC

/-- Every relative eigenbasis of support degree at most three satisfies
the Marcus–de Oliveira inclusion, for arbitrary spectra and orders. -/
theorem holds_of_support_degrees_le_three : ∀ n, SupportDegreeLEThreeConjecture n := by
  apply holds_of_supportDegreeLEThree_of_exact_three
  intro n hbelow a b U hU hrows hcols
  by_cases hblocks : HasProperPairedBlocks U
  · exact holds_sparse_of_proper_paired_blocks hbelow a b hU
      ⟨fun r => (hrows r).le, fun c => (hcols c).le⟩ hblocks
  have hn := cubic_order_le_four_of_no_paired_blocks hU hrows hcols hblocks
  by_cases hsmall : n ≤ 3
  · exact conjecture_le_three hsmall a b U hU
  have heq : n = 4 := by omega
  subst n
  exact four_holds_of_support_degrees_three a b hU hrows hcols

/-- A bound of three nonzero entries in each row suffices, in every order. -/
theorem holds_of_row_degree_le_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (hrows : ∀ r, (supportColumns U {r}).card ≤ 3) : Holds a b U := by
  classical
  let e := (Fintype.equivFin ι).symm
  apply (holds_reindex_iff e e a b U).mp
  apply holds_of_rowSupportDegreeLEThree_of_exact_three
    (fun n _ a b V hV hr hc => holds_of_support_degrees_le_three n a b V hV
      ⟨fun r => (hr r).le, fun c => (hc c).le⟩)
    _ _ _ _ (unitary_reindex e e hU)
  intro r
  refine le_trans ?_ (hrows (e r))
  apply Finset.card_le_card_of_injOn e _ e.injective.injOn
  intro j hj
  simpa [supportColumns, Matrix.submatrix_apply] using hj

/-- The corresponding column bound follows by exchanging the two spectra. -/
theorem holds_of_column_degree_le_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (hcols : ∀ c, (supportColumns Uᴴ {c}).card ≤ 3) : Holds a b U := by
  apply (holds_swap_iff a b hU).mp
  exact holds_of_row_degree_le_three b a
    ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
     by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩ hcols

/-- Every failure of the inclusion requires both a row and a column with
at least four nonzero entries. -/
theorem exists_row_and_column_degree_ge_four_of_not_holds
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℂ)
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (hfail : ¬ Holds a b U) :
    (∃ r, 4 ≤ (supportColumns U {r}).card) ∧
      (∃ c, 4 ≤ (supportColumns Uᴴ {c}).card) := by
  constructor
  · by_contra! h
    exact hfail (holds_of_row_degree_le_three a b hU (fun r => by have := h r; omega))
  · by_contra! h
    exact hfail (holds_of_column_degree_le_three a b hU (fun c => by have := h c; omega))

/-- In order four, a failure requires both a full row and a full column. -/
theorem four_exists_full_row_and_column_of_not_holds
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hfour : Fintype.card ι = 4)
    (a b : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U) (hfail : ¬ Holds a b U) :
    (∃ r, ∀ j, U r j ≠ 0) ∧ (∃ c, ∀ i, U i c ≠ 0) := by
  obtain ⟨⟨r, hr⟩, ⟨c, hc⟩⟩ := exists_row_and_column_degree_ge_four_of_not_holds a b hU hfail
  have full (S : Finset ι) (h : 4 ≤ S.card) : S = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rwa [Finset.card_univ, hfour]
  constructor
  · refine ⟨r, fun j => mem_supportColumns_singleton.mp ?_⟩
    rw [full _ hr]
    exact Finset.mem_univ _
  · refine ⟨c, fun i => mem_adjoint_supportColumns_singleton.mp ?_⟩
    rw [full _ hc]
    exact Finset.mem_univ _

end MOC

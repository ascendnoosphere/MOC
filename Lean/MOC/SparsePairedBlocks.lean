import MOC.SparseDegreeInduction
import MOC.OrderFourZeroDiagonalUnitary

open Matrix

namespace MOC

private theorem supportColumns_singleton_card_submatrix
    {m n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (r c : Fin m → Fin n) (hc : Function.Injective c) (i : Fin m) :
    (supportColumns (U.submatrix r c) {i}).card ≤
      (supportColumns U {r i}).card := by
  classical
  refine Finset.card_le_card_of_injOn c (fun j hj => ?_) hc.injOn
  simpa [supportColumns, submatrix_apply] using hj

private theorem supportDegreeLEThree_submatrix {m n : ℕ}
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : SupportDegreeLEThree U)
    (r c : Fin m → Fin n) (hr : Function.Injective r) (hc : Function.Injective c) :
    SupportDegreeLEThree (U.submatrix r c) := by
  refine ⟨fun i => (supportColumns_singleton_card_submatrix r c hc i).trans (hU.1 _), ?_⟩
  intro j
  rw [Matrix.conjTranspose_submatrix]
  exact (supportColumns_singleton_card_submatrix c r hr j).trans (hU.2 _)

/-- A proper paired block split preserves the degree bound and reduces the order. -/
theorem holds_sparse_of_proper_paired_blocks {n : ℕ}
    (hbelow : ∀ m < n, SupportDegreeLEThreeConjecture m)
    (a b : Fin n → ℂ) {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitary U) (hsparse : SupportDegreeLEThree U)
    (hblocks : HasProperPairedBlocks U) : Holds a b U := by
  obtain ⟨m, k, eRow, eCol, V, W, hm, hk, hsplit⟩ := hblocks
  obtain ⟨hm', hk'⟩ := paired_block_orders_lt eRow hm hk
  have hVeq : U.submatrix (eRow ∘ Sum.inl) (eCol ∘ Sum.inl) = V := by
    ext i j : 1
    exact congrFun (congrFun hsplit (.inl i)) (.inl j)
  have hWeq : U.submatrix (eRow ∘ Sum.inr) (eCol ∘ Sum.inr) = W := by
    ext i j : 1
    exact congrFun (congrFun hsplit (.inr i)) (.inr j)
  have hV := supportDegreeLEThree_submatrix hsparse _ _
    (eRow.injective.comp Sum.inl_injective) (eCol.injective.comp Sum.inl_injective)
  have hW := supportDegreeLEThree_submatrix hsparse _ _
    (eRow.injective.comp Sum.inr_injective) (eCol.injective.comp Sum.inr_injective)
  rw [hVeq] at hV
  rw [hWeq] at hW
  have hUnitary := unitary_reindex eRow eCol hU
  rw [hsplit] at hUnitary
  obtain ⟨hVU, hWU⟩ := unitary_directSum_iff.mp hUnitary
  have hsplitSpectrum (f : Fin n → ℂ) (e : Fin m ⊕ Fin k ≃ Fin n) :
      Sum.elim (f ∘ e ∘ Sum.inl) (f ∘ e ∘ Sum.inr) = f ∘ e := by
    funext i
    cases i <;> rfl
  apply (holds_reindex_iff eRow eCol a b U).mp
  rw [hsplit, ← hsplitSpectrum a eRow, ← hsplitSpectrum b eCol]
  exact holds_directSum _ _ _ _ _ _ (hbelow m hm' _ _ V hVU hV) (hbelow k hk' _ _ W hWU hW)

/-- A permutation of zero entries can be moved to the diagonal by relabeling the columns. -/
theorem four_holds_of_zero_matching (a b : Fin 4 → ℂ)
    {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (σ : Equiv.Perm (Fin 4)) (hz : ∀ i, U i (σ i) = 0) :
    Holds a b U :=
  (holds_reindex_iff (Equiv.refl _) σ a b U).mp
    (four_holds_zero_diagonal_unitary _ _ (unitary_reindex (Equiv.refl _) σ hU) hz)

/-- At order four, degree three in every row and column supplies a permutation of zeros. -/
theorem four_holds_of_support_degrees_three (a b : Fin 4 → ℂ)
    {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U)
    (hr : ∀ i, (supportColumns U {i}).card = 3)
    (hc : ∀ j, (supportColumns Uᴴ {j}).card = 3) : Holds a b U := by
  classical
  have hrone (i : Fin 4) : ∃ j, (supportColumns U {i})ᶜ = {j} := by
    apply Finset.card_eq_one.mp
    rw [Finset.card_compl, hr, Fintype.card_fin]
  have hcone (j : Fin 4) : ∃ i, (supportColumns Uᴴ {j})ᶜ = {i} := by
    apply Finset.card_eq_one.mp
    rw [Finset.card_compl, hc, Fintype.card_fin]
  choose f hf using hrone
  have hz (i : Fin 4) : U i (f i) = 0 := by
    have hmem : f i ∈ (supportColumns U {i})ᶜ := by rw [hf]; simp
    simpa [supportColumns] using hmem
  have hinj : Function.Injective f := by
    intro i i' heq
    obtain ⟨r, hr⟩ := hcone (f i)
    have hm : i ∈ (supportColumns Uᴴ {f i})ᶜ := by
      simp [supportColumns, Matrix.conjTranspose_apply, hz i]
    have hm' : i' ∈ (supportColumns Uᴴ {f i})ᶜ := by
      simp [supportColumns, Matrix.conjTranspose_apply, heq, hz i']
    rw [hr, Finset.mem_singleton] at hm hm'
    exact hm.trans hm'.symm
  exact four_holds_of_zero_matching a b hU
    (Equiv.ofBijective f ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩) hz

end MOC

import MOC.Blocks
import Mathlib.Logic.Equiv.Fin.Basic

/-! The verified orders through three and the block cases they imply. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
private theorem matchingProduct_reindex (eRow eCol : κ ≃ ι) (a b : ι → ℂ)
    (σ : Equiv.Perm κ) :
    matchingProduct (a ∘ eRow) (b ∘ eCol) σ =
      matchingProduct a b ((eCol.symm.trans σ).trans eRow) := by
  unfold matchingProduct
  rw [← Equiv.prod_comp eCol (fun j => a (((eCol.symm.trans σ).trans eRow) j) + b j)]
  simp

theorem determinantValue_reindex (eRow eCol : κ ≃ ι) (a b : ι → ℂ) (U : Matrix ι ι ℂ) :
    determinantValue (a ∘ eRow) (b ∘ eCol) (U.submatrix eRow eCol) =
      determinantValue a b U := by
  unfold determinantValue
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_diagonal_equiv a eRow,
    ← Matrix.submatrix_diagonal_equiv b eCol, Matrix.submatrix_mul_equiv _ _ eRow eCol eCol,
    Matrix.submatrix_mul_equiv _ _ eRow eCol eRow]
  exact Matrix.det_submatrix_equiv_self eRow (diagonal a + U * diagonal b * Uᴴ)

theorem unitary_reindex (eRow eCol : κ ≃ ι) {U : Matrix ι ι ℂ} (hU : IsUnitary U) :
    IsUnitary (U.submatrix eRow eCol) := by
  constructor
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ eRow eCol eRow,
      hU.1, Matrix.submatrix_one_equiv]
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ eCol eRow eCol,
      hU.2, Matrix.submatrix_one_equiv]

/-- The determinant hull condition is invariant under separate relabeling of the two spectra. -/
theorem holds_reindex_iff (eRow eCol : κ ≃ ι) (a b : ι → ℂ) (U : Matrix ι ι ℂ) :
    Holds (a ∘ eRow) (b ∘ eCol) (U.submatrix eRow eCol) ↔ Holds a b U := by
  have hrange : Set.range (matchingProduct (a ∘ eRow) (b ∘ eCol)) =
      Set.range (matchingProduct a b) := by
    ext z
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨_, (matchingProduct_reindex eRow eCol a b σ).symm⟩
    · rintro ⟨σ, rfl⟩
      refine ⟨(eCol.trans σ).trans eRow.symm, ?_⟩
      rw [matchingProduct_reindex]
      congr 1
      ext j
      simp
  unfold Holds
  rw [determinantValue_reindex, hrange]

theorem conjecture_reindex_iff (e : κ ≃ ι) : Conjecture κ ↔ Conjecture ι := by
  constructor
  · intro h a b U hU
    exact (holds_reindex_iff e e a b U).mp (h _ _ _ (unitary_reindex e e hU))
  · intro h a b U hU
    exact (holds_reindex_iff e.symm e.symm a b U).mp (h _ _ _ (unitary_reindex e.symm e.symm hU))

theorem conjecture_le_three {n : ℕ} (h : n ≤ 3) : Conjecture (Fin n) := by
  have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn with rfl | rfl | rfl | rfl
  · exact conjecture_zero
  · exact conjecture_one
  · exact conjecture_two
  · exact conjecture_three

theorem conjecture_of_card_le_three (h : Fintype.card ι ≤ 3) : Conjecture ι :=
  (conjecture_reindex_iff (Fintype.equivFin ι)).mpr (conjecture_le_three h)

/-- Paired blocks remain covered after independent relabeling of the two spectra. -/
theorem holds_reindexed_blocks_of_conjectures {η : Type*} [Fintype η] [DecidableEq η]
    (hι : Conjecture ι) (hκ : Conjecture κ) (eRow eCol : η ≃ ι ⊕ κ)
    (a b : ι → ℂ) (c d : κ → ℂ) (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V) :
    Holds (Sum.elim a c ∘ eRow) (Sum.elim b d ∘ eCol)
      ((fromBlocks U 0 0 V).submatrix eRow eCol) :=
  (holds_reindex_iff eRow eCol _ _ _).mpr
    (holds_blocks_of_conjectures hι hκ a b c d U V hU hV)

/-- A paired block split can be recognized directly in an existing eigenbasis. -/
theorem holds_of_paired_blocks {η : Type*} [Fintype η] [DecidableEq η]
    (hι : Conjecture ι) (hκ : Conjecture κ) (eRow eCol : ι ⊕ κ ≃ η)
    (a b : η → ℂ) (U : Matrix η η ℂ) (hU : IsUnitary U)
    (V : Matrix ι ι ℂ) (W : Matrix κ κ ℂ)
    (hBlocks : U.submatrix eRow eCol = fromBlocks V 0 0 W) : Holds a b U := by
  have hUnitary : IsUnitary (fromBlocks V 0 0 W) := hBlocks ▸ unitary_reindex eRow eCol hU
  obtain ⟨hV, hW⟩ := unitary_directSum_iff.mp hUnitary
  have hsplit (f : η → ℂ) (e : ι ⊕ κ ≃ η) :
      Sum.elim (fun i => f (e (.inl i))) (fun j => f (e (.inr j))) = f ∘ e := by
    funext x
    cases x <;> rfl
  apply (holds_reindex_iff eRow eCol a b U).mp
  rw [hBlocks, ← hsplit a eRow, ← hsplit b eCol]
  exact holds_blocks_of_conjectures hι hκ _ _ _ _ V W hV hW

/-- Two paired blocks of size at most three give a verified case in the full ambient hull. -/
theorem holds_blocks_le_three {m n : ℕ} (hm : m ≤ 3) (hn : n ≤ 3)
    (eRow eCol : Fin (m + n) ≃ Fin m ⊕ Fin n) (a b : Fin m → ℂ) (c d : Fin n → ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V) :
    Holds (Sum.elim a c ∘ eRow) (Sum.elim b d ∘ eCol)
      ((fromBlocks U 0 0 V).submatrix eRow eCol) :=
  holds_reindexed_blocks_of_conjectures (conjecture_le_three hm) (conjecture_le_three hn)
    eRow eCol a b c d U V hU hV

/-- The combined order-two and order-three proof for paired blocks in order five. -/
theorem holds_blocks_two_three (a b : Fin 2 → ℂ) (c d : Fin 3 → ℂ)
    (U : Matrix (Fin 2) (Fin 2) ℂ) (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V) :
    Holds (Sum.elim a c ∘ finSumFinEquiv.symm) (Sum.elim b d ∘ finSumFinEquiv.symm)
      ((fromBlocks U 0 0 V).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) :=
  holds_blocks_le_three (by decide) (by decide) _ _ a b c d U V hU hV

end

end MOC

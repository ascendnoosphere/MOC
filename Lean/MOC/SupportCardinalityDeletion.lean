import MOC.SparseDegreeInduction

/-! Counting nonzero entries after a normalized row deletion. -/

open BigOperators Matrix

namespace MOC

/-- The number of nonzero entries of a finite square complex matrix. -/
noncomputable def supportEntryCount {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) : ℕ :=
  ∑ i, (supportColumns U {i}).card

/-- The adjoint preserves the number of nonzero entries. -/
theorem supportEntryCount_conjTranspose {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) :
    supportEntryCount Uᴴ = supportEntryCount U :=
  (sum_rowSupportDegree_eq_sum_columnSupportDegree U).symm

/-- A normalized row deletion at a nonzero pivot removes at least one nonzero entry. -/
theorem supportEntryCount_normalizedSparseRowMinor_add_one_le {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (i j k : Fin (n + 1)) (hj : U i j ≠ 0) :
    supportEntryCount (normalizedSparseRowMinor U i j k) + 1 ≤ supportEntryCount U := by
  classical
  have hmem : j ∈ supportColumns U {i} := by simpa [supportColumns] using hj
  have hrow : 1 ≤ (supportColumns U {i}).card := Finset.card_pos.mpr ⟨j, hmem⟩
  unfold supportEntryCount
  rw [Fin.sum_univ_succAbove (fun r => (supportColumns U {r}).card) i]
  rw [add_comm _ 1]
  exact add_le_add hrow (Finset.sum_le_sum fun r _ =>
    rowSupportDegree_normalizedSparseRowMinor_le i j k r)

end MOC

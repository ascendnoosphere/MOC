import MOC.SupportBlocks

open Matrix BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι]

/-- Counting nonzero entries by rows and by columns gives the same total. -/
theorem sum_rowSupportDegree_eq_sum_columnSupportDegree (U : Matrix ι ι ℂ) :
    (∑ i, (supportColumns U {i}).card) =
      ∑ j, (supportColumns Uᴴ {j}).card := by
  classical
  have row (i : ι) : (supportColumns U {i}).card =
      ∑ j, if U i j ≠ 0 then 1 else 0 := by
    simp only [supportColumns, Finset.mem_singleton, exists_eq_left,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  have col (j : ι) : (supportColumns Uᴴ {j}).card =
      ∑ i, if U i j ≠ 0 then 1 else 0 := by
    simp only [supportColumns, Finset.mem_singleton, exists_eq_left,
      Matrix.conjTranspose_apply, ne_eq, star_eq_zero,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [row, col]
  exact Finset.sum_comm

/-- If each row degree is at most a bound and each column degree is at least
that bound, every row and column degree equals the bound. -/
theorem supportDegrees_eq_of_row_le_of_column_ge {U : Matrix ι ι ℂ} (d : ℕ)
    (hr : ∀ i, (supportColumns U {i}).card ≤ d)
    (hc : ∀ j, d ≤ (supportColumns Uᴴ {j}).card) :
    (∀ i, (supportColumns U {i}).card = d) ∧
      (∀ j, (supportColumns Uᴴ {j}).card = d) := by
  classical
  have hrc := sum_rowSupportDegree_eq_sum_columnSupportDegree U
  have hrow := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hr i)
  have hcol := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hc j)
  have heq : (∑ i, (supportColumns U {i}).card) = ∑ _ : ι, d :=
    le_antisymm hrow (hcol.trans_eq hrc.symm)
  have h := (Finset.sum_eq_sum_iff_of_le (fun i _ => hr i)).mp heq
  have k := (Finset.sum_eq_sum_iff_of_le (fun j _ => hc j)).mp (heq.symm.trans hrc)
  exact ⟨fun i => h i (Finset.mem_univ i), fun j => (k j (Finset.mem_univ j)).symm⟩

end MOC

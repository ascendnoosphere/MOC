import MOC.AdjacentMinorSupport
import MOC.NestedValues
import MOC.Small

/-! A third eigenvalue of multiplicity one is covered by adjacent minor laws. -/

open Matrix

namespace MOC

set_option maxHeartbeats 800000 in
/-- In any finite order, the determinant inclusion holds if all but one
entry of the second spectrum lie in a two-point set. -/
theorem holds_three_values_one_singleton (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) (j : Fin n) (c d : ℂ)
    (hb : ∀ k, k ≠ j → b k = c ∨ b k = d) : Holds a b U := by
  classical
  by_cases hcd : c = d
  · subst d
    exact holds_one_exception a b U hU j c (fun k h => (hb k h).elim id id)
  let J := Finset.univ.filter (fun k => k ≠ j ∧ b k = c)
  have hj : j ∉ J := by simp [J]
  have hb' : Function.update (fun k => if k ∈ J then c else d) j (b j) = b := by
    funext k
    by_cases h : k = j
    · subst k
      simp only [Function.update_self]
    · rw [Function.update_of_ne h]
      rcases hb k h with hc | hd
      · simp [J, h, hc]
      · simp [J, h, hd, Ne.symm hcd]
  obtain ⟨p, hp, hnest, hrow, hcol⟩ := exists_adjacent_minor_transport U hU J j hj
  have h := holds_update_of_nested_image_coupling a J j hj c d (b j) hcd U hU p hp hnest hrow hcol
  rwa [hb'] at h

/-- The same two-value and singleton condition is invariant under relabeling. -/
theorem holds_three_values_one_singleton_fintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (j : ι) (c d : ℂ)
    (hb : ∀ k, k ≠ j → b k = c ∨ b k = d) : Holds a b U := by
  let e := (Fintype.equivFin ι).symm
  apply (holds_reindex_iff e e a b U).mp
  apply holds_three_values_one_singleton _ _ _ (unitary_reindex e e hU) (e.symm j) c d
  intro k hk
  apply hb (e k)
  intro he
  exact hk (e.injective (he.trans (e.apply_symm_apply j).symm))

end MOC

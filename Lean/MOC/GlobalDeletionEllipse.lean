import MOC.DeletionEllipse
import MOC.SparseRow

/-! The induction step for the global deletion ellipse premise. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private def deletionBorderIndex {n : ℕ} (i : Fin (n + 1)) : (Fin 1 ⊕ Fin n) ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.ofUnique (Fin 1) Unit) (Equiv.refl (Fin n))).trans
    ((Equiv.sumComm Unit (Fin n)).trans
      ((Equiv.optionEquivSumPUnit (Fin n)).symm.trans (finSuccEquiv' i).symm))

private theorem deletionBorderIndex_inl {n : ℕ} (i : Fin (n + 1)) (k : Fin 1) :
    deletionBorderIndex i (.inl k) = i := by simp [deletionBorderIndex]

private theorem deletionBorderIndex_inr {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    deletionBorderIndex i (.inr k) = i.succAbove k := by simp [deletionBorderIndex]

variable {n : ℕ}

/-- Delete one row and column and complete the minor on its affine phase circle.
At a decoupled anchor use the deleted matrix itself. -/
def deletionEllipseCompletion (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i j : Fin (n + 1)) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  if Complex.normSq (U i j) < 1 then
    affineSchurTransfer (U i j) (U.submatrix (fun _ => i) j.succAbove)
      (U.submatrix i.succAbove (fun _ => j)) (U.submatrix i.succAbove j.succAbove) z
  else U.submatrix i.succAbove j.succAbove

theorem deletionEllipseCompletion_at_anchor (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i j : Fin (n + 1)) :
    deletionEllipseCompletion U i j (-star (U i j)) = U.submatrix i.succAbove j.succAbove := by
  unfold deletionEllipseCompletion
  split_ifs <;> simp [affineSchurTransfer]

private theorem deletionAnchor_normSq_le {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : IsUnitary U) (i j : Fin (n + 1)) : Complex.normSq (U i j) ≤ 1 := by
  have h := sum_col_of_mem_doublyStochastic (normSq_transpose_doublyStochastic U hU) i
  change (∑ k, Complex.normSq (U i k)) = 1 at h
  rw [← h]
  exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (U i k)) (Finset.mem_univ j)

theorem deletionEllipseCompletion_unitary {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : IsUnitary U) (i j : Fin (n + 1)) (z : ℂ) (hz : ‖z‖ = 1) :
    IsUnitary (deletionEllipseCompletion U i j z) := by
  let r := U.submatrix (fun _ : Fin 1 => i) j.succAbove
  let c := U.submatrix i.succAbove (fun _ : Fin 1 => j)
  let D := U.submatrix i.succAbove j.succAbove
  have hblocks : IsUnitary (fromBlocks (scalar (Fin 1) (U i j)) r c D) := by
    have h := unitary_reindex (deletionBorderIndex i) (deletionBorderIndex j) hU
    have he : U.submatrix (deletionBorderIndex i) (deletionBorderIndex j) =
        fromBlocks (scalar (Fin 1) (U i j)) r c D := by
      ext (k | k) (l | l) : 1
      · have hkl : k = l := Subsingleton.elim _ _
        simp [deletionBorderIndex_inl, Matrix.scalar_apply, hkl]
      · simp [r, deletionBorderIndex_inl, deletionBorderIndex_inr]
      · simp [c, deletionBorderIndex_inl, deletionBorderIndex_inr]
      · simp [D, deletionBorderIndex_inr]
    rwa [he] at h
  unfold deletionEllipseCompletion
  split_ifs with ha
  · apply affineSchurTransfer_unitary _ _ _ _ z hblocks ha
    simp [Complex.normSq_eq_norm_sq, hz]
  · have hq : Complex.normSq (U i j) = 1 :=
      (deletionAnchor_normSq_le hU i j).antisymm (le_of_not_gt ha)
    have hn : ‖U i j‖ = 1 := (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
      (by simpa [Complex.normSq_eq_norm_sq] using hq)
    exact (schurTransfer_boundary _ _ _ _ hblocks hn).2.2

/-- Each point pairs the two deleted labels and uses the completed smaller
unitary for the other labels. -/
def deletionEllipsePoint (a b : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i j : Fin (n + 1)) (z : ℂ) : ℂ :=
  (a i + b j) * determinantValue (a ∘ i.succAbove) (b ∘ j.succAbove)
    (deletionEllipseCompletion U i j z)

/-- This premise asks for membership in the convex hull of the union of
the deletion ellipses in order one more than the index. -/
def GlobalDeletionEllipse (n : ℕ) : Prop :=
  ∀ (a b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), IsUnitary U →
    determinantValue a b U ∈ convexHull ℝ
      {w | ∃ (i j : Fin (n + 1)) (z : ℂ), ‖z‖ = 1 ∧ w = deletionEllipsePoint a b U i j z}

/-- The global deletion ellipse premise and the smaller-order conjecture
imply the next order. -/
theorem conjecture_succ_of_globalDeletionEllipse
    (h : GlobalDeletionEllipse n) (hSmall : Conjecture (Fin n)) :
    Conjecture (Fin (n + 1)) := by
  intro a b U hU
  apply convexHull_min ?_ (convex_convexHull ℝ _) (h a b U hU)
  rintro _ ⟨i, j, z, hz, rfl⟩
  let f : ℂ →ₗ[ℝ] ℂ := LinearMap.mulLeft ℝ (a i + b j)
  change f _ ∈ convexHull ℝ (Set.range (matchingProduct a b))
  apply convexHull_min ?_ ((convex_convexHull ℝ _).linear_preimage f)
    (hSmall _ _ _ (deletionEllipseCompletion_unitary hU i j z hz))
  rintro _ ⟨p, rfl⟩
  change (a i + b j) * matchingProduct (a ∘ i.succAbove) (b ∘ j.succAbove) p ∈ _
  rw [← matchingProduct_extendSparseRowMatching]
  exact matchingProduct_mem_hull a b _

end

end MOC

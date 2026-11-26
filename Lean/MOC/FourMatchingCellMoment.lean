import MOC.SignedCellMatchingMass
import MOC.FourMatchingAlternatingCorrection

/-! The four cells of two subset-image indicators. -/

open Matrix BigOperators

namespace MOC

/-- A cell label records membership in two subsets of four positions. -/
def fourMatchingCell (I K : Finset (Fin 4)) (i : Fin 4) : Fin 4 :=
  if i ∈ I then if i ∈ K then 0 else 1 else if i ∈ K then 2 else 3

private def matchingCellSet (I K : Finset (Fin 4)) : Fin 4 → Finset (Fin 4) :=
  ![I ∩ K, I \ K, K \ I, (I ∪ K)ᶜ]

private theorem matchingCellSet_mem (I K : Finset (Fin 4)) (c i : Fin 4) :
    i ∈ matchingCellSet I K c ↔ fourMatchingCell I K i = c := by
  fin_cases c <;> by_cases hI : i ∈ I <;> by_cases hK : i ∈ K <;>
    simp (disch := decide) [matchingCellSet, fourMatchingCell, hI, hK]

private theorem matchingBlock_det (A : Matrix (Fin 4) (Fin 4) ℝ)
    (I K : Finset (Fin 4)) (c : Fin 4) :
    (A.toSquareBlock (fourMatchingCell I K) c).det =
      principalRowDet A (matchingCellSet I K c) := by
  rw [principalRowDet_eq_det_submatrix]
  let s := matchingCellSet I K c
  have he (i : Fin 4) : i ∈ s ↔ fourMatchingCell I K i = c := matchingCellSet_mem I K c i
  let e : ↥s ≃ {i : Fin 4 // fourMatchingCell I K i = c} := Equiv.subtypeEquivRight he
  have hA : (A.toSquareBlock (fourMatchingCell I K) c).submatrix e e =
      A.submatrix (Subtype.val : ↥s → Fin 4) (Subtype.val : ↥s → Fin 4) := by
    ext i j
    rfl
  rw [← hA, Matrix.det_submatrix_equiv_self]

/-- The product of the four principal cell minors equals the determinant of
the matrix with all entries between different cells set to zero. -/
theorem det_labelledMatrix_fourMatchingCell (A : Matrix (Fin 4) (Fin 4) ℝ)
    (I K : Finset (Fin 4)) :
    (labelledMatrix A (fourMatchingCell I K) (fourMatchingCell I K)).det =
      fourPrincipalCellProduct A I K := by
  rw [det_labelledMatrix_eq_principalBlocks]
  simp only [matchingBlock_det]
  calc
    _ = ∏ c : Fin 4, principalRowDet A (matchingCellSet I K c) := by
      apply Finset.prod_subset (Finset.subset_univ _)
      intro c _ hc
      have he : matchingCellSet I K c = ∅ := by
        ext i
        simp only [Finset.not_mem_empty, iff_false]
        intro hi
        apply hc
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (matchingCellSet_mem I K c i).mp hi⟩
      rw [he, principalRowDet_eq_det_submatrix, Matrix.det_isEmpty]
    _ = _ := by rw [Fin.prod_univ_four]; rfl

/-- The sign sum of permutations that preserve a labelling is one for an
injective labelling and zero whenever two positions have the same label. -/
theorem signed_sum_matchingCell (label : Fin 4 → Fin 4) :
    (∑ σ : Equiv.Perm (Fin 4), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      (if ∀ i, label i = label (σ i) then 1 else 0)) =
      if Function.Injective label then 1 else 0 := by
  let B : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun _ _ => 1
  have hB := det_labelledMatrix_eq_signed_matching B label label
  simp only [B, Matrix.of_apply, Finset.prod_const_one] at hB
  rw [← hB]
  by_cases h : Function.Injective label
  · rw [if_pos h, show labelledMatrix B label label = 1 by
      ext i j
      simp only [labelledMatrix, B, Matrix.of_apply, h.eq_iff, Matrix.one_apply], Matrix.det_one]
  · rw [if_neg h]
    unfold Function.Injective at h
    push_neg at h
    obtain ⟨i, j, hij, hne⟩ := h
    apply Matrix.det_zero_of_row_eq hne
    funext k
    simp only [labelledMatrix, Matrix.of_apply, hij, B]

end MOC

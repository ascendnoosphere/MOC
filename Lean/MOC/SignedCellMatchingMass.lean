import Mathlib.LinearAlgebra.Matrix.Block

/-! A sum of signed determinant terms with fixed row-to-column labels. -/

open Matrix BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [DecidableEq κ]
variable {R : Type*} [CommRing R]

/-- The labelled matrix keeps the entries whose row and column labels agree. -/
def labelledMatrix (A : Matrix ι ι R) (rowLabel colLabel : ι → κ) : Matrix ι ι R :=
  Matrix.of fun i j => if rowLabel i = colLabel j then A i j else 0

/-- The determinant keeps precisely the matching terms that respect the labels. -/
theorem det_labelledMatrix_eq_signed_matching (A : Matrix ι ι R)
    (rowLabel colLabel : ι → κ) :
    (labelledMatrix A rowLabel colLabel).det =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : R) *
        (if ∀ i, rowLabel i = colLabel (σ i) then ∏ i, A i (σ i) else 0) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.transpose_apply, labelledMatrix, Matrix.of_apply]
  congr 1
  by_cases h : ∀ i, rowLabel i = colLabel (σ i)
  · rw [if_pos h]
    simp only [h, if_true]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

/-- When the two labellings coincide, the signed sum is a product of
principal minors, one for each occupied label. -/
theorem det_labelledMatrix_eq_principalBlocks [LinearOrder κ] (A : Matrix ι ι R)
    (label : ι → κ) :
    (labelledMatrix A label label).det =
      ∏ c ∈ (Finset.univ.image label), (A.toSquareBlock label c).det := by
  have htri : (labelledMatrix A label label).BlockTriangular label := by
    intro i j hij
    exact if_neg (ne_of_gt hij)
  rw [htri.det]
  apply Finset.prod_congr rfl
  intro c _
  congr 1
  ext i j
  change (if label i.val = label j.val then A i.val j.val else 0) = A i.val j.val
  rw [i.property, j.property, if_pos rfl]

end MOC

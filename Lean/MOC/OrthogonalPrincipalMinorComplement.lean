import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NoncommRing

/-! Signed principal minor complementation for orthogonal matrices. -/

open Matrix BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

private def principalProjection (s : Finset ι) : Matrix ι ι R :=
  Matrix.diagonal fun i => if i ∈ s then 1 else 0

omit [Fintype ι] in
private theorem principalProjection_transpose (s : Finset ι) :
    (principalProjection (R := R) s)ᵀ = principalProjection s := Matrix.diagonal_transpose _

private theorem principalProjection_compl (s : Finset ι) :
    principalProjection (R := R) sᶜ = 1 - principalProjection s := by
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i ∈ s <;> simp [principalProjection, hi]
  · simp [principalProjection, Matrix.one_apply_ne, h]

private def principalRowMatrix (A : Matrix ι ι R) (s : Finset ι) : Matrix ι ι R :=
  principalProjection s * A + (1 - principalProjection s)

private theorem principalRowMatrix_apply (A : Matrix ι ι R) (s : Finset ι) (i j : ι) :
    principalRowMatrix A s i j = if i ∈ s then A i j else (1 : Matrix ι ι R) i j := by
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ s <;>
      simp [principalRowMatrix, principalProjection, Matrix.diagonal_mul, hi]
  · by_cases hi : i ∈ s <;>
      simp [principalRowMatrix, principalProjection, Matrix.diagonal_mul, Matrix.one_apply_ne hij, hi, hij]

/-- A principal minor as a determinant with identity rows outside the selected set. -/
def principalRowDet (A : Matrix ι ι R) (s : Finset ι) : R := (principalRowMatrix A s).det

/-- The selected rows give the principal submatrix determinant. -/
theorem principalRowDet_eq_det_submatrix (A : Matrix ι ι R) (s : Finset ι) :
    principalRowDet A s = (A.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det := by
  let B := principalRowMatrix A s
  have hzero (i : ι) (hi : i ∉ s) (j : ι) (hj : j ∈ s) : B i j = 0 := by
    have hne : i ≠ j := fun h => hi (h ▸ hj)
    simp only [B, principalRowMatrix_apply, if_neg hi, Matrix.one_apply_ne hne]
  have hsub : B.toSquareBlockProp (· ∈ s) = A.submatrix Subtype.val Subtype.val := by
    ext i j
    change B i.val j.val = A i.val j.val
    simp only [B, principalRowMatrix_apply, if_pos i.property]
  have hcomp : B.toSquareBlockProp (· ∉ s) = 1 := by
    ext i j
    change B i.val j.val = _
    simp only [B, principalRowMatrix_apply, if_neg i.property, Matrix.one_apply]
    simp only [Subtype.ext_iff]
  change B.det = _
  rw [Matrix.twoBlockTriangular_det B (· ∈ s) hzero, hsub, hcomp, Matrix.det_one, mul_one]
  exact congrArg (fun F : Fintype ↥s =>
    @Matrix.det ↥s inferInstance F R inferInstance (A.submatrix Subtype.val Subtype.val))
    (Subsingleton.elim _ _)

private theorem principalRowMatrix_eq (A : Matrix ι ι R) (s : Finset ι) :
    principalRowMatrix A s = principalProjection s * (A - 1) + 1 := by
  unfold principalRowMatrix
  rw [Matrix.mul_sub, mul_one]
  abel

/-- A principal minor has the same value after transposition. -/
theorem principalRowDet_transpose (A : Matrix ι ι R) (s : Finset ι) :
    principalRowDet Aᵀ s = principalRowDet A s := by
  unfold principalRowDet
  rw [principalRowMatrix_eq, principalRowMatrix_eq, ← Matrix.det_transpose
    (principalProjection s * (Aᵀ - 1) + 1), Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose,
    principalProjection_transpose, Matrix.det_mul_add_one_comm]

/-- Each complementary pair of principal minors differs by the determinant
of the orthogonal matrix. -/
theorem principalRowDet_compl (A : Matrix ι ι R) (hA : A * Aᵀ = 1) (s : Finset ι) :
    principalRowDet A sᶜ = A.det * principalRowDet A s := by
  have he : principalRowMatrix A s * Aᵀ = principalRowMatrix Aᵀ sᶜ := by
    unfold principalRowMatrix
    rw [principalProjection_compl, Matrix.add_mul, Matrix.mul_assoc, hA, mul_one]
    rw [sub_sub_cancel]
    abel
  rw [← principalRowDet_transpose A sᶜ]
  unfold principalRowDet
  rw [← he, Matrix.det_mul, Matrix.det_transpose, mul_comm]

end MOC

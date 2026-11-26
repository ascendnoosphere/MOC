import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Every linear matrix pencil in the entries of one matrix has a realization
with one Kronecker product. The proof gives a norm bound from two finite
matrices that depend only on the coefficient matrices. -/

open BigOperators Matrix
open scoped Kronecker Matrix.L2OpNorm

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The input matrix copies the state into each column coordinate. -/
def matrixPencilInput : Matrix (ι × (ι × κ)) κ ℂ :=
  Matrix.of fun u s => if u.1 = u.2.1 ∧ u.2.2 = s then 1 else 0

/-- The output matrix records the entries of all the coefficient matrices. -/
def matrixPencilOutput (D : ι → ι → Matrix κ κ ℂ) : Matrix κ (ι × (ι × κ)) ℂ :=
  Matrix.of fun s u => D u.1 u.2.1 s u.2.2

private theorem amplified_mul_matrixPencilInput (Z : Matrix ι ι ℂ)
    (i j : ι) (k s : κ) :
    ((Z ⊗ₖ (1 : Matrix (ι × κ) (ι × κ) ℂ)) * matrixPencilInput) (i, (j, k)) s =
      if k = s then Z i j else 0 := by
  let T : Matrix (ι × (ι × κ)) κ ℂ := matrixPencilInput
  let V := Z ⊗ₖ (1 : Matrix (ι × κ) (ι × κ) ℂ)
  have hs (a : ι) : (∑ q : ι × κ, V (i, (j, k)) (a, q) * T (a, q) s) =
      Z i a * T (a, (j, k)) s := by
    calc
      _ = ∑ q : ι × κ, if (j, k) = q then Z i a * T (a, q) s else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases h : (j, k) = q
        all_goals simp [V, Matrix.kronecker_apply, Matrix.one_apply, h]
      _ = _ := by simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change (V * T) (i, (j, k)) s = _
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [hs]
  by_cases h : k = s
  · simp only [T, matrixPencilInput, Matrix.of_apply, h, and_true, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp [T, matrixPencilInput, h]

private theorem matrixPencil_factorization (D : ι → ι → Matrix κ κ ℂ) (Z : Matrix ι ι ℂ) :
    matrixPencilOutput D * ((Z ⊗ₖ (1 : Matrix (ι × κ) (ι × κ) ℂ)) * matrixPencilInput) =
      ∑ i : ι, ∑ j : ι, Z i j • D i j := by
  ext s t : 1
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, amplified_mul_matrixPencilInput]
  simp only [matrixPencilOutput, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_comm]

/-- One amplification realizes the determinant of an arbitrary linear
matrix pencil. The bound uses the norms of the displayed input and output
matrices. -/
theorem exists_determinantal_realization_linear_matrix_pencil (D : ι → ι → Matrix κ κ ℂ) :
    ∃ K : Matrix (ι × (ι × κ)) (ι × (ι × κ)) ℂ,
      ‖K‖ ≤ ‖(matrixPencilInput : Matrix (ι × (ι × κ)) κ ℂ)‖ * ‖matrixPencilOutput D‖ ∧
      ∀ Z : Matrix ι ι ℂ,
        (1 - K * (Z ⊗ₖ (1 : Matrix (ι × κ) (ι × κ) ℂ))).det =
          (1 - ∑ i : ι, ∑ j : ι, Z i j • D i j).det := by
  let T : Matrix (ι × (ι × κ)) κ ℂ := matrixPencilInput
  let R := matrixPencilOutput D
  refine ⟨T * R, Matrix.l2_opNorm_mul T R, fun Z => ?_⟩
  let V := Z ⊗ₖ (1 : Matrix (ι × κ) (ι × κ) ℂ)
  change (1 - (T * R) * V).det = _
  rw [Matrix.mul_assoc, Matrix.det_one_sub_mul_comm T (R * V), Matrix.mul_assoc]
  rw [matrixPencil_factorization D Z]

end

end MOC

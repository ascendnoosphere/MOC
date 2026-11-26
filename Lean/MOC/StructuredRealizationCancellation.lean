import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! A structured state pencil can have a zero that disappears from its
scalar transfer function. The two nonzero state blocks, input and output
in this example use one square matrix variable. -/

open Matrix
open scoped Kronecker

namespace MOC.StructuredRealizationCancellation

noncomputable section

private abbrev State := Fin 3 ⊕ Fin 3

private def stateIndex : State ≃ Fin 2 × Fin 3 where
  toFun := Sum.elim (fun j => (0, j)) (fun j => (1, j))
  invFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  left_inv := by
    rintro (j | j) <;> rfl
  right_inv := by
    rintro ⟨i, j⟩
    fin_cases i <;> rfl

private def firstStateBlock : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 1, 0, 0; 0, 0, 0]

private def secondStateBlock : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 0, 0; 1, 0, 0]

def stateMatrix : Matrix State State ℂ :=
  fromBlocks firstStateBlock secondStateBlock 0 0

def amplifiedVariable (Z : Matrix (Fin 2) (Fin 2) ℂ) : Matrix State State ℂ :=
  (Z ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)).submatrix stateIndex stateIndex

private theorem amplifiedVariable_blocks (Z : Matrix (Fin 2) (Fin 2) ℂ) :
    amplifiedVariable Z = fromBlocks (Z 0 0 • (1 : Matrix (Fin 3) (Fin 3) ℂ))
      (Z 0 1 • 1) (Z 1 0 • 1) (Z 1 1 • 1) := by
  apply Matrix.ext
  rintro (i | i) (j | j) <;>
    simp [amplifiedVariable, stateIndex, Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul]

private def leadingBlock (x y : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 - x, 0, 0; -x, 1, 0; -y, 0, 1]

private theorem leadingBlock_eq (x y : ℂ) :
    leadingBlock x y = 1 - (x • firstStateBlock + y • secondStateBlock) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [leadingBlock, firstStateBlock, secondStateBlock, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

def statePencil (Z : Matrix (Fin 2) (Fin 2) ℂ) : Matrix State State ℂ :=
  1 - stateMatrix * amplifiedVariable Z

private theorem statePencil_blocks (Z : Matrix (Fin 2) (Fin 2) ℂ) :
    statePencil Z = fromBlocks (leadingBlock (Z 0 0) (Z 1 0))
      (-(Z 0 1 • firstStateBlock + Z 1 1 • secondStateBlock)) 0 1 := by
  rw [statePencil, amplifiedVariable_blocks, stateMatrix, Matrix.fromBlocks_multiply,
    leadingBlock_eq]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.zero_mul, smul_zero, add_zero]
  apply Matrix.ext
  rintro (i | i) (j | j) <;> simp [Matrix.one_apply]

/-- The state determinant has a zero at every scalar point with first entry one. -/
theorem det_statePencil (Z : Matrix (Fin 2) (Fin 2) ℂ) :
    (statePencil Z).det = 1 - Z 0 0 := by
  rw [statePencil_blocks, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    leadingBlock, Matrix.det_fin_three]
  simp [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

private def firstInput : Fin 3 → ℂ := ![1, 0, 0]
private def firstOutput : Fin 3 → ℂ := ![0, 0, -1]
private def secondOutput : Fin 3 → ℂ := ![0, 1, 0]

def stateInput : State → ℂ := Sum.elim firstInput 0
def stateOutput : State → ℂ := Sum.elim firstOutput secondOutput

def scalarTransfer (Z : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  1 + stateOutput ⬝ᵥ (amplifiedVariable Z *ᵥ ((statePencil Z)⁻¹ *ᵥ stateInput))

/-- On the invertible locus of the pencil, the scalar transfer is constant. -/
theorem scalarTransfer_eq_one (Z : Matrix (Fin 2) (Fin 2) ℂ) (hx : 1 - Z 0 0 ≠ 0) :
    scalarTransfer Z = 1 := by
  let d := (1 - Z 0 0)⁻¹
  let v₀ : Fin 3 → ℂ := ![d, Z 0 0 * d, Z 1 0 * d]
  let v : State → ℂ := Sum.elim v₀ 0
  have hd : (1 - Z 0 0) * d = 1 := mul_inv_cancel₀ hx
  have h₀ : leadingBlock (Z 0 0) (Z 1 0) *ᵥ v₀ = firstInput := by
    funext i
    fin_cases i <;>
      simp [leadingBlock, v₀, firstInput, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, hd] <;> ring
  have hsolve : statePencil Z *ᵥ v = stateInput := by
    rw [statePencil_blocks, Matrix.fromBlocks_mulVec]
    change Sum.elim (_ *ᵥ v₀ + _ *ᵥ 0) (_ *ᵥ v₀ + _ *ᵥ 0) = stateInput
    simp only [h₀, Matrix.mulVec_zero, Matrix.zero_mulVec, add_zero, stateInput]
  have hunit : IsUnit (statePencil Z).det := by
    rw [det_statePencil]
    exact isUnit_iff_ne_zero.mpr hx
  have hv : (statePencil Z)⁻¹ *ᵥ stateInput = v := by
    rw [← hsolve, Matrix.mulVec_mulVec, (statePencil Z).nonsing_inv_mul hunit, Matrix.one_mulVec]
  have hout : stateOutput ⬝ᵥ (amplifiedVariable Z *ᵥ v) = 0 := by
    rw [amplifiedVariable_blocks, Matrix.fromBlocks_mulVec, Matrix.dotProduct_block]
    change firstOutput ⬝ᵥ (_ *ᵥ v₀ + _ *ᵥ 0) + secondOutput ⬝ᵥ (_ *ᵥ v₀ + _ *ᵥ 0) = 0
    simp only [Matrix.mulVec_zero, add_zero, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
    simp [firstOutput, secondOutput, v₀, dotProduct, Fin.sum_univ_three, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;> ring
  rw [scalarTransfer, hv, hout, add_zero]

/-- An input vector and two of its images under state blocks give three
independent reachable vectors. -/
theorem reachable_columns_det :
    (Matrix.of fun (i j : Fin 3) =>
      (![firstInput, firstStateBlock *ᵥ firstInput, secondStateBlock *ᵥ firstInput]
        : Fin 3 → Fin 3 → ℂ) j i).det = 1 := by
  norm_num [Matrix.det_fin_three, firstInput, firstStateBlock, secondStateBlock, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- Two output rows and the image of one row under a state block give
three independent rows for the observability test. -/
theorem observable_rows_det :
    (Matrix.of fun (i j : Fin 3) =>
      (![firstOutput, secondOutput, secondOutput ᵥ* firstStateBlock]
        : Fin 3 → Fin 3 → ℂ) i j).det = 1 := by
  norm_num [Matrix.det_fin_three, firstOutput, secondOutput, firstStateBlock, Matrix.vecMul,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- The scalar transfer has a constant extension across a zero of the
state determinant. The independent columns and rows verify the two
state span tests. This example excludes the inference in Corollary 2.2
of https://arxiv.org/html/1503.06161#S2 that zeros of a structured minimal
state determinant must be singularities of the scalar restriction.
For the related distinction between extended domains and stable extended
domains, see Volčič, https://arxiv.org/html/1608.02594#S2, Example 2.1. -/
theorem scalar_extension_with_singular_pencil :
    (∀ Z : Matrix (Fin 2) (Fin 2) ℂ, (statePencil Z).det ≠ 0 → scalarTransfer Z = 1) ∧
      (statePencil (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
  constructor
  · intro Z hZ
    rw [det_statePencil] at hZ
    exact scalarTransfer_eq_one Z hZ
  · simp only [det_statePencil, Matrix.one_apply_eq, sub_self]

end

end MOC.StructuredRealizationCancellation

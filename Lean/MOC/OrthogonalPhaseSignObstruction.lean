import MOC.TwoByTwoTensorPermutationLaw
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Real.Sqrt

/-! An order-three obstruction to replacing diagonal phases by signs in a
fixed chart. The all-mixer determinant inclusion in order three is
`MOC.conjecture_three`. -/

open Matrix

namespace MOC

noncomputable section

/-- The constant matrix with every entry equal to one third. -/
def phaseSignProjection : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun _ _ => ((1 / 3 : ℝ) : ℂ)

/-- Use `true` for the sign one and `false` for the sign minus one. -/
def phaseSignList (s : Fin 3 → Bool) (i : Fin 3) : ℂ :=
  if s i then 1 else -1

private theorem phaseSignProjection_hermitian : phaseSignProjection.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [phaseSignProjection, Matrix.of_apply, Complex.star_def, Complex.conj_ofReal]

private theorem phaseSign_sum_apply (z : Fin 3 → ℂ) (i j : Fin 3) :
    (1 - phaseSignProjection + diagonal z * phaseSignProjection * (diagonal z)ᴴ) i j =
      (if i = j then (1 : ℂ) else 0) - 1 / 3 + z i * star (z j) / 3 := by
  rw [Matrix.diagonal_conjTranspose]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, phaseSignProjection, Matrix.of_apply, Pi.star_apply,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- The determinant in this chart is the squared modulus of the phase sum
divided by nine. -/
theorem phaseSign_sum_det (z : Fin 3 → ℂ) :
    (1 - phaseSignProjection + diagonal z * phaseSignProjection * (diagonal z)ᴴ).det =
      ((Complex.normSq (z 0 + z 1 + z 2) / 9 : ℝ) : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.normSq_eq_conj_mul_self]
  simp only [Matrix.det_fin_three, phaseSign_sum_apply, Complex.star_def, map_add]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  simp only [if_pos rfl, if_neg h01, if_neg h02, if_neg h12,
    if_neg h01.symm, if_neg h02.symm, if_neg h12.symm, if_true]
  ring

private def phaseSignRoot : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

private theorem phaseSignRoot_normSq : Complex.normSq phaseSignRoot = 1 := by
  rw [Complex.normSq_apply]
  change (-1 / 2 : ℝ) * (-1 / 2) + (Real.sqrt 3 / 2) * (Real.sqrt 3 / 2) = 1
  nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private def phaseSignWitness : Fin 3 → ℂ := ![1, phaseSignRoot, star phaseSignRoot]

private theorem phaseSignWitness_normSq (i : Fin 3) : Complex.normSq (phaseSignWitness i) = 1 := by
  fin_cases i <;> simp [phaseSignWitness, phaseSignRoot_normSq, Complex.star_def]

private theorem phaseSignWitness_sum : phaseSignWitness 0 + phaseSignWitness 1 + phaseSignWitness 2 = 0 := by
  change 1 + phaseSignRoot + star phaseSignRoot = 0
  apply Complex.ext <;>
    norm_num [phaseSignRoot, Complex.star_def, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im] <;> ring

/-- There are unit phases that give determinant zero for the two fixed
real normal matrices. Every real sign choice gives determinant at least
one ninth in its real part. -/
theorem orthogonal_phase_sign_obstruction :
    let A : Matrix (Fin 3) (Fin 3) ℂ := 1 - phaseSignProjection
    let B := phaseSignProjection
    IsStarNormal A ∧ IsStarNormal B ∧ (∀ i j, (A i j).im = 0 ∧ (B i j).im = 0) ∧
      ∃ z : Fin 3 → ℂ, IsUnitary (diagonal z) ∧
        IsStarNormal (diagonal z * B * (diagonal z)ᴴ) ∧
        (A + diagonal z * B * (diagonal z)ᴴ).det = 0 ∧
        ∀ s : Fin 3 → Bool, IsUnitary (diagonal (phaseSignList s)) ∧
          (1 / 9 : ℝ) ≤ (A + diagonal (phaseSignList s) * B * (diagonal (phaseSignList s))ᴴ).det.re := by
  dsimp only
  have hA : (1 - phaseSignProjection).IsHermitian :=
    Matrix.isHermitian_one.sub phaseSignProjection_hermitian
  refine ⟨hA.isSelfAdjoint.isStarNormal, phaseSignProjection_hermitian.isSelfAdjoint.isStarNormal,
    ?_, phaseSignWitness, diagonal_phase_unitary _ phaseSignWitness_normSq,
    (Matrix.isHermitian_mul_mul_conjTranspose _ phaseSignProjection_hermitian).isSelfAdjoint.isStarNormal,
    ?_, ?_⟩
  · intro i j
    refine ⟨?_, Complex.ofReal_im _⟩
    by_cases hij : i = j <;>
      simp only [Matrix.sub_apply, Matrix.one_apply, phaseSignProjection, Matrix.of_apply,
        hij, if_true, if_false, Complex.sub_im, Complex.ofReal_im, Complex.one_im,
        Complex.zero_im, sub_zero]
  · rw [phaseSign_sum_det, phaseSignWitness_sum]
    simp only [Complex.normSq_zero, zero_div, Complex.ofReal_zero]
  · intro s
    constructor
    · apply diagonal_phase_unitary
      intro i
      cases hi : s i <;> simp [phaseSignList, hi, Complex.normSq_neg]
    · rw [phaseSign_sum_det, Complex.ofReal_re]
      cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
        norm_num [phaseSignList, h0, h1, h2, Complex.normSq_apply, Complex.add_re,
          Complex.add_im, Complex.neg_re, Complex.neg_im]

end

end MOC

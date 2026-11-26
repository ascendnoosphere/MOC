import MOC.FourHodgeExteriorSquare
import MOC.RealCoordinateRotation
import MOC.TwoByTwoTensorPermutationLaw
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.NormNum

/-! Explicit lifts of a rotation inside one Hodge block and of the block cycle. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private def fourHodgePhaseDiagonal (z : ℂ) : Fin 4 → ℂ :=
  ![z, z, star z, star z]

private def fourHodgePhaseCompoundDiagonal (w : ℂ) (p : HodgeIndex) : ℂ :=
  if p.1 = 0 then (if p.2 = 0 then w else star w) else 1

set_option maxHeartbeats 1500000 in
private theorem fourHodgeCompound_phaseDiagonal (z w : ℂ) (hz : z ^ 2 = w)
    (hphase : z * star z = 1) :
    fourHodgeCompound (Matrix.diagonal (fourHodgePhaseDiagonal z)) =
      Matrix.diagonal (fourHodgePhaseCompoundDiagonal w) := by
  have hzz : z * z = w := by simpa only [pow_two] using hz
  have hzzStar : star z * star z = star w := by
    simpa only [star_mul] using congrArg (star : ℂ → ℂ) hzz
  have hcomm : star z * z = 1 := (mul_comm (star z) z).trans hphase
  rw [fourHodgeCompound_diagonal]
  apply congrArg Matrix.diagonal
  funext p
  rcases p with ⟨p, i⟩
  fin_cases p <;> fin_cases i <;>
    norm_num [fourHodgePair, fourHodgePhaseDiagonal, fourHodgePhaseCompoundDiagonal,
      Matrix.cons_val, hzz, hzzStar, hphase, hcomm]

set_option maxHeartbeats 1500000 in
private theorem fourHodgeRealRepresentation_phaseDiagonal (c s : ℝ) (z : ℂ)
    (hz : z ^ 2 = ⟨c, s⟩) (hphase : z * star z = 1)
    (hU : IsUnitary (Matrix.diagonal (fourHodgePhaseDiagonal z)))
    (hd : (Matrix.diagonal (fourHodgePhaseDiagonal z)).det = 1) :
    fourHodgeRealRepresentation (Matrix.diagonal (fourHodgePhaseDiagonal z)) =
      realCoordinateRotation ((0, 0) : HodgeIndex) (0, 1) c s := by
  let d := fourHodgePhaseCompoundDiagonal (⟨c, s⟩ : ℂ)
  have hcomp : fourHodgeCompound (Matrix.diagonal (fourHodgePhaseDiagonal z)) =
      Matrix.diagonal d := fourHodgeCompound_phaseDiagonal z ⟨c, s⟩ hz hphase
  ext ⟨p, i⟩ ⟨q, j⟩
  rw [fourHodgeRealRepresentation_block _ hU hd, hcomp]
  fin_cases p <;> fin_cases q <;> fin_cases i <;> fin_cases j <;>
    norm_num [hodgeRealBlock, d, fourHodgePhaseCompoundDiagonal, Matrix.diagonal_apply,
      realCoordinateRotation]

/-- Every rotation inside the first Hodge block lifts to a diagonal special unitary. -/
theorem fourHodge_block_zero_rotation_lifts (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary U ∧ U.det = 1 ∧
      fourHodgeRealRepresentation U = realCoordinateRotation ((0, 0) : HodgeIndex) (0, 1) c s := by
  let w : ℂ := ⟨c, s⟩
  have hwnorm : Complex.normSq w = 1 := by
    simpa only [w, Complex.normSq_apply, pow_two] using h
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) two_pos
  have hzs : Complex.normSq z ^ 2 = 1 := by
    rw [← map_pow Complex.normSq, hz, hwnorm]
  have hznorm : Complex.normSq z = 1 :=
    (sq_eq_sq₀ (Complex.normSq_nonneg z) zero_le_one).mp (by simpa only [one_pow] using hzs)
  have hphase : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hznorm, Complex.ofReal_one]
  have hU : IsUnitary (Matrix.diagonal (fourHodgePhaseDiagonal z)) := by
    apply diagonal_phase_unitary
    intro i
    fin_cases i <;>
      simp [fourHodgePhaseDiagonal, Matrix.cons_val, Complex.star_def, Complex.normSq_conj, hznorm]
  have hd : (Matrix.diagonal (fourHodgePhaseDiagonal z)).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    change z * z * star z * star z = 1
    calc
      _ = (z * star z) ^ 2 := by ring
      _ = 1 := by rw [hphase, one_pow]
  exact ⟨_, hU, hd, fourHodgeRealRepresentation_phaseDiagonal c s z hz hphase hU hd⟩

/-- The Hodge block cycle sends `0` to `1`, `1` to `2`, and `2` to `0`. -/
def fourHodgeBlockCycle : Equiv.Perm (Fin 3) := Equiv.swap 0 2 * Equiv.swap 0 1

private def fourHodgeCyclePermutation : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 2 * Equiv.swap 1 3

private def fourHodgeCycleMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  fourHodgeCyclePermutation.permMatrix ℂ

private def fourHodgeCycleCompound : Matrix HodgeIndex HodgeIndex ℂ :=
  fun p q => if p = (fourHodgeBlockCycle q.1, q.2) then 1 else 0

private theorem fourHodgeCycleMatrix_apply (i j : Fin 4) :
    fourHodgeCycleMatrix i j = if j = fourHodgeCyclePermutation i then 1 else 0 := by
  simp only [fourHodgeCycleMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_some, eq_comm]

private theorem fourHodgeCycleMatrix_unitary : IsUnitary fourHodgeCycleMatrix := by
  have h : fourHodgeCycleMatrix * fourHodgeCycleMatrixᴴ = 1 := by
    change fourHodgeCyclePermutation.permMatrix ℂ *
      (fourHodgeCyclePermutation.permMatrix ℂ)ᴴ = 1
    rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    have hi : (fourHodgeCyclePermutation⁻¹ : Equiv.Perm (Fin 4)) (fourHodgeCyclePermutation i) = i :=
      fourHodgeCyclePermutation.symm_apply_apply i
    simp only [Matrix.submatrix_apply, id_eq, Matrix.one_apply, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_some, hi]
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

private theorem fourHodgeCycleMatrix_det : fourHodgeCycleMatrix.det = 1 := by
  simp [fourHodgeCycleMatrix, fourHodgeCyclePermutation, map_mul,
    Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 3)]

set_option maxHeartbeats 1500000 in
private theorem fourHodgeCompound_cycleMatrix :
    fourHodgeCompound fourHodgeCycleMatrix = fourHodgeCycleCompound := by
  ext ⟨p, i⟩ ⟨q, j⟩
  fin_cases p <;> fin_cases q <;> fin_cases i <;> fin_cases j <;>
    norm_num [fourHodgeCompound, fourHodgePair, fourHodgeCycleMatrix_apply,
      fourHodgeCycleCompound, fourHodgeCyclePermutation, fourHodgeBlockCycle, Matrix.cons_val,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

set_option maxHeartbeats 1500000 in
private theorem fourHodgeRealRepresentation_cycleMatrix :
    fourHodgeRealRepresentation fourHodgeCycleMatrix =
      fun p q => if p = (fourHodgeBlockCycle q.1, q.2) then 1 else 0 := by
  ext ⟨p, i⟩ ⟨q, j⟩
  rw [fourHodgeRealRepresentation_block _ fourHodgeCycleMatrix_unitary fourHodgeCycleMatrix_det,
    fourHodgeCompound_cycleMatrix]
  fin_cases p <;> fin_cases q <;> fin_cases i <;> fin_cases j <;>
    norm_num [hodgeRealBlock, fourHodgeCycleCompound, fourHodgeBlockCycle,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

/-- A cycle of the three Hodge blocks lifts to a coordinate permutation of determinant one. -/
theorem fourHodge_block_cycle_lifts :
    ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary U ∧ U.det = 1 ∧
      fourHodgeRealRepresentation U = fun p q =>
        if p = (fourHodgeBlockCycle q.1, q.2) then 1 else 0 :=
  ⟨fourHodgeCycleMatrix, fourHodgeCycleMatrix_unitary, fourHodgeCycleMatrix_det,
    fourHodgeRealRepresentation_cycleMatrix⟩

end

end MOC

import MOC.Pencil
import Mathlib.Analysis.Complex.Basic

/-! The Walsh example obstructs monotone rounding by a single paired
coordinate completion. Four phase evaluations check each completion circle. -/

open Matrix

namespace MOC

noncomputable section

private def walsh : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]

private def walshLeft : Fin 4 → ℂ := ![1, -1, -3 * Complex.I, 3 * Complex.I]

private def walshRight : Fin 4 → ℂ := ![-3, 3, -Complex.I, Complex.I]

private def completionColumn (i j : Fin 4) : Matrix (Fin 3) (Fin 1) ℂ :=
  Matrix.of fun k _ => (4 / 3 : ℂ) * walsh (i.succAbove k) j

private def completionRow (i j : Fin 4) : Matrix (Fin 1) (Fin 3) ℂ :=
  Matrix.of fun _ l => walsh i (j.succAbove l)

private def completionCenter (i j : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  walsh.submatrix i.succAbove j.succAbove + star (walsh i j) •
    (completionColumn i j * completionRow i j)

private def completion (i j : Fin 4) (z : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  completionCenter i j + z • (completionColumn i j * completionRow i j)

private def completionSupport (i j : Fin 4) (z : ℂ) : ℂ :=
  Complex.I * (walshLeft i + walshRight j) *
    determinantValue (walshLeft ∘ i.succAbove) (walshRight ∘ j.succAbove) (completion i j z)

theorem walsh_unitary : IsUnitary walsh := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [walsh, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Matrix.smul_apply, smul_eq_mul, Matrix.cons_val',
      Complex.ext_iff, Complex.star_def, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply]

private theorem completion_biaffine (i j : Fin 4) :
    ∃ a b c d : ℂ, ∀ z : ℂ,
      completionSupport i j z = a + b * z + c * star z + d * (z * star z) := by
  let A := diagonal (walshLeft ∘ i.succAbove)
  let B := diagonal (walshRight ∘ j.succAbove)
  let L := completionColumn i j
  let R := completionRow i j
  let D := completionCenter i j
  let p (s t : ℂ) := (A + (D + s • (L * R)) * B * (Dᴴ + t • (Rᴴ * Lᴴ))).det
  let k := Complex.I * (walshLeft i + walshRight j)
  refine ⟨k * p 0 0, k * (p 1 0 - p 0 0), k * (p 0 1 - p 0 0),
    k * (p 1 1 - p 1 0 - p 0 1 + p 0 0), fun z => ?_⟩
  have hf : completionSupport i j z = k * p z (star z) := by
    simp only [completionSupport, determinantValue, completion, p, A, B, D, L, R, k,
      Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]
  have hp : p z (star z) = p 0 0 + z * (p 1 0 - p 0 0) + star z * (p 0 1 - p 0 0) +
      z * star z * (p 1 1 - p 1 0 - p 0 1 + p 0 0) := by
    simpa only [p, Matrix.one_mul] using
      det_completion_biaffine A 1 D Dᴴ B L R Rᴴ Lᴴ z (star z)
  rw [hf, hp]
  ring

set_option maxHeartbeats 1500000 in
private theorem completion_four_phases (i j : Fin 4) :
    (completionSupport i j 1).re = -16 - 64 * (walsh i j).re ∧
    (completionSupport i j (-1)).re = -16 + 64 * (walsh i j).re ∧
    (completionSupport i j Complex.I).re = -16 ∧
    (completionSupport i j (-Complex.I)).re = -16 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [completionSupport, completion, completionCenter, completionColumn, completionRow,
      walsh, walshLeft, walshRight, determinantValue, Matrix.det_fin_three,
      Matrix.mul_diagonal, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.submatrix_apply, smul_eq_mul,
      Function.comp_apply, Fin.sum_univ_succ, Fin.succAbove, Fin.castSucc, Fin.succ,
      Fin.lt_def, Matrix.cons_val', Complex.star_def, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply]

theorem walsh_completion_bound (i j : Fin 4) (z : ℂ) (hz : Complex.normSq z = 1) :
    (completionSupport i j z).re ≤ 16 := by
  obtain ⟨a, b, c, d, h⟩ := completion_biaffine i j
  obtain ⟨h₁, h₂, h₃, h₄⟩ := completion_four_phases i j
  have hf := re_biaffine_circle _ a b c d h z hz
  rw [h₁, h₂, h₃, h₄] at hf
  have hnorm : ‖z‖ = 1 := by simp [Complex.norm_def, hz]
  have hre := Complex.abs_re_le_norm z
  rw [hnorm, abs_le] at hre
  have hw : (walsh i j).re = 1 / 2 ∨ (walsh i j).re = -(1 / 2) := by
    fin_cases i <;> fin_cases j <;>
      norm_num [walsh, Matrix.smul_apply, Matrix.cons_val', smul_eq_mul,
        Complex.mul_re, Complex.div_re, Complex.normSq_apply]
  rcases hw with hw | hw <;> rw [hw] at hf <;> nlinarith [hre.1, hre.2]

set_option maxHeartbeats 1500000 in
theorem walsh_original_support :
    (Complex.I * determinantValue walshLeft walshRight walsh).re = 24 := by
  rw [determinantValue, Matrix.det_succ_row_zero]
  norm_num [walsh, walshLeft, walshRight, Matrix.det_fin_three, Matrix.mul_diagonal,
    Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul, Fin.sum_univ_succ,
    Fin.succAbove, Fin.castSucc, Fin.succ, Fin.lt_def, Matrix.cons_val', Complex.star_def,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Complex.normSq_apply]

end

end MOC

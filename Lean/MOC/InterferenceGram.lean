import MOC.FiniteMinorLaw
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Pairwise row interference gives a positive real Gram matrix of rank at
most two. The same identities apply to columns after taking the adjoint. -/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def rowInterferenceVector (U : Matrix ι ι ℂ) (i j : ι) (k : ι) : ℂ :=
  U i k * star (U j k)

private def rowInterferenceComponents (U : Matrix ι ι ℂ) (i j : ι) : Matrix (Fin 2) ι ℝ :=
  Matrix.of fun r k => if r = 0 then (rowInterferenceVector U i j k).re
    else (rowInterferenceVector U i j k).im

/-- The real Gram matrix of the two Cartesian coordinates of row interference. -/
def rowInterferenceGram (U : Matrix ι ι ℂ) (i j : ι) : Matrix ι ι ℝ :=
  (rowInterferenceComponents U i j)ᴴ * rowInterferenceComponents U i j

private theorem rowInterferenceGram_apply (U : Matrix ι ι ℂ) (i j k l : ι) :
    rowInterferenceGram U i j k l =
      (rowInterferenceVector U i j k * star (rowInterferenceVector U i j l)).re := by
  simp [rowInterferenceGram, rowInterferenceComponents, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.star_def, Complex.mul_re] <;> ring

theorem rowInterferenceGram_posSemidef (U : Matrix ι ι ℂ) (i j : ι) :
    (rowInterferenceGram U i j).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

theorem rowInterferenceGram_rank_le (U : Matrix ι ι ℂ) (i j : ι) :
    (rowInterferenceGram U i j).rank ≤ 2 :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem rowInterferenceGram_diagonal (U : Matrix ι ι ℂ) (i j k : ι) :
    rowInterferenceGram U i j k k = Complex.normSq (U i k) * Complex.normSq (U j k) := by
  simp only [rowInterferenceGram_apply, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re, rowInterferenceVector, map_mul, Complex.normSq_conj]

theorem rowInterferenceGram_sum (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (i j : ι) (hij : i ≠ j) (k : ι) : ∑ l, rowInterferenceGram U i j k l = 0 := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j) hU.1
  have hz : ∑ l, rowInterferenceVector U i j l = 0 := by
    simpa only [rowInterferenceVector, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, if_neg hij] using h
  simp_rw [rowInterferenceGram_apply]
  rw [← Complex.re_sum, ← Finset.mul_sum, ← star_sum, hz, star_zero,
    mul_zero, Complex.zero_re]

theorem subsetMinorSq_eq_rowInterferenceGram (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) :
    subsetMinorSq U {i, j} {k, l} =
      Complex.normSq (U i k) * Complex.normSq (U j l) +
        Complex.normSq (U i l) * Complex.normSq (U j k) - 2 * rowInterferenceGram U i j k l := by
  rw [subsetMinorSq_pair U hU hij hkl, rowInterferenceGram_apply]
  simp only [rowInterferenceVector, Complex.normSq_apply, Complex.star_def,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  ring

end

end MOC

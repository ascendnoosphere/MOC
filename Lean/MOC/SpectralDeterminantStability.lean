import MOC.Core
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Upper half-plane nonvanishing for the spectral determinant and
an order-two obstruction for independent matrix-entry variables. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem im_diagonal_quadratic (a v : ι → ℂ) :
    (dotProduct (star v) (diagonal a *ᵥ v)).im =
      ∑ i, (a i).im * Complex.normSq (v i) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Complex.im_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  have he : star (v i) * (a i * v i) = a i * (Complex.normSq (v i) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def]
    ring
  rw [he]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]

private theorem conjugated_quadratic (B U : Matrix ι ι ℂ) (v : ι → ℂ) :
    dotProduct (star v) ((U * B * Uᴴ) *ᵥ v) =
      dotProduct (star (Uᴴ *ᵥ v)) (B *ᵥ (Uᴴ *ᵥ v)) := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- Strictly positive imaginary parts in the first list, and nonnegative
imaginary parts in the second, make the spectral determinant nonzero.
The argument permits an arbitrary matrix in the congruence. -/
theorem determinantValue_ne_zero_of_im_pos
    (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (ha : ∀ i, 0 < (a i).im) (hb : ∀ i, 0 ≤ (b i).im) :
    determinantValue a b U ≠ 0 := by
  intro hz
  change (diagonal a + U * diagonal b * Uᴴ).det = 0 at hz
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! hn
    exact hv (funext hn)
  have hA : 0 < ∑ j, (a j).im * Complex.normSq (v j) :=
    Finset.sum_pos' (fun j _ => mul_nonneg (ha j).le (Complex.normSq_nonneg (v j)))
      ⟨i, Finset.mem_univ i, mul_pos (ha i) (Complex.normSq_pos.mpr hi)⟩
  have hB : 0 ≤ ∑ j, (b j).im * Complex.normSq ((Uᴴ *ᵥ v) j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hb j) (Complex.normSq_nonneg _))
  have h : (dotProduct (star v) ((diagonal a + U * diagonal b * Uᴴ) *ᵥ v)).im = 0 := by
    rw [hker, dotProduct_zero, Complex.zero_im]
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_im, im_diagonal_quadratic,
    conjugated_quadratic, im_diagonal_quadratic] at h
  exact (add_pos_of_pos_of_nonneg hA hB).ne' h

/-- Independent entry variables in the upper half-plane can give a zero
determinant after entrywise multiplication by a unitary matrix. -/
theorem exists_independent_entry_halfPlane_zero :
    ∃ U Z : Matrix (Fin 2) (Fin 2) ℂ, IsUnitary U ∧
      (∀ i j, 0 < (Z i j).im) ∧ (Matrix.of (fun i j => Z i j * U i j)).det = 0 := by
  let U : Matrix (Fin 2) (Fin 2) ℂ :=
    !![((3 / 5 : ℝ) : ℂ), ((4 / 5 : ℝ) : ℂ); ((-4 / 5 : ℝ) : ℂ), ((3 / 5 : ℝ) : ℂ)]
  let Z : Matrix (Fin 2) (Fin 2) ℂ := !![4 + 4 * Complex.I, -3 + 3 * Complex.I;
    -3 + 3 * Complex.I, 4 + 4 * Complex.I]
  refine ⟨U, Z, ?_, ?_, ?_⟩
  · constructor <;> ext i j : 1 <;> fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      norm_num [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
        Fin.sum_univ_two, Complex.star_def, Complex.conj_ofNat, Complex.mul_re, Complex.mul_im]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Z, Complex.add_im, Complex.mul_im]
  · apply Complex.ext <;>
      norm_num [U, Z, Matrix.det_fin_two, Matrix.of_apply, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]

end MOC

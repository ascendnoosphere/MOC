import MOC.FourContact0710PencilFactors
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Reduce the actual order-four matching Hessian to a six-by-six Schur
complement. The leading block has a four-by-four zero corner. -/

open BigOperators Matrix
open private gradientTerms GradientTerm.hessianEntry from MOC.FourMatchingHessianMatrix

namespace MOC.FourContact0710

noncomputable section

private abbrev LeadingIndex := Fin 4 ⊕ Fin 4

private def leadingIndices : LeadingIndex → Fin 14 :=
  Sum.elim (![1, 3, 4, 6]) (![2, 7, 9, 13])

private def remainingIndices : Fin 6 → Fin 14 := ![0, 5, 8, 10, 11, 12]

private def blockIndex : LeadingIndex ⊕ Fin 6 → Fin 14 :=
  Sum.elim leadingIndices remainingIndices

private def blockIndexInverse : Fin 14 → LeadingIndex ⊕ Fin 6 :=
  ![.inr 0, .inl (.inl 0), .inl (.inr 0), .inl (.inl 1),
    .inl (.inl 2), .inr 1, .inl (.inl 3), .inl (.inr 1),
    .inr 2, .inl (.inr 2), .inr 3, .inr 4, .inr 5, .inl (.inr 3)]

private def blockEquiv : LeadingIndex ⊕ Fin 6 ≃ Fin 14 where
  toFun := blockIndex
  invFun := blockIndexInverse
  left_inv := by
    change ∀ i, blockIndexInverse (blockIndex i) = i
    decide +kernel
  right_inv := by
    change ∀ i, blockIndex (blockIndexInverse i) = i
    decide +kernel

private def crossing (c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![d, d, d - 1, d; 0, 0, -1, 0; 0, c + 1, c, 0; 0, 0, 0, 1]

private def crossingInverse (c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / d, -(c - d + 1) / (d * (c + 1)), -1 / (c + 1), -1;
    0, c / (c + 1), 1 / (c + 1), 0;
    0, -1, 0, 0;
    0, 0, 0, 1]

private def leadingTail : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, -1, 0; 0, 0, -1, 0; -1, -1, -2, 0; 0, 0, 0, 0]

private def leading (c d : ℝ) : Matrix LeadingIndex LeadingIndex ℝ :=
  Matrix.fromBlocks 0 (crossing c d) (crossing c d)ᵀ leadingTail

private def leadingInverse (c d : ℝ) : Matrix LeadingIndex LeadingIndex ℝ :=
  let i := crossingInverse c d
  Matrix.fromBlocks (-(iᵀ * leadingTail * i)) iᵀ i 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem leading_eq (a b c d e t : ℝ) :
    (fourMatchingHessian (lift a b c d e t)).submatrix leadingIndices leadingIndices =
      leading c d := by
  ext i j : 1
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    norm_num [leadingIndices, leading, crossing, leadingTail, fourMatchingHessian, gradientTerms,
      GradientTerm.hessianEntry, lift, Matrix.submatrix_apply, Matrix.transpose_apply] <;> ring

private def swapBlockRows : Equiv.Perm LeadingIndex :=
  Equiv.swap (.inl 0) (.inr 0) * Equiv.swap (.inl 1) (.inr 1) *
    Equiv.swap (.inl 2) (.inr 2) * Equiv.swap (.inl 3) (.inr 3)

private theorem swapBlockRows_left (i : Fin 4) : swapBlockRows (.inl i) = .inr i := by
  fin_cases i <;> decide

private theorem swapBlockRows_right (i : Fin 4) : swapBlockRows (.inr i) = .inl i := by
  fin_cases i <;> decide

private theorem swapBlockRows_sign : Equiv.Perm.sign swapBlockRows = 1 := by
  simp [swapBlockRows, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap, Sum.inl_ne_inr]

private theorem det_crossing (c d : ℝ) : (crossing c d).det = d * (c + 1) := by
  norm_num [crossing, Matrix.det_succ_row_zero, Matrix.det_fin_zero,
    Fin.sum_univ_succ, Fin.succAbove, Matrix.submatrix_apply] <;> ring

private theorem det_leading (c d : ℝ) : (leading c d).det = d ^ 2 * (c + 1) ^ 2 := by
  have hp := Matrix.det_permute swapBlockRows (leading c d)
  have hrew : (leading c d).submatrix swapBlockRows id =
      Matrix.fromBlocks (crossing c d)ᵀ leadingTail 0 (crossing c d) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [leading, Matrix.submatrix_apply, swapBlockRows_left, swapBlockRows_right, id_eq,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  rw [hrew, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose, det_crossing,
    swapBlockRows_sign] at hp
  simp only [Units.val_one, Int.cast_one, one_mul] at hp
  linear_combination -hp

private theorem crossing_inverse_products (c d : ℝ) (hc : c + 1 ≠ 0) (hd : d ≠ 0) :
    crossing c d * crossingInverse c d = 1 ∧ crossingInverse c d * crossing c d = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [crossing, crossingInverse, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
    field_simp [hc, hd] <;> ring

private theorem leading_inverse_product (c d : ℝ) (hc : c + 1 ≠ 0) (hd : d ≠ 0) :
    leading c d * leadingInverse c d = 1 := by
  obtain ⟨hi, hI⟩ := crossing_inverse_products c d hc hd
  have htranspose : (crossing c d)ᵀ * (crossingInverse c d)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hI, Matrix.transpose_one]
  rw [leading, leadingInverse, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have hz :
      (crossing c d)ᵀ * (-((crossingInverse c d)ᵀ * leadingTail * crossingInverse c d)) +
        leadingTail * crossingInverse c d = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, htranspose, Matrix.one_mul, neg_add_cancel]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.add_zero, Matrix.zero_add, hi, htranspose, hz]

private def schur (H : Matrix (Fin 14) (Fin 14) ℝ) (c d : ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  H.submatrix remainingIndices remainingIndices -
    H.submatrix remainingIndices leadingIndices * leadingInverse c d *
      H.submatrix leadingIndices remainingIndices

private def rowScales (c d : ℝ) : Fin 6 → ℝ :=
  ![c + 1, d, c + 1, d, c + 1, (c + 1) * d]

private theorem det_rowScales (c d : ℝ) :
    (diagonal (rowScales c d)).det = d ^ 3 * (c + 1) ^ 4 := by
  rw [Matrix.det_diagonal]
  simp [rowScales, Fin.prod_univ_succ] <;> ring

/-- Division-free entries of the rescaled six-by-six Schur complement. -/
private def scaledSchur (a b c d e t : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![2 * (c + 1) * (c * e + d * e + d * t + e * t + e + t),
      (c + 1) * (2 * c * e + d * e + e * t + 2 * e + t),
      (c + 1) * (-a * c - a * d - a - c + d * e + d * t - d - 1),
      e * (c + 1) * (2 * c + d + t + 1),
      -a * c ^ 2 - a * c * d - a * c - c ^ 2 + c * d * e + c * d * t - c * d - c + d * e + d * t,
      b * c ^ 2 + b * c * t + b * c + b * t + 2 * c ^ 2 * e + 2 * c * d * e + c * d * t - c * d + c * e * t + 3 * c * e + c * t + 2 * d * e + d * t + e * t + e + t;
     d * (2 * c * e + d * e + e * t + 2 * e + t),
      2 * d * e * (c + 1),
      d * (-a * c - a - c + d * e + t - 1),
      e * (2 * c * d + 2 * d + t),
      d * (-a * c - c + d * e + t),
      b * c * d + b * d + b * t + 2 * c * d * e + d ^ 2 * e + 2 * d * e + d * t + d + e * t + t;
     (c + 1) * (-a * c - a * d - a - c + d * e + d * t - d - 1),
      (c + 1) * (-a * c - a - c + d * e + t - 1),
      -2 * d * (a + 1) * (c + 1),
      -(c + 1) * (a * c + a + c - d * e + e + 1),
      -(a + 1) * (2 * c * d - c + d - 1),
      -a * b * c - a * b - a * c ^ 2 - a * c * d - 2 * a * c - a * d - a - b * c - b - c ^ 2 + c * d * e - 2 * c * d - c * e - 2 * c + d * e - d - e - 1;
     d * e * (2 * c + d + t + 1),
      e * (2 * c * d + 2 * d + t),
      -d * (a * c + a + c - d * e + e + 1),
      2 * d * e * (c + 1),
      -d * (a * c + c - d * e + e),
      d * (b * c + b + 2 * c * e + d * e + e + 1);
     -a * c ^ 2 - a * c * d - a * c - c ^ 2 + c * d * e + c * d * t - c * d - c + d * e + d * t,
      (c + 1) * (-a * c - c + d * e + t),
      -(a + 1) * (2 * c * d - c + d - 1),
      -(c + 1) * (a * c + c - d * e + e),
      2 * (a + 1) * (b - c * d + c + 1),
      -a * b * c - a * c ^ 2 - a * c * d - a * c - 2 * b * c - c ^ 2 + c * d * e - 2 * c * d - c * e - c + d * e - e;
     d * (b * c ^ 2 + b * c * t + b * c + b * t + 2 * c ^ 2 * e + 2 * c * d * e + c * d * t - c * d + c * e * t + 3 * c * e + c * t + 2 * d * e + d * t + e * t + e + t),
      (c + 1) * (b * c * d + b * d + b * t + 2 * c * d * e + d ^ 2 * e + 2 * d * e + d * t + d + e * t + t),
      -d * (a * b * c + a * b + a * c ^ 2 + a * c * d + 2 * a * c + a * d + a + b * c + b + c ^ 2 - c * d * e + 2 * c * d + c * e + 2 * c - d * e + d + e + 1),
      d * (c + 1) * (b * c + b + 2 * c * e + d * e + e + 1),
      -d * (a * b * c + a * c ^ 2 + a * c * d + a * c + 2 * b * c + c ^ 2 - c * d * e + 2 * c * d + c * e + c - d * e + e),
      2 * d * (b * c ^ 2 + c ^ 2 * e + c * d * e - c * d + c * e + d * e)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
private theorem scaledSchur_eq (a b c d e t : ℝ) (hc : c + 1 ≠ 0) (hd : d ≠ 0) :
    scaledSchur a b c d e t =
      diagonal (rowScales c d) * schur (fourMatchingHessian (lift a b c d e t)) c d := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    norm_num [scaledSchur, Matrix.diagonal_mul, rowScales, schur, leadingIndices,
      remainingIndices, leadingInverse, leadingTail, crossingInverse, fourMatchingHessian,
      gradientTerms, GradientTerm.hessianEntry, lift, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.neg_apply, Matrix.transpose_apply, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_succ] <;> field_simp [hc, hd] <;> ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 60000000 in
private theorem det_scaledSchur (a b c d e t : ℝ) :
    (scaledSchur a b c d e t).det =
      -4 * d * (c + 1) ^ 2 * linearFactor a b c d e t * quadraticFactor a b c d e t := by
  norm_num [scaledSchur, Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.succAbove, Matrix.submatrix_apply, Matrix.cons_val, Matrix.of_apply, linearFactor,
    linearConstant, linearSlope, quadraticFactor, quadraticConstant, quadraticLinear,
    quadraticLeading, heightDenominator, couplingParameter, rootPolynomial, linearParameter,
    constantParameter, q, p] <;> ring

/-- The determinant of the actual matching Hessian is the product of
the scalar factors. The fourth weight must be positive for this
Schur chart. The third weight may vanish. -/
theorem hessian_det_eq_factor_product (a b c d e t : ℝ) (hc : 0 ≤ c) (hd : 0 < d) :
    (fourMatchingHessian (lift a b c d e t)).det =
      -4 * linearFactor a b c d e t * quadraticFactor a b c d e t := by
  let H := fourMatchingHessian (lift a b c d e t)
  let A := H.submatrix leadingIndices leadingIndices
  let B := H.submatrix leadingIndices remainingIndices
  let C := H.submatrix remainingIndices leadingIndices
  let D := H.submatrix remainingIndices remainingIndices
  have hc1 : 0 < c + 1 := by positivity
  have hA : A = leading c d := leading_eq a b c d e t
  have hAdet : A.det = d ^ 2 * (c + 1) ^ 2 := by rw [hA, det_leading]
  have hunit : IsUnit A.det := by
    rw [hAdet, isUnit_iff_ne_zero]
    exact mul_ne_zero (pow_ne_zero 2 hd.ne') (pow_ne_zero 2 hc1.ne')
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hunit
  have hi : A * leadingInverse c d = 1 := by
    rw [hA]
    exact leading_inverse_product c d hc1.ne' hd.ne'
  have hInv : ⅟ A = leadingInverse c d := invOf_eq_right_inv hi
  have hblock : H.submatrix blockEquiv blockEquiv = Matrix.fromBlocks A B C D := by
    ext i j
    cases i <;> cases j <;> rfl
  have hSchur : H.det = (d ^ 2 * (c + 1) ^ 2) * (schur H c d).det := by
    rw [← Matrix.det_submatrix_equiv_self blockEquiv H, hblock,
      Matrix.det_fromBlocks₁₁, hAdet, hInv] <;> rfl
  have hScaled := det_scaledSchur a b c d e t
  rw [scaledSchur_eq a b c d e t hc1.ne' hd.ne', Matrix.det_mul, det_rowScales] at hScaled
  change d ^ 3 * (c + 1) ^ 4 * (schur H c d).det = _ at hScaled
  change H.det = _
  apply mul_left_cancel₀ (mul_ne_zero hd.ne' (pow_ne_zero 2 hc1.ne'))
  rw [hSchur]
  linear_combination hScaled

/-- For a spectral lift with positive fourth weight, the normalized
branch equation follows from the actual Hessian determinant. -/
theorem branchPolynomial_zero_of_spectralLift {a b c d e t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d) (he : 0 ≤ e)
    (hs : HasSpectralLift a b c d e t) :
    branchPolynomial a b c d e = 0 := by
  obtain ⟨hQ, _, ht⟩ := height_of_spectralLift ha hb hc he hs
  have hdet := hessian_singular_of_spectralLift hs
  rw [hessian_det_eq_factor_product a b c d e t hc hd, ht,
    linearFactor_at_height hQ, quadraticFactor_at_height hQ] at hdet
  have hmain : (c + 1) * branchPolynomial a b c d e / heightDenominator d e = 0 := by
    rcases mul_eq_zero.mp hdet with h | h
    · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    · exact h
  have hc1 : c + 1 ≠ 0 := ne_of_gt (by positivity)
  exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hmain).resolve_right hQ)).resolve_left hc1

/-- For an actual gap in the unequal branch, the signed second
difference of the Hessian pencil is positive. This reduces exclusion
to a separate necessary spectral sign inequality. -/
theorem hessian_second_difference_pos_of_unequal_spectralLift {a b c d e t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d) (he : 0 ≤ e)
    (hne : a ≠ b) (hQ : heightDenominator d e < 0) (hs : HasSpectralLift a b c d e t) :
    0 < (fourMatchingHessian (lift a b c d e (t + 1))).det +
          (fourMatchingHessian (lift a b c d e (t - 1))).det -
          2 * (fourMatchingHessian (lift a b c d e t)).det := by
  have hP := branchPolynomial_zero_of_spectralLift ha hb hc hd he hs
  have hep : 0 < e := by
    refine lt_of_le_of_ne he ?_
    intro hez
    subst e
    exact (branchPolynomial_pos_at_zero ha hb hc hd.le).ne' hP
  obtain ⟨_, _, ht⟩ := height_of_spectralLift ha hb hc he hs
  obtain ⟨hpos, hexp⟩ := positive_quadratic_term_of_unequal_factor_product ha hb hc hd hep hne hP hQ ht
  have hplus := hexp 1
  have hminus := hexp (-1)
  rw [hessian_singular_of_spectralLift hs, mul_zero, sub_zero, sub_eq_add_neg,
    hessian_det_eq_factor_product a b c d e (t + 1) hc hd,
    hessian_det_eq_factor_product a b c d e (t + -1) hc hd, hplus, hminus]
  nlinarith only [hpos]

/-- A nonpositive Hessian second difference excludes the unequal branch
with negative signed contact height. -/
theorem no_unequal_spectralLift_of_hessian_second_difference_nonpos {a b c d e t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d) (he : 0 ≤ e)
    (hne : a ≠ b) (hQ : heightDenominator d e < 0)
    (h : (fourMatchingHessian (lift a b c d e (t + 1))).det +
          (fourMatchingHessian (lift a b c d e (t - 1))).det -
          2 * (fourMatchingHessian (lift a b c d e t)).det ≤ 0) :
    ¬ HasSpectralLift a b c d e t := by
  intro hs
  exact (not_lt_of_ge h)
    (hessian_second_difference_pos_of_unequal_spectralLift ha hb hc hd he hne hQ hs)

end

end MOC.FourContact0710

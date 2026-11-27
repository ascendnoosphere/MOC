import MOC.FourContact0710PencilFactors
import Mathlib.LinearAlgebra.Matrix.SchurComplement
set_option Elab.async false
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

private def inverseTail (d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1 / d, 0, 0; -1 / d, 2 / d, 0, 1; 0, 0, 0, 0; 0, 1, 0, 0]

private def leadingInverse (c d : ℝ) : Matrix LeadingIndex LeadingIndex ℝ :=
  Matrix.fromBlocks (inverseTail d) (crossingInverse c d)ᵀ (crossingInverse c d) 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem leading_eq (a b c d e t : ℝ) :
    (fourMatchingHessian (lift a b c d e t)).submatrix leadingIndices leadingIndices =
      leading c d := by
  ext i j : 1
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply,
      leadingIndices, Sum.elim_inl, Sum.elim_inr, leading, crossing, leadingTail,
      Matrix.of_apply, Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    simp (disch := decide) only [if_pos, if_neg, fourMatchingHessian, gradientTerms,
      Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ',
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      GradientTerm.hessianEntry, lift, Matrix.zero_apply] <;>
    norm_num only [Fin.ext_iff] <;> ring

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
  have hz (i : Fin 3) : crossing c d i.succ 0 = 0 := by
    fin_cases i <;> rfl
  have hminor : (crossing c d).submatrix Fin.succ Fin.succ =
      !![0, -1, 0; c + 1, c, 0; 0, 0, 1] := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (0 : Fin 4)]
  · rw [Fin.succAbove_zero, hminor, Matrix.det_fin_three]
    simp only [crossing, Fin.val_zero, pow_zero, one_mul, Matrix.of_apply,
      Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ']
    <;> ring
  · intro i _ hi
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    rw [hz, mul_zero, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

set_option maxRecDepth 4096 in
private theorem det_leading (c d : ℝ) : (leading c d).det = d ^ 2 * (c + 1) ^ 2 := by
  have hrew : (leading c d).submatrix swapBlockRows id =
      Matrix.fromBlocks (crossing c d)ᵀ leadingTail 0 (crossing c d) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [leading, Matrix.submatrix_apply, swapBlockRows_left, swapBlockRows_right, id_eq,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  have hperm : ((leading c d).submatrix swapBlockRows id).det = (leading c d).det := by
    simpa only [swapBlockRows_sign, Units.val_one, Int.cast_one, one_mul] using
      Matrix.det_permute swapBlockRows (leading c d)
  calc
    (leading c d).det = ((leading c d).submatrix swapBlockRows id).det := hperm.symm
    _ = (Matrix.fromBlocks (crossing c d)ᵀ leadingTail 0 (crossing c d)).det :=
      congrArg (fun A : Matrix LeadingIndex LeadingIndex ℝ => A.det) hrew
    _ = _ := by
      simp only [Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose, det_crossing, mul_pow, pow_two]
      ring

private theorem crossing_inverse_products (c d : ℝ) (hc : c + 1 ≠ 0) (hd : d ≠ 0) :
    crossing c d * crossingInverse c d = 1 ∧ crossingInverse c d * crossing c d = 1 := by
  constructor <;> ext i j : 1 <;> fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_four, crossing,
      crossingInverse, Matrix.of_apply, Matrix.cons_val, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.one_apply] <;>
    simp (disch := decide) only [if_pos, if_neg, zero_mul, mul_zero, zero_add, add_zero] <;>
    field_simp [hc, hd] <;> ring

private theorem inverseTail_eq (c d : ℝ) (hc : c + 1 ≠ 0) (hd : d ≠ 0) :
    inverseTail d = -((crossingInverse c d)ᵀ * leadingTail * crossingInverse c d) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.transpose_apply, inverseTail, crossingInverse, leadingTail, Matrix.of_apply,
      Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ',
      zero_mul, mul_zero, zero_add, add_zero] <;>
    field_simp [hc, hd] <;> ring

private theorem leading_inverse_product (c d : ℝ) (hc : c + 1 ≠ 0) (hd : d ≠ 0) :
    leading c d * leadingInverse c d = 1 := by
  obtain ⟨hi, hI⟩ := crossing_inverse_products c d hc hd
  have htranspose : (crossing c d)ᵀ * (crossingInverse c d)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hI, Matrix.transpose_one]
  rw [leading, leadingInverse, inverseTail_eq c d hc hd, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one]
  have hz :
      (crossing c d)ᵀ * (-((crossingInverse c d)ᵀ * leadingTail * crossingInverse c d)) +
        leadingTail * crossingInverse c d = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, htranspose, Matrix.one_mul, neg_add_cancel]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hi, htranspose, hz]

private def schur (H : Matrix (Fin 14) (Fin 14) ℝ) (c d : ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  H.submatrix remainingIndices remainingIndices -
    H.submatrix remainingIndices leadingIndices * leadingInverse c d *
      H.submatrix leadingIndices remainingIndices

private def joiningFirst (b c d t : ℝ) : Matrix (Fin 4) (Fin 6) ℝ :=
  !![-c - 1, -c - t - 1, 0, -c - 1, 0, -b - c - 1;
     -c - d - 1, -c - 1, -d, -c - 1, -d, -b - c - d - 1;
     0, 0, c + 1, 0, b + c + 1, 0;
     t, 0, 0, 0, 0, -b]

private def joiningSecond (a b c e : ℝ) : Matrix (Fin 4) (Fin 6) ℝ :=
  !![-c - 1, -c - 1, 0, -c + e - 1, 0, -c + e;
     0, 0, 0, e, -a - 1, e;
     -e - 2, -e - 1, a, -1, -1, -b - 1;
     -e - 1, -e, 0, 0, 0, 0]

private def joining (a b c d e t : ℝ) : Matrix LeadingIndex (Fin 6) ℝ :=
  Sum.elim (joiningFirst b c d t) (joiningSecond a b c e)

private def trailing (b c : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-2 * c - 2, -c - 1, 0, -c - 1, b, -c - 1;
     -c - 1, 0, 0, 0, b, 0;
     0, 0, 0, 0, 0, 0;
     -c - 1, 0, 0, 0, b, 0;
     b, b, 0, b, 0, 0;
     -c - 1, 0, 0, 0, 0, 0]

private def scaledSolution (a b c d e t : ℝ) : Matrix LeadingIndex (Fin 6) ℝ :=
  Sum.elim
    !![d * (c + 1), 0, d * (c + 1), e * (c + 1), d * (c + 1), (c + 1) * (b + d + e + 1);
       d * (c + 1) * (e + t - 1), (c + 1) * (d * e + t), -d * (a + 2) * (c + 1),
        e * (c + 1) * (d - 1), -d * (a * c + 2 * c + 1),
        -b * c - b + c * d * e - 2 * c * d - c * e - c + d * e - d - e - 1;
       d * (c + 1), d * (c + 1), 0, d * (c + 1), -d * (a + 1), c * d;
       -d * (c + 1) * (d + e + 1), -d * e * (c + 1), -d ^ 2 * (c + 1),
        -d * e * (c + 1), -d ^ 2 * (c + 1), -d * (c + 1) * (b + d + e + 1)]
    !![-d * (c * t + d + t), -(c + 1) * (d + t), -d ^ 2, -d * (c + 1),
        -d * (b + d), d * (b * c - d);
       -c * d * (c + d + 1), -c * d * (c + 1), -d * (c * d - c - 1), -c * d * (c + 1),
        d * (b - c * d + c + 1), -c * d * (b + c + d + 1);
       d * (c + 1) * (c + d + 1), d * (c + 1) ^ 2, d ^ 2 * (c + 1), d * (c + 1) ^ 2,
        d ^ 2 * (c + 1), d * (c + 1) * (b + c + d + 1);
       d * t * (c + 1), 0, 0, 0, 0, -b * d * (c + 1)]

set_option maxHeartbeats 2000000 in
private theorem scaledSolution_eq (a b c d e t : ℝ) (hc : c + 1 ≠ 0) (hd : d ≠ 0) :
    scaledSolution a b c d e t = (d * (c + 1)) • (leadingInverse c d * joining a b c d e t) := by
  ext i j : 1
  rcases i with i | i <;> fin_cases i <;> fin_cases j <;>
    simp only [scaledSolution, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_four, leadingInverse, inverseTail, crossingInverse,
      joining, joiningFirst, joiningSecond, Matrix.transpose_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, Matrix.of_apply, Matrix.cons_val,
      Matrix.cons_val_zero', Matrix.cons_val_succ', zero_mul, mul_zero, zero_add, add_zero] <;>
    field_simp [hc, hd] <;> ring

set_option maxHeartbeats 3000000 in
private theorem schur_block_entries (a b c d e t : ℝ) :
    let H := fourMatchingHessian (lift a b c d e t)
    H.submatrix leadingIndices remainingIndices = joining a b c d e t ∧
      H.submatrix remainingIndices leadingIndices = (joining a b c d e t)ᵀ ∧
      H.submatrix remainingIndices remainingIndices = trailing b c := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩ <;> ext i j : 1
  all_goals
    first
    | (change LeadingIndex at i; rcases i with i | i)
    | (change LeadingIndex at j; rcases j with j | j)
    | skip
  all_goals
    fin_cases i <;> fin_cases j <;>
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply, leadingIndices, remainingIndices,
      joining, joiningFirst, joiningSecond, trailing, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    simp (disch := decide) only [if_pos, if_neg, fourMatchingHessian, gradientTerms,
      Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ',
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      GradientTerm.hessianEntry, lift] <;>
    norm_num only [Fin.ext_iff] <;> ring

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
  obtain ⟨hB, hC, hD⟩ := schur_block_entries a b c d e t
  rw [schur, hB, hC, hD]
  let z := d * (c + 1)
  let J := joining a b c d e t
  have hsolve : scaledSolution a b c d e t = z • (leadingInverse c d * J) :=
    scaledSolution_eq a b c d e t hc hd
  have hinner : z • (trailing b c - Jᵀ * leadingInverse c d * J) =
      z • trailing b c - Jᵀ * scaledSolution a b c d e t := by
    rw [smul_sub, Matrix.mul_assoc Jᵀ, hsolve, Matrix.mul_smul]
  change scaledSchur a b c d e t =
    diagonal (rowScales c d) * (trailing b c - Jᵀ * leadingInverse c d * J)
  apply smul_right_injective _ (show z ≠ 0 from mul_ne_zero hd hc)
  change z • scaledSchur a b c d e t =
    z • (diagonal (rowScales c d) * (trailing b c - Jᵀ * leadingInverse c d * J))
  rw [← Matrix.mul_smul (diagonal (rowScales c d)) z, hinner]
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp only [z, J, scaledSchur, Matrix.diagonal_mul, rowScales, Matrix.smul_apply,
      smul_eq_mul, joining, joiningFirst, joiningSecond, trailing, scaledSolution,
      Matrix.sub_apply, Matrix.transpose_apply, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_four, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply, Matrix.cons_val,
      Matrix.cons_val_zero', Matrix.cons_val_succ', zero_mul, mul_zero, zero_add, add_zero] <;>
    ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 60000000 in
private theorem det_scaledSchur (a b c d e t : ℝ) :
    (scaledSchur a b c d e t).det =
      -4 * d * (c + 1) ^ 2 * linearFactor a b c d e t * quadraticFactor a b c d e t := by
  simp only [Matrix.det_succ_row_zero (n := 5), Matrix.det_succ_row_zero (n := 4),
    Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [scaledSchur, Fin.succAbove, Matrix.cons_val, Matrix.cons_val_zero',
    Matrix.cons_val_succ', Matrix.of_apply, linearFactor,
    linearConstant, linearSlope, quadraticFactor, quadraticConstant, quadraticLinear,
    quadraticLeading, heightDenominator, couplingParameter, rootPolynomial, linearParameter,
    constantParameter, q, p]
  <;> ring

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
  let S := schur H c d
  have hSchurMatrix : D - C * ⅟ A * B = S :=
    congrArg (fun X : Matrix LeadingIndex LeadingIndex ℝ => D - C * X * B) hInv
  have hdetFact : (Matrix.fromBlocks A B C D).det = A.det * (D - C * ⅟ A * B).det :=
    Matrix.det_fromBlocks₁₁ A B C D
  have hSchur : H.det = (d ^ 2 * (c + 1) ^ 2) * S.det := by
    calc
      H.det = (H.submatrix blockEquiv blockEquiv).det :=
        (Matrix.det_submatrix_equiv_self blockEquiv H).symm
      _ = (Matrix.fromBlocks A B C D).det := congrArg
        (fun X : Matrix (LeadingIndex ⊕ Fin 6) (LeadingIndex ⊕ Fin 6) ℝ => X.det) hblock
      _ = A.det * (D - C * ⅟ A * B).det := hdetFact
      _ = (d ^ 2 * (c + 1) ^ 2) * S.det := congrArg₂ (· * ·) hAdet
        (congrArg (fun X : Matrix (Fin 6) (Fin 6) ℝ => X.det) hSchurMatrix)
  have hScaled : d ^ 3 * (c + 1) ^ 4 * S.det =
      -4 * d * (c + 1) ^ 2 * linearFactor a b c d e t * quadraticFactor a b c d e t := by
    calc
      _ = (diagonal (rowScales c d)).det * S.det :=
        congrArg (fun x : ℝ => x * S.det) (det_rowScales c d).symm
      _ = (diagonal (rowScales c d) * S).det := (Matrix.det_mul _ _).symm
      _ = (scaledSchur a b c d e t).det := congrArg
        (fun X : Matrix (Fin 6) (Fin 6) ℝ => X.det)
        (scaledSchur_eq a b c d e t hc1.ne' hd.ne').symm
      _ = _ := det_scaledSchur a b c d e t
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
  let F (r : ℝ) := (fourMatchingHessian (lift a b c d e r)).det
  let u := -4 * linearSlope a b c d e * quadraticSlope a b c d e t
  let v := -4 * linearSlope a b c d e * quadraticLeading a b c d e
  have hzero : F t = 0 := hessian_singular_of_spectralLift hs
  have hplus : F (t + 1) = u + v := by
    refine (hessian_det_eq_factor_product a b c d e (t + 1) hc hd).trans ?_
    simpa only [u, v, one_pow, mul_one] using hexp 1
  have hminus : F (t - 1) = u + v * (-1) ^ 3 := by
    refine (hessian_det_eq_factor_product a b c d e (t - 1) hc hd).trans ?_
    have h := hexp (-1)
    rw [← sub_eq_add_neg] at h
    simpa only [u, v, neg_sq, one_pow, mul_one] using h
  have hdiff : F (t + 1) + F (t - 1) - 2 * F t = u + u := by
    rw [hplus, hminus, hzero]
    ring
  change 0 < F (t + 1) + F (t - 1) - 2 * F t
  rw [hdiff]
  exact add_pos hpos hpos

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

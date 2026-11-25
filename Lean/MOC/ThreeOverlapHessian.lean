import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Exact coefficients and curvature tests for three overlapping order-three
rotations. Each pair can pass while the three rotations together fail. -/

open BigOperators Matrix

namespace MOC

/-- When a pair saturates the positive semidefinite bound, its null direction
has zero mixed coefficient with the third direction. -/
theorem three_direction_mixed_eq_of_saturated_pair (a b c d e f : ℝ)
    (h : ∀ x y z : ℝ,
      0 ≤ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + 2 * d * x * y + 2 * e * x * z + 2 * f * y * z)
    (hsat : a * b = d ^ 2) : b * e = d * f := by
  have hc : 0 ≤ c := by simpa using h 0 0 1
  let v := b * e - d * f
  have hconst : a * b ^ 2 - b * d ^ 2 = 0 := by
    calc
      _ = b * (a * b - d ^ 2) := by ring
      _ = 0 := by rw [hsat, sub_self, mul_zero]
  have htest (z : ℝ) : 0 ≤ c * z ^ 2 + 2 * v * z := by
    dsimp only [v]
    nlinarith only [h b (-d) z, hconst]
  apply sub_eq_zero.mp
  change v = 0
  by_contra hv
  have hp : 0 < c + 1 := by linarith only [hc]
  have hvalue := htest (-v / (c + 1))
  have he : c * (-v / (c + 1)) ^ 2 + 2 * v * (-v / (c + 1)) =
      -((c + 2) * v ^ 2 / (c + 1) ^ 2) := by
    field_simp [hp.ne'] <;> ring
  rw [he] at hvalue
  have hpos := div_pos (mul_pos (by linarith only [hc] : 0 < c + 2) (sq_pos_of_ne_zero hv))
    (pow_pos hp 2)
  linarith only [hvalue, hpos]

private def overlapMixer : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1 / 3, -2 / 3, -2 / 3; -2 / 3, 1 / 3, -2 / 3; -2 / 3, -2 / 3, 1 / 3]

private def overlapWeightsRe : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-4, 1, 1; -16, -7 / 2, -29 / 4; -1, 31 / 4, 23 / 2]

private def overlapWeightsIm : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-9, 5, 3; -129 / 4, 25 / 2, 33 / 4; -6, 35 / 4, 9 / 2]

private def overlapEdge (s : ℚ) (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.stdBasisMatrix i (i + 1) 1 + Matrix.stdBasisMatrix (i + 1) i s

private def overlapCurvature (s : ℚ) (X Y : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  -∑ i : Fin 3, ∑ j : Fin 3, overlapWeightsRe i j *
    (2 * (X * overlapMixer) i j * (Y * overlapMixer) i j +
      s * overlapMixer i j * ((X * Y + Y * X) * overlapMixer) i j)

private def overlapSlope (X : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  2 * ∑ i : Fin 3, ∑ j : Fin 3, overlapWeightsIm i j * overlapMixer i j * (X * overlapMixer) i j

/-- Exact coefficients in the real and imaginary rotation blocks, and in
the derivative of the imaginary part, for this order-three example. -/
theorem three_overlap_exact_coefficients :
    (∀ i j, overlapCurvature 1 (overlapEdge (-1) i) (overlapEdge (-1) j) =
      if i = j then -5 else 5) ∧
    (∀ i j, overlapCurvature (-1) (overlapEdge 1 i) (overlapEdge 1 j) = -5) ∧
    (∀ i, overlapSlope (overlapEdge (-1) i) = ![-35 / 3, -80 / 3, 4 / 3] i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

/-- The real and imaginary blocks of the support Hessian. -/
noncomputable def threeOverlapHessianForm (x y z p q r : ℝ) : ℝ :=
  -10 * (x ^ 2 + y ^ 2 + z ^ 2) + 5 * (x + y + z) ^ 2 - 5 * (p + q + r) ^ 2

/-- Allowing both phases on any two of the three edges gives nonpositive curvature. -/
theorem three_overlap_hessian_pair_nonpos (x y z p q r : ℝ)
    (h : (x = 0 ∧ p = 0) ∨ (y = 0 ∧ q = 0) ∨ (z = 0 ∧ r = 0)) :
    threeOverlapHessianForm x y z p q r ≤ 0 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · norm_num [threeOverlapHessianForm]
    nlinarith only [sq_nonneg (y - z), sq_nonneg (q + r)]
  · norm_num [threeOverlapHessianForm]
    nlinarith only [sq_nonneg (x - z), sq_nonneg (p + r)]
  · norm_num [threeOverlapHessianForm]
    nlinarith only [sq_nonneg (x - y), sq_nonneg (p + q)]

theorem three_overlap_hessian_triple_pos : 0 < threeOverlapHessianForm 1 1 1 0 0 0 := by
  norm_num [threeOverlapHessianForm]

/-- The support Hessian with direction scaled by 1000 and the determinant
derivative square added, when each imaginary generator has half the weight
of the corresponding real generator. -/
noncomputable def threeOverlapPenaltyForm (x y z : ℝ) : ℝ :=
  -10000 * (x ^ 2 + y ^ 2 + z ^ 2) + 3750 * (x + y + z) ^ 2 +
    ((-35 * x - 80 * y + 4 * z) / 3) ^ 2

/-- The augmented Hessian is strictly negative on each nonzero coordinate-pair direction. -/
theorem three_overlap_penalty_pair_le (x y z : ℝ) (h : x = 0 ∨ y = 0 ∨ z = 0) :
    threeOverlapPenaltyForm x y z ≤ -1651 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  rcases h with rfl | rfl | rfl
  · norm_num [threeOverlapPenaltyForm]
    nlinarith only [sq_nonneg (y - z), sq_nonneg (4 * y + 80 * z), sq_nonneg y, sq_nonneg z]
  · norm_num [threeOverlapPenaltyForm]
    nlinarith only [sq_nonneg (x - z), sq_nonneg (4 * x + 35 * z), sq_nonneg x, sq_nonneg z]
  · norm_num [threeOverlapPenaltyForm]
    nlinarith only [sq_nonneg (x - y), sq_nonneg (80 * x - 35 * y), sq_nonneg x, sq_nonneg y]

theorem three_overlap_penalty_triple_pos : 0 < threeOverlapPenaltyForm 1 1 1 := by
  norm_num [threeOverlapPenaltyForm]

end MOC

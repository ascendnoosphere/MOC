import MOC.FourHodgeExteriorSquare
import MOC.RealCoordinateRotation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! A rotation between two different complementary-pair coordinates. -/

open Matrix

namespace MOC

/-- Apply the same real rotation to coordinates 0 and 1 and to coordinates 2 and 3. -/
noncomputable def fourHodgeCrossUnitary (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(a : ℂ), -(b : ℂ), 0, 0;
    (b : ℂ), (a : ℂ), 0, 0;
    0, 0, (a : ℂ), -(b : ℂ);
    0, 0, (b : ℂ), (a : ℂ)]

private theorem cross_norm_complex {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by
  simpa only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one] using
    congrArg (fun x : ℝ => (x : ℂ)) h

set_option maxRecDepth 4096 in
theorem fourHodgeCrossUnitary_isUnitary (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    IsUnitary (fourHodgeCrossUnitary a b) := by
  have hc := cross_norm_complex h
  constructor <;> ext i j : 1 <;> fin_cases i <;> fin_cases j <;>
    norm_num [fourHodgeCrossUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Matrix.of_apply, Matrix.cons_val, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Complex.star_def, Complex.conj_ofReal] <;>
    ring_nf at hc ⊢ <;> exact hc

private abbrev crossBlockEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv

theorem fourHodgeCrossUnitary_det (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    (fourHodgeCrossUnitary a b).det = 1 := by
  let J : Matrix (Fin 2) (Fin 2) ℂ := !![(a : ℂ), -(b : ℂ); (b : ℂ), (a : ℂ)]
  have hJ : J.det = 1 := by
    rw [Matrix.det_fin_two]
    change (a : ℂ) * (a : ℂ) - (-(b : ℂ)) * (b : ℂ) = 1
    linear_combination (cross_norm_complex h)
  have hblock : (fourHodgeCrossUnitary a b).submatrix crossBlockEquiv crossBlockEquiv =
      Matrix.fromBlocks J 0 0 J := by
    ext (i | i) (j | j) : 1 <;> fin_cases i <;> fin_cases j <;> rfl
  rw [← Matrix.det_submatrix_equiv_self crossBlockEquiv (fourHodgeCrossUnitary a b),
    hblock, Matrix.det_fromBlocks_zero₂₁, hJ, one_mul]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- On the Hodge real form, the two equal rotations move only the plane
of the two indicated sum vectors. The complementary-pair orientation
is `(01,23)`, `(02,31)`, `(03,12)`. -/
theorem fourHodgeRealRepresentation_cross (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    fourHodgeRealRepresentation (fourHodgeCrossUnitary a b) =
      realCoordinateRotation ((1, 0) : HodgeIndex) (2, 0) (a ^ 2 - b ^ 2) (2 * a * b) := by
  have hu := fourHodgeCrossUnitary_isUnitary a b h
  have hd := fourHodgeCrossUnitary_det a b h
  ext ⟨i, k⟩ ⟨j, l⟩ : 1
  rw [fourHodgeRealRepresentation_block _ hu hd]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp (config := { decide := true }) only [hodgeRealBlock, fourHodgeCrossUnitary, fourHodgeCompound, fourHodgePair,
      realCoordinateRotation, Matrix.of_apply, Matrix.cons_val, Fin.succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_add, add_zero, sub_zero, zero_sub,
      zero_mul, mul_zero, one_mul, mul_one, neg_zero] <;>
    nlinarith only [h]

private theorem exists_cross_half_angle (c s : ℝ) (hc : c ^ 2 + s ^ 2 = 1) :
    ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧ a ^ 2 - b ^ 2 = c ∧ 2 * a * b = s := by
  let w : ℂ := ⟨c, s⟩
  have hw : Complex.normSq w = 1 := by
    simpa only [w, Complex.normSq_apply, pow_two] using hc
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) two_pos
  have hsq : Complex.normSq z ^ 2 = 1 := by rw [← map_pow, hz, hw]
  have hn : Complex.normSq z = 1 :=
    (sq_eq_sq₀ (Complex.normSq_nonneg z) zero_le_one).mp (by simpa only [one_pow] using hsq)
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  refine ⟨z.re, z.im, ?_, ?_, ?_⟩
  · simpa only [Complex.normSq_apply, pow_two] using hn
  · simpa only [w, pow_two, Complex.mul_re] using hre
  · simp only [w, pow_two, Complex.mul_im] at him
    linear_combination him

/-- Every real rotation on the indicated cross plane has a lift with
determinant one. -/
theorem exists_fourHodgeCrossRotation (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary U ∧ U.det = 1 ∧
      fourHodgeRealRepresentation U = realCoordinateRotation ((1, 0) : HodgeIndex) (2, 0) c s := by
  obtain ⟨a, b, hab, hc, hs⟩ := exists_cross_half_angle c s h
  refine ⟨fourHodgeCrossUnitary a b, fourHodgeCrossUnitary_isUnitary a b hab,
    fourHodgeCrossUnitary_det a b hab, ?_⟩
  rw [fourHodgeRealRepresentation_cross a b hab, hc, hs]

end MOC

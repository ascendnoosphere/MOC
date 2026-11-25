import MOC.FourContactCertificate
import MOC.FourMatchingHessianMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Fraction-free pivot identities for the T34 Hessian. -/

namespace MOC

open BigOperators Matrix

noncomputable section

variable {R : Type*} [CommRing R]

/-- The matrix of two-by-two minors containing the leading pivot. -/
def leadingPivotMinor {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => A 0 0 * A i.succ j.succ - A i.succ 0 * A 0 j.succ

private def leadingPivotMultiplier {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Fin.cases (Fin.cases 1 fun _ => 0)
    (fun i => Fin.cases (-A i.succ 0) fun j => if i = j then A 0 0 else 0)

private theorem det_leadingPivotMultiplier {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (leadingPivotMultiplier A).det = A 0 0 ^ n := by
  have h00 : leadingPivotMultiplier A 0 0 = 1 := rfl
  have h0s (j : Fin n) : leadingPivotMultiplier A 0 j.succ = 0 := rfl
  have hdiag : (leadingPivotMultiplier A).submatrix Fin.succ Fin.succ =
      Matrix.diagonal (fun _ : Fin n => A 0 0) := by
    ext i j
    simp [leadingPivotMultiplier, Matrix.diagonal_apply]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [h00, h0s, Fin.succAbove_zero, hdiag, Matrix.det_diagonal, Finset.prod_const]

private theorem leadingPivotMultiplier_mul_succ {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin n) (j : Fin (n + 1)) :
    (leadingPivotMultiplier A * A) i.succ j =
      A 0 0 * A i.succ j - A i.succ 0 * A 0 j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, leadingPivotMultiplier,
    Fin.cases_succ, Fin.cases_zero, neg_mul, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg, add_comm]

private theorem det_leadingPivotMultiplier_mul {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (leadingPivotMultiplier A * A).det = A 0 0 * (leadingPivotMinor A).det := by
  have hp : (leadingPivotMultiplier A * A) 0 0 = A 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ, leadingPivotMultiplier]
  have hz (i : Fin n) : (leadingPivotMultiplier A * A) i.succ 0 = 0 := by
    rw [leadingPivotMultiplier_mul_succ, mul_comm (A 0 0), sub_self]
  have hr : (leadingPivotMultiplier A * A).submatrix Fin.succ Fin.succ =
      leadingPivotMinor A := by
    ext i j
    exact leadingPivotMultiplier_mul_succ A i j.succ
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [hp, hz, hr, Fin.succAbove_zero]

/-- Fraction-free elimination preserves the determinant up to the pivot power. -/
theorem det_leadingPivotMinor {n : ℕ} [IsDomain R]
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (hp : A 0 0 ≠ 0) :
    (leadingPivotMinor A).det = A 0 0 ^ n * A.det := by
  have h := (det_leadingPivotMultiplier_mul A).symm.trans (Matrix.det_mul _ _)
  rw [det_leadingPivotMultiplier, pow_succ', mul_assoc] at h
  exact mul_left_cancel₀ hp h

/-- A nonzero pivot transfers singularity to its fraction-free minors. -/
theorem det_leadingPivotMinor_eq_zero_iff {n : ℕ} [IsDomain R]
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (hp : A 0 0 ≠ 0) :
    (leadingPivotMinor A).det = 0 ↔ A.det = 0 := by
  rw [det_leadingPivotMinor A hp, mul_eq_zero]
  simp [pow_ne_zero n hp]

/-- A nonsingular leading block and scaled right inverse columns for the
remaining indices certify nonsingularity of the full matrix. -/
theorem det_fromBlocks_ne_zero_of_right_columns {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [IsDomain R]
    (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R) (D : Matrix κ κ R)
    (X : Matrix ι κ R) (Y : Matrix κ κ R) (z : R)
    (hA : A.det ≠ 0) (hz : z ≠ 0) (hX : A * X + B * Y = 0)
    (hY : C * X + D * Y = z • (1 : Matrix κ κ R)) :
    (Matrix.fromBlocks A B C D).det ≠ 0 := by
  intro hsingular
  have hproduct : Matrix.fromBlocks A B C D * Matrix.fromBlocks (1 : Matrix ι ι R) X 0 Y =
      Matrix.fromBlocks A 0 C (z • (1 : Matrix κ κ R)) := by
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, add_zero, hX, hY]
  have hdet := congrArg Matrix.det hproduct
  rw [Matrix.det_mul, hsingular, zero_mul, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  exact (mul_ne_zero hA (pow_ne_zero _ hz)) hdet.symm

/-- Scaling a T34 lift scales the entries of the Hessian uniformly. -/
theorem t34_heightLift_scale (z p r a b c q d s h : ℝ) :
    t34HeightLift (z * p) (z * r) (z * a) (z * b) (z * c) (z * q) (z * d)
      (z * s) (z * h) = fun i => z * t34HeightLift p r a b c q d s h i := by
  funext i
  fin_cases i <;> simp [t34HeightLift] <;> ring

/-- The radial height denominator is homogeneous of degree two. -/
theorem t34_radialQ_normalize (a b c d r s : ℝ) (hd : d ≠ 0) :
    t34RadialQ (a / d) (b / d) (c / d) 1 (r / d) (s / d) = t34RadialQ a b c d r s / d ^ 2 := by
  unfold t34RadialQ
  field_simp [hd]
  <;> ring

/-- The mixed coefficient can be set to one before evaluating the Hessian
determinant at the cubic height. -/
theorem t34_hessian_at_radial_height_normalize (p r a b c q d s : ℝ)
    (hd : d ≠ 0) (hQ : t34RadialQ a b c d r s ≠ 0) :
    let C := t34RadialC p r a b c q d s
    let Q := t34RadialQ a b c d r s
    let C' := t34RadialC (p / d) (r / d) (a / d) (b / d) (c / d) (q / d) 1 (s / d)
    let Q' := t34RadialQ (a / d) (b / d) (c / d) 1 (r / d) (s / d)
    (fourMatchingHessian (t34HeightLift (p / d) (r / d) (a / d) (b / d) (c / d)
      (q / d) 1 (s / d) (-C' / Q'))).det =
      d⁻¹ ^ 14 * (fourMatchingHessian (t34HeightLift p r a b c q d s (-C / Q))).det := by
  dsimp only
  let C := t34RadialC p r a b c q d s
  let Q := t34RadialQ a b c d r s
  have hQ' : t34RadialQ (a / d) (b / d) (c / d) 1 (r / d) (s / d) = Q / d ^ 2 := by
    exact t34_radialQ_normalize a b c d r s hd
  have hC' : t34RadialC (p / d) (r / d) (a / d) (b / d) (c / d) (q / d) 1 (s / d) =
      C / d ^ 3 := by
    dsimp only [C, t34RadialC]
    field_simp [hd]
    <;> ring
  rw [hC', hQ']
  have hh : -(C / d ^ 3) / (Q / d ^ 2) = d⁻¹ * (-C / Q) := by
    field_simp [hd, show Q ≠ 0 from hQ]
    <;> ring
  rw [hh]
  have hscale : t34HeightLift (p / d) (r / d) (a / d) (b / d) (c / d) (q / d)
      1 (s / d) (d⁻¹ * (-C / Q)) = fun i => d⁻¹ * t34HeightLift p r a b c q d s (-C / Q) i := by
    simpa only [← div_eq_inv_mul, div_self hd] using
      t34_heightLift_scale d⁻¹ p r a b c q d s (-C / Q)
  rw [hscale, fourMatchingHessian_scale, Matrix.det_smul, Fintype.card_fin]

private theorem t34HessianPivotUnit_sq : t34HessianPivotUnit * t34HessianPivotUnit = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [t34HessianPivotUnit, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

private theorem t34HessianPivotUnit_det : t34HessianPivotUnit.det = 1 := by
  norm_num [t34HessianPivotUnit, Matrix.det_succ_row_zero, Matrix.det_fin_zero,
    Fin.sum_univ_succ, Fin.succAbove, Matrix.submatrix_apply]

private def t34HessianPivotSchur (a b q s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -a - 1, 0, 0;
     -a - 1, 2 * (q - b) * (a + b + 1), q * (a + b + 1), b - q;
     0, q * (a + b + 1), 0, -q - s - 1;
     0, b - q, -q - s - 1, 0]

private theorem t34HessianPivotSchur_eq (a b q s : ℝ) :
    t34HessianPivotTail b q s - (t34HessianPivotCross a b q)ᵀ *
        t34HessianPivotUnit * t34HessianPivotCross a b q = t34HessianPivotSchur a b q s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [t34HessianPivotTail, t34HessianPivotCross, t34HessianPivotUnit,
      t34HessianPivotSchur, Matrix.sub_apply, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

private theorem t34HessianPivotSchur_det (a b q s : ℝ) :
    (t34HessianPivotSchur a b q s).det = (a + 1) ^ 2 * (q + s + 1) ^ 2 := by
  norm_num [t34HessianPivotSchur, Matrix.det_succ_row_zero, Matrix.det_fin_zero,
    Fin.sum_univ_succ, Fin.succAbove, Matrix.submatrix_apply] <;> ring

/-- The first eight pivots of the normalized T34 Hessian form an invertible
block whenever the anchor and the two named gaps are nonnegative. -/
theorem t34Hessian_pivotBlock_det (p r a b c q s h : ℝ) :
    ((fourMatchingHessian (t34HeightLift p r a b c q 1 s h)).submatrix
      t34HessianPivotIndices t34HessianPivotIndices).det = (a + 1) ^ 2 * (q + s + 1) ^ 2 := by
  letI : Invertible t34HessianPivotUnit :=
    ⟨t34HessianPivotUnit, t34HessianPivotUnit_sq, t34HessianPivotUnit_sq⟩
  have hInv : ⅟ t34HessianPivotUnit = t34HessianPivotUnit :=
    invOf_eq_right_inv t34HessianPivotUnit_sq
  rw [t34Hessian_pivotBlock, Matrix.det_fromBlocks₁₁, hInv, t34HessianPivotUnit_det,
    one_mul, t34HessianPivotSchur_eq, t34HessianPivotSchur_det]

private def t34HessianRemainingIndices : Fin 6 → Fin 14 := ![6, 9, 10, 5, 0, 8]

private def t34HessianBlockIndex : (Fin 4 ⊕ Fin 4) ⊕ Fin 6 → Fin 14 :=
  Sum.elim t34HessianPivotIndices t34HessianRemainingIndices

private def t34HessianBlockIndexInverse : Fin 14 → (Fin 4 ⊕ Fin 4) ⊕ Fin 6 :=
  ![.inr 4, .inl (.inl 0), .inl (.inr 2), .inl (.inr 0), .inl (.inl 1),
    .inr 3, .inr 0, .inl (.inr 1), .inr 5, .inr 1, .inr 2, .inl (.inl 2),
    .inl (.inr 3), .inl (.inl 3)]

private def t34HessianBlockEquiv : (Fin 4 ⊕ Fin 4) ⊕ Fin 6 ≃ Fin 14 where
  toFun := t34HessianBlockIndex
  invFun := t34HessianBlockIndexInverse
  left_inv := by
    change ∀ i, t34HessianBlockIndexInverse (t34HessianBlockIndex i) = i
    decide +kernel
  right_inv := by
    change ∀ i, t34HessianBlockIndex (t34HessianBlockIndexInverse i) = i
    decide +kernel

/-- The six-by-six Schur complement of the T34 leading pivot block. -/
def t34HessianSchur (H : Matrix (Fin 14) (Fin 14) ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  let A := H.submatrix t34HessianPivotIndices t34HessianPivotIndices
  let B := H.submatrix t34HessianPivotIndices t34HessianRemainingIndices
  let C := H.submatrix t34HessianRemainingIndices t34HessianPivotIndices
  let D := H.submatrix t34HessianRemainingIndices t34HessianRemainingIndices
  D - C * A⁻¹ * B

/-- The normalized Hessian determinant reduces to its six-by-six Schur complement. -/
theorem t34Hessian_det_eq_schur (p r a b c q s h : ℝ)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s h)
    H.det = (a + 1) ^ 2 * (q + s + 1) ^ 2 * (t34HessianSchur H).det := by
  let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s h)
  let A := H.submatrix t34HessianPivotIndices t34HessianPivotIndices
  let B := H.submatrix t34HessianPivotIndices t34HessianRemainingIndices
  let C := H.submatrix t34HessianRemainingIndices t34HessianPivotIndices
  let D := H.submatrix t34HessianRemainingIndices t34HessianRemainingIndices
  have hA : A.det = (a + 1) ^ 2 * (q + s + 1) ^ 2 :=
    t34Hessian_pivotBlock_det p r a b c q s h
  have hunit : IsUnit A.det := by
    rw [hA, isUnit_iff_ne_zero]
    positivity
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hunit
  have hblock : H.submatrix t34HessianBlockEquiv t34HessianBlockEquiv =
      Matrix.fromBlocks A B C D := by
    ext i j
    cases i <;> cases j <;> rfl
  change H.det = _
  rw [← Matrix.det_submatrix_equiv_self t34HessianBlockEquiv H, hblock,
    Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, hA] <;> rfl

set_option maxHeartbeats 2000000 in
/-- The ninth pivot has a positive factorization in the normalized gaps. -/
theorem t34Hessian_schur_zero_zero (p r a b c q s h : ℝ)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s h)
    t34HessianSchur H 0 0 = 2 * (b + p + 1) * ((b + c + 1) * q + c + 1) / (q + s + 1) := by
  let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s h)
  let A := H.submatrix t34HessianPivotIndices t34HessianPivotIndices
  let B := H.submatrix t34HessianPivotIndices t34HessianRemainingIndices
  let C := H.submatrix t34HessianRemainingIndices t34HessianPivotIndices
  let D := H.submatrix t34HessianRemainingIndices t34HessianRemainingIndices
  let u := q + s + 1
  let v := (b + c + 1) * q + c + 1
  let w := b + p + 1
  let x₆ := -w / u
  let x₇ := -v / u
  let x₁ := ((q + 1 - b) * (b + c + 1) - b * q * x₆ - (b - q) * x₇) / (a + 1)
  let x : Fin 4 ⊕ Fin 4 → ℝ :=
    Sum.elim (![b + c + 1, x₁, 0, -(q + 1) * x₆ - x₇]) (![q * x₆ - x₁, 0, x₆, x₇])
  have hau : a + 1 ≠ 0 := by positivity
  have hu : q + s + 1 ≠ 0 := by positivity
  obtain ⟨h66, hcol, hrow⟩ := t34Hessian_ninth_entries p r a b c q s h
  have hA : IsUnit A.det := by
    rw [show A.det = (a + 1) ^ 2 * (q + s + 1) ^ 2 from
      t34Hessian_pivotBlock_det p r a b c q s h, isUnit_iff_ne_zero]
    positivity
  have hblock : A = Matrix.fromBlocks t34HessianPivotUnit (t34HessianPivotCross a b q)
      (t34HessianPivotCross a b q)ᵀ (t34HessianPivotTail b q s) :=
    t34Hessian_pivotBlock p r a b c q s h
  have hx : A.mulVec x = t34HessianNinthColumn p b c := by
    rw [hblock]
    funext i
    rcases i with i | i <;> fin_cases i <;>
      norm_num [t34HessianPivotUnit, t34HessianPivotCross, t34HessianPivotTail,
        t34HessianNinthColumn, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Fintype.sum_sum_type, Fin.sum_univ_succ, x, x₁, x₆, x₇, u, v, w] <;>
      field_simp [hau, hu] <;> ring
  have hsol : (A⁻¹).mulVec (t34HessianNinthColumn p b c) = x := by
    rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
  have hprod (i : Fin 4 ⊕ Fin 4) : (A⁻¹ * B) i 0 = x i := by
    change (A⁻¹).mulVec (fun j => H (t34HessianPivotIndices j) 6) i = x i
    simp only [hcol, hsol]
  change (D - C * A⁻¹ * B) 0 0 = _
  rw [Matrix.mul_assoc, Matrix.sub_apply, Matrix.mul_apply]
  change H 6 6 - (∑ i, H 6 (t34HessianPivotIndices i) * (A⁻¹ * B) i 0) = _
  norm_num [h66, hrow, hprod, t34HessianNinthColumn, Fintype.sum_sum_type,
    Fin.sum_univ_succ, x, x₁, x₆, x₇, u, v, w] <;> field_simp [hu] <;> ring

/-- Singularity of the normalized Hessian is detected by five-by-five minors
after the nine pivots with nonnegative gaps. -/
theorem t34Hessian_det_eq_zero_iff_reduced (p r a b c q s h : ℝ)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s h)
    H.det = 0 ↔ (leadingPivotMinor (t34HessianSchur H)).det = 0 := by
  let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s h)
  have hblock : (a + 1) ^ 2 * (q + s + 1) ^ 2 ≠ 0 := by positivity
  have hpivot : (t34HessianSchur H) 0 0 ≠ 0 := by
    rw [show (t34HessianSchur H) 0 0 = _ from t34Hessian_schur_zero_zero p r a b c q s h ha hq hs]
    positivity
  change H.det = 0 ↔ _
  rw [t34Hessian_det_eq_schur p r a b c q s h ha hq hs, mul_eq_zero,
    det_leadingPivotMinor_eq_zero_iff _ hpivot]
  simp [hblock]

private def t34HessianNineEquiv : ((Fin 4 ⊕ Fin 4) ⊕ Fin 1) ⊕ Fin 5 ≃ Fin 14 :=
  (Equiv.sumAssoc (Fin 4 ⊕ Fin 4) (Fin 1) (Fin 5)).trans
    ((Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv : Fin 1 ⊕ Fin 5 ≃ Fin 6)).trans
      t34HessianBlockEquiv)

/-- The five indices left after the nine nonzero pivots. -/
def t34HessianTrailingIndices (j : Fin 5) : Fin 14 := t34HessianNineEquiv (.inr j)

private theorem t34Hessian_nine_det_ne_zero (p r a b c q s h : ℝ)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s h)
    let e := t34HessianNineEquiv ∘ Sum.inl
    (H.submatrix e e).det ≠ 0 := by
  let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s h)
  let e := t34HessianNineEquiv ∘ Sum.inl
  let A := H.submatrix t34HessianPivotIndices t34HessianPivotIndices
  let B := H.submatrix t34HessianPivotIndices (fun j : Fin 1 => e (.inr j))
  let C := H.submatrix (fun i : Fin 1 => e (.inr i)) t34HessianPivotIndices
  let D := H.submatrix (fun i : Fin 1 => e (.inr i)) (fun j : Fin 1 => e (.inr j))
  have hblock : H.submatrix e e = Matrix.fromBlocks A B C D := by
    ext i j : 1
    cases i <;> cases j <;> rfl
  have hA : A.det ≠ 0 := by
    change (H.submatrix t34HessianPivotIndices t34HessianPivotIndices).det ≠ 0
    rw [t34Hessian_pivotBlock_det p r a b c q s h]
    positivity
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA)
  have hpivot : (D - C * A⁻¹ * B) 0 0 = t34HessianSchur H 0 0 := rfl
  change (H.submatrix e e).det ≠ 0
  rw [hblock, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, Matrix.det_fin_one, hpivot,
    t34Hessian_schur_zero_zero p r a b c q s h ha hq hs]
  exact mul_ne_zero hA (by positivity)

/-- Five scaled inverse columns suffice to certify a normalized T34 Hessian. -/
theorem t34Hessian_det_ne_zero_of_right_columns (p r a b c q s h z : ℝ)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hz : z ≠ 0) (W : Matrix (Fin 14) (Fin 5) ℝ)
    (hW : fourMatchingHessian (t34HeightLift p r a b c q 1 s h) * W =
      fun i j => if i = t34HessianTrailingIndices j then z else 0) :
    (fourMatchingHessian (t34HeightLift p r a b c q 1 s h)).det ≠ 0 := by
  let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s h)
  let e := t34HessianNineEquiv
  let A := H.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)
  let B := H.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)
  let C := H.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)
  let D := H.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
  let X := W.submatrix (e ∘ Sum.inl) id
  let Y := W.submatrix (e ∘ Sum.inr) id
  have hblock : H.submatrix e e = Matrix.fromBlocks A B C D := by
    ext i j : 1
    cases i <;> cases j <;> rfl
  have hentry (i : ((Fin 4 ⊕ Fin 4) ⊕ Fin 1) ⊕ Fin 5) (j : Fin 5) :
      (H.submatrix e e * W.submatrix e id) i j = if i = .inr j then z else 0 := by
    rw [Matrix.submatrix_mul_equiv, show H * W = _ from hW]
    change (if e i = e (.inr j) then z else 0) = _
    rw [e.injective.eq_iff]
  have hX : A * X + B * Y = 0 := by
    ext i j : 1
    simpa only [A, B, X, Y, Matrix.add_apply, Matrix.mul_apply, Matrix.submatrix_apply,
      Function.comp_apply, id_eq, Fintype.sum_sum_type, Sum.inl_ne_inr, if_false,
      Matrix.zero_apply] using hentry (.inl i) j
  have hY : C * X + D * Y = z • (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
    ext i j : 1
    simpa only [C, D, X, Y, Matrix.add_apply, Matrix.mul_apply, Matrix.submatrix_apply,
      Function.comp_apply, id_eq, Fintype.sum_sum_type, Sum.inr.injEq, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] using hentry (.inr i) j
  change H.det ≠ 0
  rw [← Matrix.det_submatrix_equiv_self e H, hblock]
  exact det_fromBlocks_ne_zero_of_right_columns A B C D X Y z
    (t34Hessian_nine_det_ne_zero p r a b c q s h hp ha hb hc hq hs) hz hX hY

end

end MOC

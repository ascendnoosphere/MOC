import MOC.RankOneOrbitDeterminant
import MOC.Realification

/-!
A symbolic rank-one reflection test for a complex symmetric pair. Unlike
arbitrary first-order stationarity, this is an exact finite displacement test.
-/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full real rank-one phase arc of a transpose-symmetric pair maps to
the segment joining the original determinant to the reflected determinant.
The matrices and their determinants need not be real. -/
theorem symmetric_rankOnePhase_det_segment (A B : Matrix ι ι ℂ) (u : ι → ℝ)
    (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hu : ∑ i, star (u i : ℂ) * (u i : ℂ) = 1)
    (hz : z * star z = (1 : ℂ)) (hd : IsUnit (A + B).det) :
    let v : ι → ℂ := fun i => u i
    let V := rankOnePhase v z
    let R := rankOnePhase v (-1)
    (V * A * Vᴴ + B).det =
      (A + B).det + ((1 - z.re) / 2 : ℝ) • ((R * A * Rᴴ + B).det - (A + B).det) := by
  intro v V R
  let T := A + B
  let L : Matrix ι Unit ℂ := fun i _ => v i
  let α := (Lᴴ * A * T⁻¹ * L) () ()
  let β := (Lᴴ * T⁻¹ * (B * L)) () ()
  let γ := (Lᴴ * A * T⁻¹ * (B * L)) () ()
  let ε := (Lᴴ * T⁻¹ * L) () ()
  have hL : Lᴴ = Lᵀ := by ext i j; simp [L, v, Matrix.conjTranspose_apply, Complex.star_def]
  have hT : Tᵀ = T := by simp [T, hA, hB]
  have hi : (T⁻¹)ᵀ = T⁻¹ := by
    rw [Matrix.inv_def, Matrix.transpose_smul, Matrix.adjugate_transpose, hT]
  have halpha : α = (Lᴴ * T⁻¹ * (A * L)) () () := by
    have h := congrArg (fun M : Matrix Unit Unit ℂ => M () ())
      (show (Lᴴ * A * T⁻¹ * L)ᵀ = Lᴴ * T⁻¹ * (A * L) by
        simp only [Matrix.transpose_mul, hi, hA, Matrix.mul_assoc]
        rw [hL, Matrix.transpose_transpose])
    exact h
  have hab : α + β = 1 := by
    rw [halpha]
    change (Lᴴ * T⁻¹ * (A * L)) () () + (Lᴴ * T⁻¹ * (B * L)) () () = _
    rw [← Matrix.add_apply, ← Matrix.mul_add, ← Matrix.add_mul]
    change (Lᴴ * T⁻¹ * (T * L)) () () = _
    rw [← Matrix.mul_assoc _ T L, Matrix.mul_assoc Lᴴ, T.nonsing_inv_mul hd,
      Matrix.mul_one]
    simpa only [L, Matrix.mul_apply, Matrix.conjTranspose_apply] using hu
  have hform (w : ℂ) (hw : w * star w = 1) :
      ((rankOnePhase v w) * A * (rankOnePhase v w)ᴴ + B).det =
        T.det * (1 + (w + star w - 2) * (α * β - γ * ε)) := by
    have h := det_rankOnePhase_left_conjugation A (-B) v hu w hw
    simp only [sub_neg_eq_add, Matrix.neg_mul, neg_neg, α, β, γ, ε, T] at h ⊢
    have hx : (Lᴴ * A * T⁻¹ * L) () () + (Lᴴ * T⁻¹ * (B * L)) () () - 1 = 0 :=
      sub_eq_zero.mpr hab
    specialize h hd
    change _ = T.det *
      (1 + (1 - star w) * ((Lᴴ * A * T⁻¹ * L) () () + (Lᴴ * T⁻¹ * (B * L)) () () - 1) +
         (w + star w - 2) * (α * β - γ * ε)) at h
    simpa only [hx, mul_zero, add_zero] using h
  change ((rankOnePhase v z) * A * (rankOnePhase v z)ᴴ + B).det =
    T.det + ((1 - z.re) / 2 : ℝ) •
      (((rankOnePhase v (-1)) * A * (rankOnePhase v (-1))ᴴ + B).det - T.det)
  rw [hform z hz, hform (-1) (by simp)]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat, star_neg, star_one]
  have hz' : z + star z = 2 * (z.re : ℂ) := by
    apply Complex.ext <;> simp [Complex.star_def, Complex.mul_re, Complex.mul_im, two_mul]
  rw [hz']
  ring


/-- A single reflection is an exact support test for the whole rank-one
phase circle. In particular a real orthogonal candidate can only be a
maximum if every real rank-one reflection is non-improving. -/
theorem four_orthogonal_rankOnePhase_support_iff_reflection
    (a b : Fin 4 → ℂ) (η : ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (u : Fin 4 → ℝ) (hu : ∑ i, star (u i : ℂ) * (u i : ℂ) = 1)
    (hd : determinantValue a b (Complex.ofRealHom.mapMatrix O.val) ≠ 0) :
    let U := Complex.ofRealHom.mapMatrix O.val
    let v : Fin 4 → ℂ := fun i => u i
    let f (z : ℂ) := (η * determinantValue a b (rankOnePhase v z * U)).re
    (∀ z : ℂ, z * star z = 1 → f z ≤ (η * determinantValue a b U).re) ↔
      f (-1) ≤ (η * determinantValue a b U).re := by
  intro U v f
  constructor
  · intro h
    exact h (-1) (by simp)
  · intro h z hz
    let B := U * diagonal b * Uᴴ
    have hUT : Uᵀ = Uᴴ := by
      ext i j
      simp [U, Matrix.conjTranspose_apply, Complex.star_def]
    have hUHT : (Uᴴ)ᵀ = U := by rw [← hUT, Matrix.transpose_transpose]
    have hBT : Bᵀ = B := by
      simp only [B, Matrix.transpose_mul, Matrix.diagonal_transpose, hUHT, hUT, Matrix.mul_assoc]
    have hunit : IsUnit (B + diagonal a).det := by
      apply isUnit_iff_ne_zero.mpr
      rwa [add_comm, ← determinantValue]
    have hdet := symmetric_rankOnePhase_det_segment B (diagonal a) u hBT
      (Matrix.diagonal_transpose _) hu hz hunit
    have hvalue (w : ℂ) :
        (rankOnePhase v w * B * (rankOnePhase v w)ᴴ + diagonal a).det =
          determinantValue a b (rankOnePhase v w * U) := by
      simp only [determinantValue, B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [add_comm]
    change (rankOnePhase v z * B * (rankOnePhase v z)ᴴ + diagonal a).det =
      (B + diagonal a).det + ((1 - z.re) / 2 : ℝ) •
        ((rankOnePhase v (-1) * B * (rankOnePhase v (-1))ᴴ + diagonal a).det -
          (B + diagonal a).det) at hdet
    rw [hvalue, hvalue, add_comm B (diagonal a)] at hdet
    change determinantValue a b (rankOnePhase v z * U) =
      determinantValue a b U + ((1 - z.re) / 2 : ℝ) •
        (determinantValue a b (rankOnePhase v (-1) * U) - determinantValue a b U) at hdet
    change (η * determinantValue a b (rankOnePhase v z * U)).re ≤ _
    rw [hdet, mul_add, Complex.add_re]
    have hwt : 0 ≤ (1 - z.re) / 2 := by
      have hn : z * (starRingEnd ℂ) z = (1 : ℂ) := hz
      rw [Complex.mul_conj] at hn
      have hsq : Complex.normSq z = 1 := by exact_mod_cast hn
      have hr := Complex.re_sq_le_normSq z
      rw [hsq] at hr
      apply div_nonneg _ (by norm_num)
      nlinarith
    rw [Complex.real_smul, mul_left_comm, Complex.re_ofReal_mul]
    rw [mul_sub, Complex.sub_re]
    change _ + ((1 - z.re) / 2) * (f (-1) - (η * determinantValue a b U).re) ≤ _
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hwt (sub_nonpos.mpr h))

end

end MOC

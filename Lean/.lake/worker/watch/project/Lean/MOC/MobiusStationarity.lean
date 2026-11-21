import MOC.SpectralMobius

/-! The determinant stationarity matrix and the quadratic support penalty
under a regular fractional-linear change of spectra. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse commutator survives the simultaneous fractional-linear
changes with opposite parameters. The matrix identity does not use normality. -/
theorem inverse_commutator_mobius (A B : Matrix ι ι ℂ) (t : ℂ)
    (hC : IsUnit (A + B).det)
    (hY : IsUnit (1 - t • A).det) (hX : IsUnit (1 + t • B).det) :
    let C := A + B
    let Y := 1 - t • A
    let X := 1 + t • B
    let Bt := B * X⁻¹
    let Ct := Y⁻¹ * C * X⁻¹
    Bt * Ct⁻¹ - Ct⁻¹ * Bt = B * C⁻¹ - C⁻¹ * B := by
  intro C Y X Bt Ct
  have hYX : Y = X - t • C := by
    dsimp only [Y, X, C]
    rw [smul_add]
    abel
  have hRY : C⁻¹ * Y = C⁻¹ * X - t • (1 : Matrix ι ι ℂ) := by
    rw [hYX, Matrix.mul_sub, Matrix.mul_smul, Matrix.nonsing_inv_mul C hC]
  have hCt : Ct⁻¹ = X * C⁻¹ * X - t • X := by
    dsimp only [Ct]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv X hX,
      Matrix.nonsing_inv_nonsing_inv Y hY, Matrix.mul_assoc X C⁻¹ X, hRY, Matrix.mul_sub,
      Matrix.mul_smul, Matrix.mul_one]
  have hBX : B * X = X * B := by
    dsimp only [X]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hBtX : Bt * X = B := by
    dsimp only [Bt]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul X hX, Matrix.mul_one]
  have hXBt : X * Bt = B := by
    dsimp only [Bt]
    rw [← Matrix.mul_assoc, ← hBX, Matrix.mul_assoc, Matrix.mul_nonsing_inv X hX,
      Matrix.mul_one]
  have hl : Bt * (X * C⁻¹ * X) = B * C⁻¹ * X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBtX]
  have hr : (X * C⁻¹ * X) * Bt = X * C⁻¹ * B := by
    rw [Matrix.mul_assoc, hXBt]
  calc
    Bt * Ct⁻¹ - Ct⁻¹ * Bt = B * C⁻¹ * X - X * C⁻¹ * B := by
      rw [hCt, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hl, hr, hBtX,
        hXBt]
      abel
    _ = B * C⁻¹ - C⁻¹ * B := by
      dsimp only [X]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      abel

private theorem mobiusDenominator_ne_zero (a b : ι → ℂ) (t : ℂ)
    (ha : ∀ i, 1 - t * a i ≠ 0) (hb : ∀ j, 1 + t * b j ≠ 0) :
    mobiusDenominator a b t ≠ 0 :=
  mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ha i)
    (Finset.prod_ne_zero_iff.mpr fun j _ => hb j)

/-- The determinant-scaled inverse commutator is exactly the same matrix
after a regular Möbius change when the support direction is rescaled. -/
theorem stationary_matrix_mobius (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (hC : determinantValue a b U ≠ 0) (t ξ : ℂ)
    (ha : ∀ i, 1 - t * a i ≠ 0) (hb : ∀ j, 1 + t * b j ≠ 0) :
    let A := diagonal a
    let B := U * diagonal b * Uᴴ
    let C := A + B
    let c := mobiusSpectrum t a
    let d := mobiusSpectrum (-t) b
    let Bt := U * diagonal d * Uᴴ
    let Ct := diagonal c + Bt
    let ξt := ξ * mobiusDenominator a b t
    (ξt * Ct.det) • (Bt * Ct⁻¹ - Ct⁻¹ * Bt) =
      (ξ * C.det) • (B * C⁻¹ - C⁻¹ * B) := by
  intro A B C c d Bt Ct ξt
  let Y := 1 - t • A
  let X := 1 + t • B
  have hY : Y = diagonal (fun i => 1 - t * a i) := by
    ext i j : 1
    by_cases h : i = j <;>
      simp [Y, A, Matrix.one_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul, h]
  have hD : diagonal (fun j => 1 + t * b j) = 1 + t • diagonal b := by
    ext i j : 1
    by_cases h : i = j <;>
      simp [Matrix.one_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul, h]
  have hX : X = U * diagonal (fun j => 1 + t * b j) * Uᴴ := by
    dsimp only [X, B]
    rw [hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU.1]
  have hYu : IsUnit Y.det := by
    rw [hY, Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ha i)
  have hXu : IsUnit X.det := by
    rw [hX, det_unitary_conjugation U _ hU, Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => hb j)
  have hYAt : Y * diagonal c = A := by
    rw [hY, Matrix.diagonal_mul_diagonal]
    apply congrArg (fun f : ι → ℂ => diagonal f)
    funext i
    dsimp only [c, mobiusSpectrum]
    field_simp [ha i]
  have hBtX : Bt * X = B := by
    rw [hX]
    have hd : diagonal d * diagonal (fun j => 1 + t * b j) = diagonal b := by
      rw [Matrix.diagonal_mul_diagonal]
      apply congrArg (fun f : ι → ℂ => diagonal f)
      funext j
      simp only [d, mobiusSpectrum, neg_mul, sub_neg_eq_add]
      exact div_mul_cancel₀ _ (hb j)
    calc
      Bt * (U * diagonal (fun j => 1 + t * b j) * Uᴴ) =
          U * (diagonal d * (Uᴴ * U) * diagonal (fun j => 1 + t * b j)) * Uᴴ := by
        simp only [Bt, Matrix.mul_assoc]
      _ = B := by rw [hU.2, Matrix.mul_one, hd]
  have hBt : Bt = B * X⁻¹ := by
    rw [← hBtX, Matrix.mul_assoc, Matrix.mul_nonsing_inv X hXu, Matrix.mul_one]
  have hfact : Y * Ct * X = C := by
    change Y * (diagonal c + Bt) * X = C
    rw [Matrix.mul_add Y (diagonal c) Bt, Matrix.add_mul, hYAt, Matrix.mul_assoc Y Bt X, hBtX]
    dsimp only [Y, X, C]
    simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
    abel
  have hCt : Ct = Y⁻¹ * C * X⁻¹ := by
    rw [← hfact, ← Matrix.mul_assoc Y⁻¹ (Y * Ct) X, ← Matrix.mul_assoc Y⁻¹ Y Ct,
      Matrix.nonsing_inv_mul Y hYu, Matrix.one_mul, Matrix.mul_assoc Ct X X⁻¹,
      Matrix.mul_nonsing_inv X hXu, Matrix.mul_one]
  have hcomm : Bt * Ct⁻¹ - Ct⁻¹ * Bt = B * C⁻¹ - C⁻¹ * B := by
    rw [hBt, hCt]
    exact inverse_commutator_mobius A B t (isUnit_iff_ne_zero.mpr hC) hYu hXu
  have hξ : ξt * Ct.det = ξ * C.det := by
    change (ξ * mobiusDenominator a b t) *
      determinantValue (mobiusSpectrum t a) (mobiusSpectrum (-t) b) U =
        ξ * determinantValue a b U
    rw [determinantValue_mobius a b U hU t ha hb]
    field_simp [mobiusDenominator_ne_zero a b t ha hb] <;> ring
  rw [hξ, hcomm]

/-- A regular change preserves the determinant's complex difference from
each matching product after rescaling the direction. -/
theorem matching_support_difference_mobius (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (t ξ : ℂ)
    (ha : ∀ i, 1 - t * a i ≠ 0) (hb : ∀ j, 1 + t * b j ≠ 0) (σ : Equiv.Perm ι) :
    let c := mobiusSpectrum t a
    let d := mobiusSpectrum (-t) b
    (ξ * mobiusDenominator a b t) * (determinantValue c d U - matchingProduct c d σ) =
      ξ * (determinantValue a b U - matchingProduct a b σ) := by
  dsimp only
  rw [determinantValue_mobius a b U hU t ha hb,
    matchingProduct_mobius a b t σ ha hb]
  field_simp [mobiusDenominator_ne_zero a b t ha hb] <;> ring

/-- Under a regular Möbius change the linear pairing is preserved, while the
squared norm in the quadratic penalty gains the squared denominator factor. -/
theorem quadratic_support_mobius_iff (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (t ξ : ℂ)
    (ha : ∀ i, 1 - t * a i ≠ 0) (hb : ∀ j, 1 + t * b j ≠ 0) :
    let c := mobiusSpectrum t a
    let d := mobiusSpectrum (-t) b
    let Δ := mobiusDenominator a b t
    (∀ V : Matrix ι ι ℂ, IsUnitary V →
      let δ := determinantValue a b V - determinantValue a b U
      (ξ * δ).re ≤ -Complex.normSq δ / 2) ↔
    (∀ V : Matrix ι ι ℂ, IsUnitary V →
      let δ := determinantValue c d V - determinantValue c d U
      ((ξ * Δ) * δ).re ≤ -(Complex.normSq Δ * Complex.normSq δ) / 2) := by
  intro c d Δ
  have hΔ : Δ ≠ 0 := mobiusDenominator_ne_zero a b t ha hb
  have he (V : Matrix ι ι ℂ) (hV : IsUnitary V) :
      determinantValue a b V - determinantValue a b U =
        Δ * (determinantValue c d V - determinantValue c d U) := by
    dsimp only [c, d]
    rw [determinantValue_mobius a b V hV t ha hb,
      determinantValue_mobius a b U hU t ha hb, ← sub_div, mul_comm Δ, div_mul_cancel₀ _ hΔ]
  constructor
  · intro h V hV
    have hh := h V hV
    dsimp only at hh ⊢
    rw [he V hV, ← mul_assoc, Complex.normSq_mul] at hh
    exact hh
  · intro h V hV
    dsimp only
    rw [he V hV, ← mul_assoc, Complex.normSq_mul]
    exact h V hV

end

end MOC

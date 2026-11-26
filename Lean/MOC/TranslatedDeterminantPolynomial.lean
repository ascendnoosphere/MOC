import MOC.FourInversePencilRankLift
import MOC.Weights
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! The translated determinant polynomial and its low-rank factors. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The homogeneous polynomial for the determinant distance to `w`. -/
noncomputable def translatedDeterminantPolynomial (a b : ι → ℂ) (w : ℂ)
    (T : Matrix ι ι ℂ) : ℂ :=
  (diagonal a * T + T * diagonal b).det - w * T.det

theorem spectral_sum_kernel_eq_entrywise (a b : ι → ℂ) (T : Matrix ι ι ℂ) :
    diagonal a * T + T * diagonal b = Matrix.of (fun i j => (a i + b j) * T i j) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  ring

theorem translatedDeterminantPolynomial_unitary (a b : ι → ℂ) (w : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    translatedDeterminantPolynomial a b w U = U.det * (determinantValue a b U - w) := by
  rw [translatedDeterminantPolynomial, spectral_sum_kernel_eq_entrywise,
    determinantValue_eq_weightedEntryDet_div a b U hU, mul_sub,
    mul_div_cancel₀ _ (det_ne_zero_of_unitary hU), mul_comm U.det w]

theorem translatedDeterminantPolynomial_normSq_unitary (a b : ι → ℂ) (w : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Complex.normSq (translatedDeterminantPolynomial a b w U) =
      Complex.normSq (determinantValue a b U - w) := by
  have hd := congrArg Matrix.det hU.1
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at hd
  have hu : Complex.normSq U.det = 1 := by
    rw [← Complex.ofReal_inj, Complex.ofReal_one, ← Complex.mul_conj]
    exact hd
  rw [translatedDeterminantPolynomial_unitary a b w U hU, map_mul, hu, one_mul]

theorem translatedDeterminantPolynomial_smul (a b : ι → ℂ) (w c : ℂ)
    (T : Matrix ι ι ℂ) :
    translatedDeterminantPolynomial a b w (c • T) =
      c ^ Fintype.card ι * translatedDeterminantPolynomial a b w T := by
  simp only [translatedDeterminantPolynomial, Matrix.mul_smul, Matrix.smul_mul,
    ← smul_add, Matrix.det_smul]
  ring

private theorem det_eq_zero_of_rank_lt_card (A : Matrix ι ι ℂ) (h : A.rank < Fintype.card ι) :
    A.det = 0 := by
  by_contra hd
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hd)
  rw [Matrix.rank_of_isUnit A hu] at h
  exact (lt_irrefl _) h

/-- The polynomial vanishes when twice the rank is less than the order. -/
theorem translatedDeterminantPolynomial_eq_zero_of_rank (a b : ι → ℂ) (w : ℂ)
    (T : Matrix ι ι ℂ) (h : 2 * T.rank < Fintype.card ι) :
    translatedDeterminantPolynomial a b w T = 0 := by
  have hadd := rank_add_range_inter_le (diagonal a * T) (T * diagonal b)
  have hker : (diagonal a * T + T * diagonal b).rank < Fintype.card ι := by
    have ha : (diagonal a * T).rank ≤ T.rank := Matrix.rank_mul_le_right _ _
    have hb : (T * diagonal b).rank ≤ T.rank := Matrix.rank_mul_le_left _ _
    omega
  have hT : T.rank < Fintype.card ι := by omega
  rw [translatedDeterminantPolynomial, det_eq_zero_of_rank_lt_card _ hker,
    det_eq_zero_of_rank_lt_card _ hT, mul_zero, sub_zero]

/-- A rank factorization of `T` gives two rectangular factors for the
spectral sum kernel, with twice the inner dimension. -/
theorem spectral_sum_kernel_factorization {κ : Type*} [Fintype κ]
    (a b : ι → ℂ) (L : Matrix ι κ ℂ) (R : Matrix κ ι ℂ) :
    diagonal a * (L * R) + (L * R) * diagonal b =
      Matrix.fromCols (diagonal a * L) L * Matrix.fromRows R (R * diagonal b) := by
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_assoc, ← Matrix.mul_assoc L R]

/-- When the order is twice the inner dimension, the two factors are square. -/
theorem det_spectral_sum_kernel_factorization {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a b : κ ⊕ κ → ℂ) (L : Matrix (κ ⊕ κ) κ ℂ) (R : Matrix κ (κ ⊕ κ) ℂ) :
    (diagonal a * (L * R) + (L * R) * diagonal b).det =
      (Matrix.fromCols (diagonal a * L) L).det * (Matrix.fromRows R (R * diagonal b)).det := by
  rw [spectral_sum_kernel_factorization, Matrix.det_mul]

end MOC

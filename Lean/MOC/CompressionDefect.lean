import MOC.NormalCompressionLine

open BigOperators Matrix

namespace MOC
noncomputable section

/-- Gram's two-dimensional determinant as a sum of the squared oriented areas. -/
theorem weighted_areaSq_covariance {I : Type*} [Fintype I] (p x y : I → ℝ) :
    (∑ i, ∑ j, p i * p j * (x i * y j - y i * x j)^2) =
      2 * ((∑ i, p i * (x i)^2) * (∑ i, p i * (y i)^2) -
        (∑ i, p i * x i * y i)^2) := by
  have h (i j : I) : p i * p j * (x i * y j - y i * x j)^2 =
      (p i * (x i)^2) * (p j * (y j)^2) +
      (p i * (y i)^2) * (p j * (x j)^2) -
      2 * ((p i * x i * y i) * (p j * x j * y j)) := by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The exact squared entry norm of the spectral commutator lift.
Applied to the zero-padded compression, the weights are the deleted-row
squared overlaps and the coordinates are centered by the deleted diagonal. -/
theorem principalCompression_spectralLift_normSq_covariance {I : Type*} [Fintype I]
    (r δ : I → ℂ) :
    let p (i : I) := Complex.normSq (r i)
    let x (i : I) := (δ i).re
    let y (i : I) := (δ i).im
    (∑ i, ∑ j, Complex.normSq (star (r i) * r j *
       (star (δ i) * δ j - δ i * star (δ j)))) =
       8 * ((∑ i, p i * (x i)^2) * (∑ i, p i * (y i)^2) -
          (∑ i, p i * x i * y i)^2) := by
  intro p x y
  have h (i j : I) : Complex.normSq (star (r i) * r j *
       (star (δ i) * δ j - δ i * star (δ j))) =
       4 * (p i * p j * (x i * y j - y i * x j)^2) := by
    simp only [map_mul, Complex.star_def, Complex.normSq_conj, p, x, y]
    rw [show Complex.normSq ((starRingEnd ℂ) (δ i) * δ j - δ i * (starRingEnd ℂ) (δ j)) =
      4 * ((δ i).re * (δ j).im - (δ i).im * (δ j).re)^2 by
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im]
      ring]
    ring
  simp only [h, ← Finset.mul_sum]
  rw [weighted_areaSq_covariance]
  ring


/-- Squared Frobenius norm without changing the default matrix norm instance. -/
def matrixEntryNormSq {I : Type*} [Fintype I] (M : Matrix I I ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

private theorem matrixEntryNormSq_eq_trace {I : Type*} [Fintype I] (M : Matrix I I ℂ) :
    matrixEntryNormSq M = (Mᴴ * M).trace.re := by
  unfold matrixEntryNormSq Matrix.trace
  rw [Finset.sum_comm]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem matrixEntryNormSq_unitary_conjugation {I : Type*} [Fintype I] [DecidableEq I]
    (M U : Matrix I I ℂ) (hU : IsUnitary U) :
    matrixEntryNormSq (U * M * Uᴴ) = matrixEntryNormSq M := by
  simp only [matrixEntryNormSq_eq_trace, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  rw [show U * (Mᴴ * Uᴴ) * (U * M * Uᴴ) = U * ((Mᴴ * M) * Uᴴ) by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul]]
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc (Mᴴ * M) Uᴴ, hU.2, Matrix.mul_one]

/-- The squared Frobenius norm of a principal compression's self-commutator
is eight times the determinant of the deleted-row weighted covariance. -/
theorem principalCompression_selfCommutator_normSq_covariance {n : ℕ}
    (β : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p : Fin (n + 1)) :
    let M := U * diagonal β * Uᴴ
    let C := M.submatrix p.succAbove p.succAbove
    let w (i : Fin (n + 1)) := Complex.normSq (U p i)
    let x (i : Fin (n + 1)) := (β i - M p p).re
    let y (i : Fin (n + 1)) := (β i - M p p).im
    matrixEntryNormSq (C * Cᴴ - Cᴴ * C) =
      8 * ((∑ i, w i * (x i)^2) * (∑ i, w i * (y i)^2) -
          (∑ i, w i * x i * y i)^2) := by
  intro M C w x y
  let δ (i : Fin (n + 1)) := β i - M p p
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j =>
    star (U p i) * U p j * (star (δ i) * δ j - δ i * star (δ j))
  let T := U * E * Uᴴ
  obtain ⟨hT, hzrow, hzcol⟩ := principalCompression_selfCommutator_spectral_lift β U hU p
  change T.submatrix p.succAbove p.succAbove = _ at hT
  change ∀ i, T p i = 0 at hzrow
  change ∀ i, T i p = 0 at hzcol
  have hpad : matrixEntryNormSq (T.submatrix p.succAbove p.succAbove) = matrixEntryNormSq T := by
    unfold matrixEntryNormSq
    rw [Fin.sum_univ_succAbove _ p]
    simp only [hzrow, map_zero, Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_succAbove _ p]
    simp [hzcol, Matrix.submatrix_apply]
  rw [← hT, hpad, matrixEntryNormSq_unitary_conjugation E U hU]
  exact principalCompression_spectralLift_normSq_covariance (U p) δ


/-- If the supported spectral labels lie in an imaginary-coordinate strip
of half-width ε (about any center), the squared defect is at most eight
times ε² times their centered real variance. -/
theorem principalCompression_selfCommutator_normSq_le_strip {n : ℕ}
    (β : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p : Fin (n + 1)) (h ε : ℝ)
    (hstrip : ∀ i, U p i ≠ 0 → |(β i).im - h| ≤ ε) :
    let M := U * diagonal β * Uᴴ
    let C := M.submatrix p.succAbove p.succAbove
    matrixEntryNormSq (C * Cᴴ - Cᴴ * C) ≤
      8 * (∑ i, Complex.normSq (U p i) * ((β i - M p p).re)^2) * ε^2 := by
  intro M C
  let w (i : Fin (n + 1)) := Complex.normSq (U p i)
  let x (i : Fin (n + 1)) := (β i - M p p).re
  let y (i : Fin (n + 1)) := (β i - M p p).im
  change matrixEntryNormSq (C * Cᴴ - Cᴴ * C) ≤ 8 * (∑ i, w i * (x i)^2) * ε^2
  have hw : ∑ i, w i = 1 := by
    exact sum_col_of_mem_doublyStochastic (normSq_transpose_doublyStochastic U hU) p
  have hval : M p p = ∑ i, (w i : ℂ) * β i := by
    dsimp only [M]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, w,
      Complex.normSq_eq_conj_mul_self, Complex.star_def]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hc : (M p p).im = ∑ i, w i * (β i).im := by
    rw [hval, Complex.im_sum]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  let c := (M p p).im
  have hm : ∑ i, w i * (β i).im = c := hc.symm
  have hv (a : ℝ) :
      (∑ i, w i * ((β i).im - a)^2) =
        (∑ i, w i * (β i).im^2) - 2 * a * c + a^2 := by
    have he (i : Fin (n + 1)) : w i * ((β i).im - a)^2 =
        w i * (β i).im^2 - (2*a) * (w i * (β i).im) + w i * a^2 := by ring
    simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hm, hw, one_mul]
  have hband : (∑ i, w i * ((β i).im - h)^2) ≤ ε^2 := by
    calc
      _ ≤ ∑ i, w i * ε^2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : U p i = 0
        · simp [w,hi]
        · apply mul_le_mul_of_nonneg_left _ (Complex.normSq_nonneg _)
          have hb := abs_le.mp (hstrip i hi)
          nlinarith [sq_nonneg (ε - ((β i).im - h)), sq_nonneg (ε + ((β i).im - h)),
            mul_nonneg (sub_nonneg.mpr hb.2) (show 0 ≤ ε + ((β i).im - h) by linarith [hb.1])]
      _ = ε^2 := by rw [← Finset.sum_mul, hw, one_mul]
  have hy : (∑ i, w i * (y i)^2) ≤ ε^2 := by
    change (∑ i, w i * ((β i).im - c)^2) ≤ _
    rw [hv h] at hband
    rw [hv c]
    nlinarith [sq_nonneg (h - c)]
  have hnon : 0 ≤ (∑ i, w i * (x i)^2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)
  rw [principalCompression_selfCommutator_normSq_covariance β U hU p]
  change 8 * ((∑ i, w i * (x i)^2) * (∑ i, w i * (y i)^2) -
      (∑ i, w i * x i * y i)^2) ≤ _
  calc
    _ ≤ 8 * (∑ i, w i * (x i)^2) * (∑ i, w i * (y i)^2) := by
      nlinarith [sq_nonneg (∑ i, w i * x i * y i)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hy (mul_nonneg (by positivity) hnon)

end
end MOC

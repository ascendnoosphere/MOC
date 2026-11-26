import MOC.Transfer

/-! Cofactors of the entrywise spectral sum give the two global interference
sums. Laplace expansion reconstructs the determinant separately on every row. -/

open BigOperators Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient of the positive frequency in the feedback numerator,
with the minus sign placed outside the coefficient. -/
def feedbackPositiveCofactor (a b : ι → ℂ) (U : Matrix ι ι ℂ) (i j : ι) : ℂ :=
  (a i + b j) * (Matrix.of (fun k l => (a k + b l) * U k l)).adjugate j i / U.det

/-- Conjugating both spectral lists exchanges the two feedback frequencies. -/
def feedbackNegativeCofactor (a b : ι → ℂ) (U : Matrix ι ι ℂ) (i j : ι) : ℂ :=
  conj (feedbackPositiveCofactor (fun k => conj (a k)) (fun l => conj (b l)) U i j)

theorem feedbackPositiveCofactor_row (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (i : ι) :
    ∑ j, U i j * feedbackPositiveCofactor a b U i j = determinantValue a b U := by
  let H := Matrix.of fun k l => (a k + b l) * U k l
  have h : ∑ j, H i j * H.adjugate j i = H.det := by
    simpa only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      using congrArg (fun M : Matrix ι ι ℂ => M i i) (Matrix.mul_adjugate H)
  rw [determinantValue_eq_weightedEntryDet_div a b U hU]
  change _ = H.det / U.det
  rw [← h, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [feedbackPositiveCofactor, H]
  ring

private theorem determinantValue_conjugate_spectra (a b : ι → ℂ) (U : Matrix ι ι ℂ) :
    conj (determinantValue (fun k => conj (a k)) (fun l => conj (b l)) U) =
      determinantValue a b U := by
  have he : diagonal (fun k => conj (a k)) + U * diagonal (fun l => conj (b l)) * Uᴴ =
      (diagonal a + U * diagonal b * Uᴴ)ᴴ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.diagonal_conjTranspose]
    rfl
  simp only [determinantValue, he, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_conj]

theorem feedbackNegativeCofactor_row (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (i : ι) :
    ∑ j, conj (U i j) * feedbackNegativeCofactor a b U i j = determinantValue a b U := by
  have he := congrArg conj (feedbackPositiveCofactor_row (fun k => conj (a k))
    (fun l => conj (b l)) U hU i)
  simpa only [map_sum, map_mul, feedbackNegativeCofactor, determinantValue_conjugate_spectra] using he

/-- The two global cofactor sums reconstruct the original determinant. -/
theorem feedback_global_cofactor_reconstruction (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) :
    (∑ i, ∑ j, U i j * feedbackPositiveCofactor a b U i j) =
        (Fintype.card ι : ℂ) * determinantValue a b U ∧
    (∑ i, ∑ j, conj (U i j) * feedbackNegativeCofactor a b U i j) =
        (Fintype.card ι : ℂ) * determinantValue a b U := by
  constructor <;> simp [feedbackPositiveCofactor_row a b U hU, feedbackNegativeCofactor_row a b U hU]

/-- The positive frequency of the real support gap. -/
def feedbackSupportCoefficient (a b : ι → ℂ) (U : Matrix ι ι ℂ) (M : ℝ) (i j : ι) : ℂ :=
  (feedbackPositiveCofactor a b U i j + conj (feedbackNegativeCofactor a b U i j)) / 2 -
    (M : ℂ) * conj (U i j)

theorem feedback_support_row (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (M : ℝ) (i : ι) :
    (∑ j, U i j * feedbackSupportCoefficient a b U M i j).re = (determinantValue a b U).re - M := by
  have hn := congrArg conj (feedbackNegativeCofactor_row a b U hU i)
  simp only [map_sum, map_mul, Complex.conj_conj] at hn
  have hu : (∑ j, U i j * conj (U i j)) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Matrix.one_apply_eq]
      using congrArg (fun A : Matrix ι ι ℂ => A i i) hU.1
  have hterm (j : ι) : U i j * feedbackSupportCoefficient a b U M i j =
      (U i j * feedbackPositiveCofactor a b U i j +
       U i j * conj (feedbackNegativeCofactor a b U i j)) / 2 -
      (M : ℂ) * (U i j * conj (U i j)) := by unfold feedbackSupportCoefficient; ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hu,
    mul_one, hn, feedbackPositiveCofactor_row a b U hU]
  rw [Complex.sub_re, Complex.ofReal_re]
  simp [Complex.div_re, Complex.add_re]

theorem feedback_global_sign_iff [Nonempty ι] (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (M : ℝ) :
    (∑ i, ∑ j, U i j * feedbackSupportCoefficient a b U M i j).re ≤ 0 ↔
      (determinantValue a b U).re ≤ M := by
  rw [Complex.re_sum]
  simp_rw [feedback_support_row a b U hU M]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · intro h
    by_contra! hlt
    exact (not_lt_of_ge h) (mul_pos hc (sub_pos.mpr hlt))
  · exact fun h => mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr h)

end

end MOC

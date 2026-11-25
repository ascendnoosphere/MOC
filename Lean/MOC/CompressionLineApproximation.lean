import MOC.CompressionCovariance

/-! Fitting a supported spectrum by a line gives a normal surrogate with
entrywise spectral error controlled by the compression commutator. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private theorem weighted_line_regression {ι : Type*} [Fintype ι]
    (w x y : ι → ℝ) (hx : (∑ i, w i * x i ^ 2) ≠ 0) :
    let A := ∑ i, w i * x i ^ 2
    let B := ∑ i, w i * y i ^ 2
    let D := ∑ i, w i * x i * y i
    (∑ i, w i * (y i - (D / A) * x i) ^ 2) = (A * B - D ^ 2) / A := by
  intro A B D
  let m := D / A
  change (∑ i, w i * (y i - m * x i) ^ 2) = (A * B - D ^ 2) / A
  have hterm (i : ι) : w i * (y i - m * x i) ^ 2 =
      w i * y i ^ 2 - 2 * m * (w i * x i * y i) + m ^ 2 * (w i * x i ^ 2) := by ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change B - 2 * m * D + m ^ 2 * A = _
  dsimp only [m]
  change A ≠ 0 at hx
  field_simp [hx]
  <;> ring

/-- A nonnormal principal compression admits a normal line surrogate. For
each affected label, the squared displacement times the row weight and
four times the total spectral variance is bounded by the squared
Frobenius norm of the original compression self-commutator. -/
theorem exists_normal_line_surrogate_of_nonnormalCompression {n : ℕ}
    (β : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p : Fin (n + 1))
    (hn : ¬ IsStarNormal ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove)) :
    let M := U * diagonal β * Uᴴ
    let C := M.submatrix p.succAbove p.succAbove
    let μ := M p p
    let w (i : Fin (n + 1)) := Complex.normSq (U p i)
    ∃ γ : Fin (n + 1) → ℂ, (∀ j, U p j = 0 → γ j = β j) ∧
      IsStarNormal ((U * diagonal γ * Uᴴ).submatrix p.succAbove p.succAbove) ∧
      ∀ j, 4 * (∑ k, w k * Complex.normSq (β k - μ)) * w j * Complex.normSq (β j - γ j) ≤
        ∑ i, ∑ k, Complex.normSq ((C * Cᴴ - Cᴴ * C) i k) := by
  classical
  intro M C μ w
  let ι := Fin (n + 1)
  let x (i : ι) := (β i - μ).re
  let y (i : ι) := (β i - μ).im
  let V := ∑ i, w i * Complex.normSq (β i - μ)
  let E := ∑ i, ∑ j, Complex.normSq ((C * Cᴴ - Cᴴ * C) i j)
  let variance (a : ι → ℝ) := ∑ i, w i * a i ^ 2
  let moment (a b : ι → ℝ) := ∑ i, w i * a i * b i
  let covariance (a b : ι → ℝ) := variance a * variance b - moment a b ^ 2
  have hw (i : ι) : 0 ≤ w i := Complex.normSq_nonneg _
  have hv : V = variance x + variance y := by
    dsimp only [V, variance]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.normSq_apply, x, y]
    ring
  have he : E = 8 * covariance x y := principalCompression_selfCommutator_covariance β U hU p
  have hpos : 0 < covariance x y := principalCompression_covariance_pos β U hU p hn
  have hbuild (a b : ι → ℝ) (u v : ℂ) (hv₁ : Complex.normSq v = 1)
      (hs : ∀ i, β i - μ = u * (a i : ℂ) + v * (b i : ℂ))
      (hdom : variance b ≤ variance a) (htrace : V = variance a + variance b)
      (hc : covariance a b = covariance x y) :
      ∃ γ : ι → ℂ, (∀ j, U p j = 0 → γ j = β j) ∧
        IsStarNormal ((U * diagonal γ * Uᴴ).submatrix p.succAbove p.succAbove) ∧
        ∀ j, 4 * V * w j * Complex.normSq (β j - γ j) ≤ E := by
    have hA : 0 < variance a := by
      have hD : 0 < covariance a b := hc.symm ▸ hpos
      have hB : 0 ≤ variance b := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
      have hp : 0 < variance a * variance b := by
        change 0 < variance a * variance b - moment a b ^ 2 at hD
        linarith only [hD, sq_nonneg (moment a b)]
      exact pos_of_mul_pos_left hp hB
    let m := moment a b / variance a
    let d := u + v * (m : ℂ)
    let γ (j : ι) := if U p j = 0 then β j else μ + d * (a j : ℂ)
    refine ⟨γ, fun j hj => by simp [γ, hj], ?_, ?_⟩
    · apply normalCompression_of_spectral_line_on_support γ U hU p μ d a
      intro j hj
      simp only [γ, if_neg hj]
    · intro i
      let S := ∑ j, w j * (b j - m * a j) ^ 2
      have hsum : S = covariance a b / variance a := weighted_line_regression w a b hA.ne'
      have hentry : w i * Complex.normSq (β i - γ i) ≤ S := by
        by_cases hi : U p i = 0
        · simp only [γ, if_pos hi, sub_self, Complex.normSq_zero, mul_zero]
          exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
        · have hdifference : β i - γ i = v * ((b i - m * a i : ℝ) : ℂ) := by
            simp only [γ, if_neg hi, d, Complex.ofReal_sub, Complex.ofReal_mul]
            linear_combination hs i
          rw [hdifference, Complex.normSq_mul, hv₁, one_mul, Complex.normSq_ofReal, ← pow_two]
          dsimp only [S]
          exact Finset.single_le_sum
            (fun j _ => mul_nonneg (hw j) (sq_nonneg (b j - m * a j))) (Finset.mem_univ i)
      calc
        4 * V * w i * Complex.normSq (β i - γ i) =
          (4 * V) * (w i * Complex.normSq (β i - γ i)) := by ring
        _ ≤ (8 * variance a) * (w i * Complex.normSq (β i - γ i)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (hw i) (Complex.normSq_nonneg _))
          rw [htrace]
          linarith only [hdom]
        _ ≤ (8 * variance a) * S :=
          mul_le_mul_of_nonneg_left hentry (mul_nonneg (by norm_num) hA.le)
        _ = 8 * covariance a b := by
          rw [hsum]
          field_simp [hA.ne']
          <;> ring
        _ = E := by rw [hc, he]
  change ∃ γ : ι → ℂ, (∀ j, U p j = 0 → γ j = β j) ∧
    IsStarNormal ((U * diagonal γ * Uᴴ).submatrix p.succAbove p.succAbove) ∧
    ∀ j, 4 * V * w j * Complex.normSq (β j - γ j) ≤ E
  have hxy (i : ι) : β i - μ = (x i : ℂ) + (y i : ℂ) * Complex.I :=
    (Complex.re_add_im (β i - μ)).symm
  by_cases hdom : variance y ≤ variance x
  · apply hbuild x y 1 Complex.I Complex.normSq_I _ hdom hv rfl
    intro i
    rw [hxy i, one_mul, mul_comm Complex.I]
  · have hm : moment y x = moment x y := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hc : covariance y x = covariance x y := by
      dsimp only [covariance]
      rw [hm, mul_comm (variance y)]
    apply hbuild y x Complex.I 1 Complex.normSq_one _ (le_of_not_ge hdom) (hv.trans (add_comm _ _)) hc
    intro i
    rw [hxy i, one_mul, mul_comm Complex.I, add_comm]

end

end MOC

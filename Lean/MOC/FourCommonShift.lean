import MOC.Geometry
import MOC.Support
import Mathlib.Tactic.Linarith

/-! The shift differences in order four are quadratic. A strict margin for
the leading trace-of-product coefficient confines any violation to a bounded disk. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private def tripleSum (x : Fin 4 → ℂ) : ℂ :=
  x 0 * x 1 * x 2 + x 0 * x 1 * x 3 + x 0 * x 2 * x 3 + x 1 * x 2 * x 3

private theorem signed_covariance (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) :
    (∑ σ, signedWeight U σ * ∑ j, a (σ j) * b j) =
      (diagonal a * (U * diagonal b * Uᴴ)).trace := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hj (j : Fin 4) :
      ∑ σ, signedWeight U σ * (a (σ j) * b j) =
        ∑ i, (Complex.normSq (U i j) : ℂ) * (a i * b j) := by
    rw [sum_weighted_evaluation (signedWeight U) j (fun i => a i * b j)]
    simp only [marginal_signedWeight U hU]
  simp only [hj]
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Complex.normSq_eq_conj_mul_self, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [starRingEnd_apply]
  ring

/-- The coefficient of `z²` in a shifted matching product minus the shifted
determinant is the difference between the two trace-of-product values. -/
theorem four_common_shift_quadratic (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) :
    ∃ (linear constant : Equiv.Perm (Fin 4) → ℂ), ∀ σ z,
      matchingProduct (fun i => a i - z) b σ - determinantValue (fun i => a i - z) b U =
        ((diagonal a * (U * diagonal b * Uᴴ)).trace - ∑ j, a (σ j) * b j) * z ^ 2 +
          linear σ * z + constant σ := by
  let x (σ : Equiv.Perm (Fin 4)) (j : Fin 4) := a (σ j) + b j
  let cost (σ : Equiv.Perm (Fin 4)) := ∑ j, a (σ j) * b j
  let T : ℂ := (∑ j, a j) + ∑ j, b j
  let K : ℂ := (T ^ 2 - ((∑ j, a j ^ 2) + ∑ j, b j ^ 2)) / 2
  let base (z : ℂ) := z ^ 4 - T * z ^ 3 + K * z ^ 2
  let w := signedWeight U
  let tr := (diagonal a * (U * diagonal b * Uᴴ)).trace
  let d := determinantValue a b U
  have hx (σ : Equiv.Perm (Fin 4)) : ∑ j, x σ j = T := by
    simp only [x, T, Finset.sum_add_distrib, Equiv.sum_comp σ a]
  have hx₂ (σ : Equiv.Perm (Fin 4)) :
      ∑ j, x σ j ^ 2 = ((∑ j, a j ^ 2) + ∑ j, b j ^ 2) + 2 * cost σ := by
    calc
      _ = ∑ j, (a (σ j) ^ 2 + b j ^ 2 + 2 * (a (σ j) * b j)) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [x]
        ring
      _ = _ := by
        simp only [cost, Finset.sum_add_distrib, ← Finset.mul_sum,
          Equiv.sum_comp σ (fun i => a i ^ 2)]
  have hm (σ : Equiv.Perm (Fin 4)) (z : ℂ) :
      matchingProduct (fun i => a i - z) b σ =
        base z - cost σ * z ^ 2 - tripleSum (x σ) * z + matchingProduct a b σ := by
    have hprod : (∏ j, (x σ j - z)) =
        z ^ 4 - (∑ j, x σ j) * z ^ 3 +
          (((∑ j, x σ j) ^ 2 - ∑ j, x σ j ^ 2) / 2) * z ^ 2 -
          tripleSum (x σ) * z + ∏ j, x σ j := by
      simp only [Fin.prod_univ_four, Fin.sum_univ_four, tripleSum]
      ring
    have hz (j : Fin 4) : a (σ j) - z + b j = x σ j - z := by
      dsimp only [x]
      ring
    unfold matchingProduct
    simp_rw [hz]
    rw [hprod, hx, hx₂]
    dsimp only [base, K, x]
    ring
  have hw : ∑ σ, w σ = 1 := sum_signedWeight U (det_ne_zero_of_unitary hU)
  have hc : ∑ σ, w σ * cost σ = tr := signed_covariance a b U hU
  have hd : ∑ σ, w σ * matchingProduct a b σ = d := signed_determinant a b U hU
  have hshift (z : ℂ) : determinantValue (fun i => a i - z) b U =
      base z - tr * z ^ 2 - (∑ σ, w σ * tripleSum (x σ)) * z + d := by
    rw [← signed_determinant (fun i => a i - z) b U hU]
    change (∑ σ, w σ * matchingProduct (fun i => a i - z) b σ) = _
    simp only [hm, mul_add, mul_sub, ← mul_assoc, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hw, hc, hd, one_mul]
  refine ⟨fun σ => (∑ τ, w τ * tripleSum (x τ)) - tripleSum (x σ),
    fun σ => matchingProduct a b σ - d, fun σ z => ?_⟩
  rw [hm, hshift]
  change _ = (tr - cost σ) * z ^ 2 + _ + _
  ring

/-- If the trace-of-product point has a positive support margin in every unit
direction, the order-four inclusion holds outside a disk in the shift plane. -/
theorem holds_four_common_shift_outside (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ η : ℂ, ‖η‖ = 1 → ∃ σ : Equiv.Perm (Fin 4),
      δ ≤ (η * ((diagonal a * (U * diagonal b * Uᴴ)).trace - ∑ j, a (σ j) * b j)).re) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → Holds (fun i => a i - z) b U := by
  obtain ⟨linear, constant, hpoly⟩ := four_common_shift_quadratic a b U hU
  let L (σ : Equiv.Perm (Fin 4)) :=
    (diagonal a * (U * diagonal b * Uᴴ)).trace - ∑ j, a (σ j) * b j
  let M : ℝ := ∑ σ, (‖linear σ‖ + ‖constant σ‖)
  have hM : 0 ≤ M := Finset.sum_nonneg (fun σ _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨1 + M / δ, fun z hz => (holds_iff_directional _ _ _).mpr ?_⟩
  have hz₁ : 1 ≤ ‖z‖ := le_trans (le_add_of_nonneg_right (div_nonneg hM hδ.le)) hz
  have hz₀ : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hz₁
    norm_num at hz₁
  have hM_z : M ≤ δ * ‖z‖ := by
    have h := (div_le_iff₀ hδ).mp (show M / δ ≤ ‖z‖ by linarith only [hz])
    simpa only [mul_comm] using h
  intro k
  by_cases hk : k = 0
  · exact ⟨1, by simp [hk]⟩
  let v := k * z ^ 2
  have hv : v ≠ 0 := mul_ne_zero hk (pow_ne_zero 2 hz₀)
  have hvnorm : ‖v‖ ≠ 0 := (norm_pos_iff.mpr hv).ne'
  have hvC : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hvnorm
  obtain ⟨σ, hs⟩ := hmargin (v / (‖v‖ : ℂ)) (by
    rw [norm_div, Complex.norm_of_nonneg (norm_nonneg v), div_self hvnorm])
  change δ ≤ (v / (‖v‖ : ℂ) * L σ).re at hs
  have hmain : ‖k‖ * (δ * ‖z‖ ^ 2) ≤ (k * (L σ * z ^ 2)).re := by
    have he : (‖v‖ : ℂ) * (v / (‖v‖ : ℂ)) = v := by field_simp
    have h := mul_le_mul_of_nonneg_left hs (norm_nonneg v)
    rw [← Complex.re_ofReal_mul, ← mul_assoc, he] at h
    simpa [v, norm_mul, norm_pow, mul_comm, mul_left_comm, mul_assoc] using h
  have hsize : ‖linear σ * z + constant σ‖ ≤ δ * ‖z‖ ^ 2 := calc
    _ ≤ ‖linear σ * z‖ + ‖constant σ‖ := norm_add_le _ _
    _ ≤ (‖linear σ‖ + ‖constant σ‖) * ‖z‖ := by
      rw [norm_mul, add_mul]
      exact add_le_add_left (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hz₁ (norm_nonneg (constant σ))) _
    _ ≤ M * ‖z‖ := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun τ _ => add_nonneg (norm_nonneg (linear τ))
        (norm_nonneg (constant τ))) (Finset.mem_univ σ)) (norm_nonneg z)
    _ ≤ δ * ‖z‖ ^ 2 := by
      simpa only [pow_two, ← mul_assoc] using mul_le_mul_of_nonneg_right hM_z (norm_nonneg z)
  have herr : -(k * (linear σ * z + constant σ)).re ≤ ‖k‖ * (δ * ‖z‖ ^ 2) := calc
    _ ≤ ‖-(k * (linear σ * z + constant σ))‖ := by
      simpa only [Complex.neg_re] using Complex.re_le_norm (-(k * (linear σ * z + constant σ)))
    _ ≤ _ := by rw [norm_neg, norm_mul]; exact mul_le_mul_of_nonneg_left hsize (norm_nonneg k)
  refine ⟨σ, ?_⟩
  have hn : 0 ≤ (k * (matchingProduct (fun i => a i - z) b σ -
      determinantValue (fun i => a i - z) b U)).re := by
    rw [hpoly σ z, add_assoc, mul_add, Complex.add_re]
    change 0 ≤ (k * (L σ * z ^ 2)).re + (k * (linear σ * z + constant σ)).re
    linarith only [hmain, herr]
  rwa [mul_sub, Complex.sub_re, sub_nonneg] at hn

end

end MOC

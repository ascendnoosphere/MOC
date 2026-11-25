import MOC.Weights
import Mathlib.Tactic

/-! A rank-one assignment score need not admit a positive law
matching the first three signed moments. -/

open BigOperators Matrix

namespace MOC

/-- The rank-one assignment score with both value lists equal to `(0,1,2)`. -/
def orderThreeAssignmentScore (σ : Equiv.Perm (Fin 3)) : ℤ :=
  ∑ j, (j.val : ℤ) * ((σ j).val : ℤ)

private def thirdMomentCostInt (σ : Equiv.Perm (Fin 3)) : ℤ :=
  let r := orderThreeAssignmentScore σ
  (r - 1) * (r - 2) * (r - 4)

private theorem thirdMomentCostInt_eq (σ : Equiv.Perm (Fin 3)) :
    thirdMomentCostInt σ = if σ = 1 then 12 else 0 := by
  revert σ
  decide +kernel

/-- There is an order-three unitary for which the nonnegative cubic
assignment cost has signed expectation `-4/9`. Thus a positive law
on the same scores cannot match the signed moments through degree three. -/
theorem exists_negative_rankOne_assignment_cubic :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, IsUnitary U ∧
      (∀ σ : Equiv.Perm (Fin 3), 0 ≤
        ((orderThreeAssignmentScore σ : ℝ) - 1) *
          ((orderThreeAssignmentScore σ : ℝ) - 2) * ((orderThreeAssignmentScore σ : ℝ) - 4)) ∧
      (∑ σ : Equiv.Perm (Fin 3), realSignedWeight U σ *
        (((orderThreeAssignmentScore σ : ℝ) - 1) *
          ((orderThreeAssignmentScore σ : ℝ) - 2) * ((orderThreeAssignmentScore σ : ℝ) - 4))) =
        -4 / 9 := by
  let R : Matrix (Fin 3) (Fin 3) ℝ :=
    !![1 / 3, -2 / 3, -2 / 3; -2 / 3, 1 / 3, -2 / 3; -2 / 3, -2 / 3, 1 / 3]
  let U := R.map Complex.ofRealHom
  let g (σ : Equiv.Perm (Fin 3)) : ℝ :=
    ((orderThreeAssignmentScore σ : ℝ) - 1) *
      ((orderThreeAssignmentScore σ : ℝ) - 2) * ((orderThreeAssignmentScore σ : ℝ) - 4)
  have hg (σ : Equiv.Perm (Fin 3)) : g σ = if σ = 1 then 12 else 0 := by
    have h := thirdMomentCostInt_eq σ
    by_cases hσ : σ = 1
    · rw [if_pos hσ] at h ⊢
      dsimp only [thirdMomentCostInt] at h
      dsimp only [g]
      exact_mod_cast h
    · rw [if_neg hσ] at h ⊢
      dsimp only [thirdMomentCostInt] at h
      dsimp only [g]
      exact_mod_cast h
  have hR : R * Rᵀ = 1 := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      norm_num [R, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ]
  have hUt : Uᴴ = Rᵀ.map Complex.ofRealHom := by
    ext i j : 1
    simp [U, Matrix.conjTranspose_apply, Complex.star_def]
  have hUU : U * Uᴴ = 1 := by
    rw [hUt]
    change R.map Complex.ofRealHom * Rᵀ.map Complex.ofRealHom = 1
    rw [← Matrix.map_mul, hR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hU : IsUnitary U := ⟨hUU, Matrix.mul_eq_one_comm.mp hUU⟩
  have hdR : R.det = -1 := by
    rw [Matrix.det_fin_three]
    change (1 / 3 : ℝ) * (1 / 3) * (1 / 3) - (1 / 3) * (-2 / 3) * (-2 / 3)
      - (-2 / 3) * (-2 / 3) * (1 / 3) + (-2 / 3) * (-2 / 3) * (-2 / 3)
      + (-2 / 3) * (-2 / 3) * (-2 / 3) - (-2 / 3) * (1 / 3) * (-2 / 3) = -1
    norm_num
  have hd : U.det = -1 := by
    change (Complex.ofRealHom.mapMatrix R).det = -1
    rw [← RingHom.map_det, hdR, map_neg, map_one]
  refine ⟨U, hU, ?_, ?_⟩
  · intro σ
    change 0 ≤ g σ
    rw [hg]
    split <;> norm_num
  · change (∑ σ, realSignedWeight U σ * g σ) = -4 / 9
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin 3))]
    · rw [hg, if_pos rfl, realSignedWeight, signedWeight, hd]
      norm_num [leibnizTerm, Equiv.Perm.sign_one,
        U, R, Fin.prod_univ_succ, Complex.mul_re, Complex.mul_im, Complex.div_re,
        Complex.normSq_apply]
    · intro σ _ hσ
      rw [hg, if_neg hσ, mul_zero]
    · simp

end MOC

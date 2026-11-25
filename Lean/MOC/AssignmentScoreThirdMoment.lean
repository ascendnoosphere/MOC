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
  let U : Matrix (Fin 3) (Fin 3) ℂ :=
    !![((1 / 3 : ℝ) : ℂ), ((-2 / 3 : ℝ) : ℂ), ((-2 / 3 : ℝ) : ℂ);
      ((-2 / 3 : ℝ) : ℂ), ((1 / 3 : ℝ) : ℂ), ((-2 / 3 : ℝ) : ℂ);
      ((-2 / 3 : ℝ) : ℂ), ((-2 / 3 : ℝ) : ℂ), ((1 / 3 : ℝ) : ℂ)]
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
  have hU : IsUnitary U := by
    constructor <;> ext i j : 1 <;> fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      norm_num [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
        Fin.sum_univ_succ, Complex.star_def, Complex.mul_re, Complex.mul_im]
  have hd : U.det = -1 := by
    apply Complex.ext <;>
      norm_num [U, Matrix.det_fin_three, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im]
  refine ⟨U, hU, ?_, ?_⟩
  · intro σ
    change 0 ≤ g σ
    rw [hg]
    split <;> norm_num
  · change (∑ σ, realSignedWeight U σ * g σ) = -4 / 9
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin 3))]
    · rw [hg, if_pos rfl]
      norm_num [realSignedWeight, signedWeight, leibnizTerm, hd, Equiv.Perm.sign_one,
        U, Fin.prod_univ_succ, Complex.mul_re, Complex.mul_im, Complex.div_re,
        Complex.normSq_apply]
    · intro σ _ hσ
      rw [hg, if_neg hσ, mul_zero]
    · simp

end MOC

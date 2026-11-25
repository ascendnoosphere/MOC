import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

open BigOperators Matrix

namespace MOC

noncomputable section

/-- Three real coordinates for the critical Klein-four budgets. -/
def kleinBudgetForm (u : Fin 3 → ℝ) (t : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  (∑ i, (u i - t) * x i ^ 2) + t / 2 * (∑ i, x i) ^ 2

private theorem binary_form_nonneg (A B C x y : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hdet : 0 ≤ A * C - B ^ 2) :
    0 ≤ A * x ^ 2 + 2 * B * x * y + C * y ^ 2 := by
  rcases hA.eq_or_lt with hr | hp
  · have hz : A = 0 := hr.symm
    have hB : B = 0 := sq_eq_zero_iff.mp (by
      rw [hz, zero_mul, zero_sub] at hdet
      exact le_antisymm (neg_nonneg.mp hdet) (sq_nonneg B))
    simp only [hz, hB, zero_mul, mul_zero, zero_add]
    exact mul_nonneg hC (sq_nonneg y)
  · apply nonneg_of_mul_nonneg_right _ hp
    rw [show A * (A * x ^ 2 + 2 * B * x * y + C * y ^ 2) =
      (A * x + B * y) ^ 2 + (A * C - B ^ 2) * y ^ 2 by ring]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hdet (sq_nonneg y))

private theorem binary_form_pos (A B C : ℝ) (x : Fin 2 → ℝ)
    (hA : 0 < A) (hdet : 0 < A * C - B ^ 2) (hx : x ≠ 0) :
    0 < A * x 0 ^ 2 + 2 * B * x 0 * x 1 + C * x 1 ^ 2 := by
  by_cases hy : x 1 = 0
  · have hx' : x 0 ≠ 0 := by
      intro hh
      apply hx
      funext i
      fin_cases i
      · exact hh
      · exact hy
    simpa only [hy, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero] using
      mul_pos hA (sq_pos_of_ne_zero hx')
  · apply pos_of_mul_pos_right _ hA.le
    rw [show A * (A * x 0 ^ 2 + 2 * B * x 0 * x 1 + C * x 1 ^ 2) =
      (A * x 0 + B * x 1) ^ 2 + (A * C - B ^ 2) * x 1 ^ 2 by ring]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hdet (sq_pos_of_ne_zero hy))

/-- If the mixed budget exceeds the strong threshold, the budget form has a
strictly negative linear compression of dimension two. Zero budgets are allowed. -/
theorem kleinBudgetForm_negative_plane (a b c t : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : b ≤ a) (hac : c ≤ a) (ht : 0 < t) (htrace : a * (b + c) - b * c < t) :
    ∃ L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ), ∀ x ≠ 0,
      kleinBudgetForm ![a ^ 2, b ^ 2, c ^ 2] t (L x) < 0 := by
  by_cases hbc : b + c = 0
  · have hb0 : b = 0 := by linarith only [hbc, hc, hb]
    have hc0 : c = 0 := by linarith only [hbc, hc, hb]
    subst b
    subst c
    let d := (a ^ 2 + t) / (2 * t)
    let B : Matrix (Fin 3) (Fin 2) ℝ := !![0, 1; 1, -d; -1, -d]
    refine ⟨B.mulVecLin, fun x hx => ?_⟩
    have hform :
        kleinBudgetForm ![a ^ 2, (0 : ℝ) ^ 2, (0 : ℝ) ^ 2] t (B.mulVecLin x) =
          -(2 * t * x 0 ^ 2 + (3 * t / 2) * x 1 ^ 2) := by
      simp only [kleinBudgetForm, B, d, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      field_simp [ht.ne']
      <;> ring
    rw [hform]
    have hp := binary_form_pos (2 * t) 0 (3 * t / 2) x (by positivity)
      (by have hp : 0 < (2 * t) * (3 * t / 2) := by positivity
          simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using hp) hx
    have hpos : 0 < 2 * t * x 0 ^ 2 + (3 * t / 2) * x 1 ^ 2 := by
      simpa only [mul_zero, zero_mul, add_zero] using hp
    exact neg_lt_zero.mpr hpos
  · have ha : 0 < a := by
      by_contra! ha
      have hb0 : b = 0 := le_antisymm (hab.trans ha) hb
      have hc0 : c = 0 := le_antisymm (hac.trans ha) hc
      exact hbc (by rw [hb0, hc0, zero_add])
    have hbcp := lt_of_le_of_ne (add_nonneg hb hc) (Ne.symm hbc)
    let T := a * (b + c) - b * c
    let N00 := (a - b) * (a * b * (a - b) + a ^ 2 * c + 2 * a * b * c + b ^ 2 * c)
    let N11 := (a - c) * (a * c * (a - c) + a ^ 2 * b + 2 * a * b * c + b * c ^ 2)
    let N01 := -(a - b) * (a - c) * (a * b + a * c + b * c)
    let P00 := (a + b) ^ 2
    let P11 := (a + c) ^ 2
    let P01 := -a ^ 2 + a * b + a * c + b * c
    have hn00 : 0 ≤ N00 := by
      have hab' := sub_nonneg.mpr hab
      dsimp only [N00]
      positivity
    have hn11 : 0 ≤ N11 := by
      have hac' := sub_nonneg.mpr hac
      dsimp only [N11]
      positivity
    have hnDet : 0 ≤ N00 * N11 - N01 ^ 2 := by
      have hE : N00 * N11 - N01 ^ 2 =
          4 * a ^ 2 * b * c * (a - b) * (a - c) * (a * b + a * c + 2 * b * c) := by
        dsimp only [N00, N11, N01]
        ring
      rw [hE]
      have hab' := sub_nonneg.mpr hab
      have hac' := sub_nonneg.mpr hac
      positivity
    have hp00 : 0 < P00 := by dsimp only [P00]; positivity
    have hpDet : 0 < P00 * P11 - P01 ^ 2 := by
      have hE : P00 * P11 - P01 ^ 2 = 4 * a ^ 2 * (a * (b + c) + b * c) := by
        dsimp only [P00, P11, P01]
        ring
      rw [hE]
      positivity
    let B : Matrix (Fin 3) (Fin 2) ℝ := !![-b, -c; a, 0; 0, a]
    refine ⟨B.mulVecLin, fun x hx => ?_⟩
    have hform : -2 * kleinBudgetForm ![a ^ 2, b ^ 2, c ^ 2] t (B.mulVecLin x) =
        (N00 * x 0 ^ 2 + 2 * N01 * x 0 * x 1 + N11 * x 1 ^ 2) +
          (t - T) * (P00 * x 0 ^ 2 + 2 * P01 * x 0 * x 1 + P11 * x 1 ^ 2) := by
      simp only [kleinBudgetForm, B, T, N00, N01, N11, P00, P01, P11,
        Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_two,
        Fin.sum_univ_three, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    have hn := binary_form_nonneg N00 N01 N11 (x 0) (x 1) hn00 hn11 hnDet
    have hp := binary_form_pos P00 P01 P11 x hp00 hpDet hx
    have hT : 0 < t - T := sub_pos.mpr htrace
    have hz := add_pos_of_nonneg_of_pos hn (mul_pos hT hp)
    rw [← hform] at hz
    linarith only [hz]

/-- A real sum of the real parts of four complex squares cannot be strictly
negative on the image of every nonzero vector of a five-dimensional space. -/
theorem no_negative_five_of_complex_squares {E : Type*} [AddCommGroup E] [Module ℝ E]
    (l : Fin 4 → E →ₗ[ℝ] ℂ) (L : (Fin 5 → ℝ) →ₗ[ℝ] E) :
    ∃ x : Fin 5 → ℝ, x ≠ 0 ∧ 0 ≤ ∑ i, ((l i (L x)) ^ 2).re := by
  let P : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
    { toFun := fun x i => (l i (L x)).im
      map_add' := by
        intro x y
        funext i
        simp only [map_add, Complex.add_im, Pi.add_apply]
      map_smul' := by
        intro r x
        funext i
        simp only [map_smul, Complex.smul_im, Pi.smul_apply, RingHom.id_apply] }
  have hdim : Module.finrank ℝ (Fin 4 → ℝ) < Module.finrank ℝ (Fin 5 → ℝ) := by
    rw [Module.finrank_pi, Module.finrank_pi]
    decide
  obtain ⟨x, hx, hx0⟩ := (LinearMap.ker P).ne_bot_iff.mp (P.ker_ne_bot_of_finrank_lt hdim)
  have him (i : Fin 4) : (l i (L x)).im = 0 := congrFun (LinearMap.mem_ker.mp hx) i
  refine ⟨x, hx0, Finset.sum_nonneg (fun i _ => ?_)⟩
  simpa only [pow_two, Complex.mul_re, him, mul_zero, sub_zero] using
    mul_self_nonneg (l i (L x)).re

end
end MOC

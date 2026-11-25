import MOC.PrincipalCoisometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact examples for the deletion and padding reductions in
*Principal minors and the Marcus–de Oliveira conjecture*. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private theorem finTwo_perm_entries (p : Equiv.Perm (Fin 2)) :
    (p 0 = 0 ∧ p 1 = 1) ∨ (p 0 = 1 ∧ p 1 = 0) := by
  have hne : p 0 ≠ p 1 := p.injective.ne (by decide)
  generalize p 0 = i at *
  generalize p 1 = j at *
  fin_cases i <;> fin_cases j <;> simp_all

/-- The Householder matrix for the nonnormal deletion example. -/
def deletionObstructionMixer : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1/3, -2/3, -2/3; -2/3, 1/3, -2/3; -2/3, -2/3, 1/3]

theorem deletionObstructionMixer_unitary : IsUnitary deletionObstructionMixer := by
  constructor <;> ext i j : 1 <;> fin_cases i <;> fin_cases j <;>
    norm_num [deletionObstructionMixer, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_three, Matrix.cons_val, Matrix.cons_val_two,
      Complex.star_def, map_ofNat]

/-- Delete the last row and column from the mixer. The lower-order
similarity term has determinant outside the lower matching hull. -/
theorem deletionObstruction_outside_matching_hull :
    let W := deletionObstructionMixer.submatrix Fin.castSucc Fin.castSucc
    let a : Fin 2 → ℂ := ![0, 1]
    let v := (diagonal a + W * diagonal a * W⁻¹).det
    v = 4 / 3 ∧ v ∉ convexHull ℝ (Set.range (matchingProduct a a)) := by
  classical
  intro W a v
  have hW : W = !![1/3, -2/3; -2/3, 1/3] := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> rfl
  let V : Matrix (Fin 2) (Fin 2) ℂ := !![-1, -2; -2, -1]
  have hVW : V * W = 1 := by
    rw [hW]
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      norm_num [V, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, Matrix.cons_val]
  have hdet : IsUnit W.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hW]
    norm_num [Matrix.det_fin_two, Matrix.cons_val]
  have hInv : W⁻¹ = V := by
    calc
      W⁻¹ = (V * W) * W⁻¹ := by rw [hVW, Matrix.one_mul]
      _ = V := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv W hdet, Matrix.mul_one]
  have hvalue : v = 4 / 3 := by
    change (diagonal a + W * diagonal a * W⁻¹).det = _
    rw [hInv, hW]
    norm_num [a, V, Matrix.det_fin_two, Matrix.add_apply, Matrix.diagonal_apply,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.cons_val]
  refine ⟨hvalue, fun hv => ?_⟩
  have hle : Complex.reLm v ≤ 1 := by
    apply convexHull_min _ ((convex_Iic (𝕜 := ℝ) (1 : ℝ)).linear_preimage Complex.reLm) hv
    rintro _ ⟨p, rfl⟩
    change (matchingProduct a a p).re ≤ 1
    rw [matchingProduct, Fin.prod_univ_two]
    rcases finTwo_perm_entries p with ⟨h₀,h₁⟩ | ⟨h₀,h₁⟩ <;>
      rw [h₀, h₁] <;> norm_num [a, Matrix.cons_val]
  rw [hvalue] at hle
  norm_num [Complex.reLm_coe, Complex.div_re, Complex.normSq] at hle

/-- The projection onto the real axis of the two square vertices is
constant, but every choice of one unused right label raises the support. -/
theorem paddingTwo_raises_real_support (z : ℂ) :
    let a : Fin 2 → ℂ := ![-Complex.I, 0]
    let b : Fin 2 → ℂ := ![-1, 1]
    let b' : Fin 3 → ℂ := ![-1, 1, z]
    (∀ p : Equiv.Perm (Fin 2), (matchingProduct a b p).re = -1) ∧
      ∃ e : Fin 2 ↪ Fin 3, 0 ≤ (rectangularMatchingProduct a b' e).re := by
  intro a b b'
  have inject (j : Fin 3) (hj : j ≠ 2) :
      Function.Injective (![2, j] : Fin 2 → Fin 3) := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all [Matrix.cons_val]
  let e₀ : Fin 2 ↪ Fin 3 := ⟨![2, 0], inject 0 (by decide)⟩
  let e₁ : Fin 2 ↪ Fin 3 := ⟨![2, 1], inject 1 (by decide)⟩
  refine ⟨?_, ?_⟩
  · intro p
    rw [matchingProduct, Fin.prod_univ_two]
    rcases finTwo_perm_entries p with ⟨h₀,h₁⟩ | ⟨h₀,h₁⟩ <;>
      rw [h₀,h₁] <;> norm_num [a, b, Matrix.cons_val, Complex.add_re, Complex.I_re]
  have h₀ : rectangularMatchingProduct a b' e₀ = -(z - Complex.I) := by
    rw [rectangularMatchingProduct, Fin.prod_univ_two]
    simp [a, b', e₀, Matrix.cons_val] <;> ring
  have h₁ : rectangularMatchingProduct a b' e₁ = z - Complex.I := by
    rw [rectangularMatchingProduct, Fin.prod_univ_two]
    simp [a, b', e₁, Matrix.cons_val] <;> ring
  by_cases h : 0 ≤ (z - Complex.I).re
  · exact ⟨e₁, by rwa [h₁]⟩
  · refine ⟨e₀, ?_⟩
    rw [h₀, Complex.neg_re]
    exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge h))

/-- The original three-label permutation hull has real support 8. -/
theorem paddingThree_original_support_eight :
    let a : Fin 3 → ℂ := ![2, -1, -1 + Complex.I]
    let b : Fin 3 → ℂ := ![1 - 2 * Complex.I, 2 + 2 * Complex.I, -1 + Complex.I]
    (∀ p : Equiv.Perm (Fin 3), (matchingProduct a b p).re ≤ 8) ∧
      ∃ p : Equiv.Perm (Fin 3), (matchingProduct a b p).re = 8 := by
  intro a b
  constructor
  · intro p
    have h₀₁ : p 0 ≠ p 1 := p.injective.ne (by decide)
    have h₀₂ : p 0 ≠ p 2 := p.injective.ne (by decide)
    have h₁₂ : p 1 ≠ p 2 := p.injective.ne (by decide)
    rw [matchingProduct, Fin.prod_univ_three]
    generalize p 0 = i at *
    generalize p 1 = j at *
    generalize p 2 = k at *
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [a, b, Matrix.cons_val, Matrix.cons_val_two, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at *
  · refine ⟨Equiv.swap (0 : Fin 3) 1, ?_⟩
    rw [matchingProduct, Fin.prod_univ_three,
      show Equiv.swap (0 : Fin 3) 1 2 = 2 by decide]
    norm_num [a, b, Matrix.cons_val, Matrix.cons_val_two, Equiv.swap_apply_def, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- For the order-three example two new injection values have a fixed
convex mean of 12 in the real direction, for every unused label. -/
theorem paddingThree_has_new_support_at_least_twelve (z : ℂ) :
    let a : Fin 3 → ℂ := ![2, -1, -1 + Complex.I]
    let b : Fin 4 → ℂ := ![1 - 2 * Complex.I, 2 + 2 * Complex.I, -1 + Complex.I, z]
    ∃ e : Fin 3 ↪ Fin 4, 12 ≤ (rectangularMatchingProduct a b e).re := by
  intro a b
  let e₀ : Fin 3 ↪ Fin 4 := ⟨![1, 3, 2], by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all [Matrix.cons_val]⟩
  let e₁ : Fin 3 ↪ Fin 4 := ⟨![3, 0, 1], by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all [Matrix.cons_val]⟩
  have h₀ : (rectangularMatchingProduct a b e₀).re = 12 - 12 * z.re - 4 * z.im := by
    rw [rectangularMatchingProduct, Fin.prod_univ_three]
    norm_num [a, b, e₀, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
      Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;> ring
  have h₁ : (rectangularMatchingProduct a b e₁).re = 12 + 6 * z.re + 2 * z.im := by
    rw [rectangularMatchingProduct, Fin.prod_univ_three]
    norm_num [a, b, e₁, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
      Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;> ring
  by_cases h : 12 ≤ (rectangularMatchingProduct a b e₀).re
  · exact ⟨e₀, h⟩
  · have ht := lt_of_not_ge h
    rw [h₀] at ht
    refine ⟨e₁, ?_⟩
    rw [h₁]
    linarith

end

end MOC

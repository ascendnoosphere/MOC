import MOC.Core
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Jacobi's determinant derivative at a diagonal matrix, including singular diagonal sums. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At a diagonal matrix only the diagonal entry derivatives contribute to the first variation. -/
theorem hasDerivAt_det_diagonal
    (M : ℝ → Matrix ι ι ℂ) (V : Matrix ι ι ℂ) (t : ℝ) (h : ι → ℂ)
    (hvalue : M t = diagonal h)
    (hderiv : ∀ i j, HasDerivAt (fun s => M s i j) (V i j) t) :
    HasDerivAt (fun s => (M s).det)
      (∑ i, (∏ j ∈ Finset.univ.erase i, h j) * V i i) t := by
  let f (σ : Equiv.Perm ι) (s : ℝ) := ∏ i, M s (σ i) i
  let df (σ : Equiv.Perm ι) := ∑ i, (∏ j ∈ Finset.univ.erase i, M t (σ j) j) * V (σ i) i
  let c (σ : Equiv.Perm ι) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ)
  have hσ (σ : Equiv.Perm ι) : HasDerivAt (fun s => c σ * f σ s) (c σ * df σ) t := by
    apply HasDerivAt.const_mul
    have hp := HasDerivAt.finset_prod (u := Finset.univ) (f := fun i s => M s (σ i) i)
      (f' := fun i => V (σ i) i) (fun i _ => hderiv (σ i) i)
    simpa only [f, df, Finset.prod_apply, smul_eq_mul] using hp
  have hz (σ : Equiv.Perm ι) (hσ' : σ ≠ 1) : df σ = 0 := by
    have hex : ∃ j, σ j ≠ j := by
      by_contra hh
      push_neg at hh
      exact hσ' (Equiv.ext hh)
    obtain ⟨j, hj⟩ := hex
    apply Finset.sum_eq_zero
    intro i _
    have hk : ∃ k, k ≠ i ∧ σ k ≠ k := by
      by_cases hji : j = i
      · exact ⟨σ j, hji ▸ hj, fun hh => hj (σ.injective hh)⟩
      · exact ⟨j, hji, hj⟩
    obtain ⟨k, hki, hk⟩ := hk
    have hp : (∏ j ∈ Finset.univ.erase i, M t (σ j) j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩)
      simp [hvalue, Matrix.diagonal_apply_ne _ hk]
    rw [hp, zero_mul]
  have hd := HasDerivAt.sum (u := Finset.univ) (fun σ _ => hσ σ)
  have hsum : (∑ σ, c σ * df σ) = ∑ i, (∏ j ∈ Finset.univ.erase i, h j) * V i i := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm ι)]
    · simp [c, df, hvalue]
    · intro σ _ hc
      rw [hz σ hc, mul_zero]
    · simp
  rw [hsum] at hd
  simpa only [Matrix.det_apply', c, f] using hd

/-- The invertible diagonal formula divides each contribution by the corresponding eigenvalue. -/
theorem hasDerivAt_det_diagonal_of_nonzero
    (M : ℝ → Matrix ι ι ℂ) (V : Matrix ι ι ℂ) (t : ℝ) (h : ι → ℂ)
    (hvalue : M t = diagonal h) (hnz : ∀ i, h i ≠ 0)
    (hderiv : ∀ i j, HasDerivAt (fun s => M s i j) (V i j) t) :
    HasDerivAt (fun s => (M s).det) ((diagonal h).det * ∑ i, V i i / h i) t := by
  convert hasDerivAt_det_diagonal M V t h hvalue hderiv using 1
  rw [Matrix.det_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ i)]
  field_simp [hnz i]
  ring

end MOC

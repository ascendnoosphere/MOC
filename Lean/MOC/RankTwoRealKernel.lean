import MOC.Hermitian
import MOC.RankTwoMatchingProfile

/-! A real rank-two kernel with nonzero diagonal is an additive matching
profile after nonzero real row and column scalings. -/

open BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real matching kernels with vanishing three-row minors satisfy the hull
bound for every unitary matrix. The nonzero diagonal ensures that the real
additive gauge exists even if some off-diagonal entries vanish. -/
theorem sum_signedWeight_mem_hull_of_real_rank_two_kernel
    (K : Matrix ι ι ℝ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hdiag : ∀ i, K i i ≠ 0)
    (hminor : ∀ r c : Fin 3 → ι, (K.submatrix r c).det = 0) :
    (∑ σ : Equiv.Perm ι, signedWeight U σ * ∏ j, (K (σ j) j : ℂ)) ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm ι => ∏ j, (K (σ j) j : ℂ))) := by
  letI : Infinite ℝ := Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective
  obtain ⟨l, m, a, b, _, _, he⟩ := exists_additive_gauge_of_three_minors_eq_zero K hminor
    (fun i => ⟨i, hdiag i⟩) (fun j => ⟨j, hdiag j⟩)
  let c : ℂ := (∏ i, (l i : ℂ)) * ∏ j, (m j : ℂ)
  let A (i : ι) : ℂ := a i
  let B (j : ι) : ℂ := b j
  have hp (σ : Equiv.Perm ι) : (∏ j, (K (σ j) j : ℂ)) = c * matchingProduct A B σ := by
    simp only [he, c, A, B, matchingProduct, Complex.ofReal_add, Complex.ofReal_mul,
      Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => (l i : ℂ))]
  have hd :
      (∑ σ : Equiv.Perm ι, signedWeight U σ * ∏ j, (K (σ j) j : ℂ)) =
        c * determinantValue A B U := by
    rw [← signed_determinant A B U hU, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hp, mul_left_comm (signedWeight U σ) c]
  exact hull_of_common_factor hd hp (holds_of_real_spectra a b U hU)

end MOC

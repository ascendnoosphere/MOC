import MOC.Claim
import MOC.RankTwoKernelInclusion
import MOC.Singular

/-! The reduction requires a construction of the larger rank-two kernel.
The predicate states the determinant and separation conditions for that construction. -/

open BigOperators Matrix

namespace MOC

/-- The zero-point determinant theorem applies to rank-two Hadamard kernels. -/
theorem zero_mem_kernelMatchingHull_of_kernelDeterminantValue_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K U : Matrix ι ι ℂ) (hK : K.rank ≤ 2) (hU : IsUnitary U)
    (hz : kernelDeterminantValue K U = 0) :
    0 ∈ convexHull ℝ (Set.range (kernelMatchingProduct K)) := by
  obtain ⟨d, a, b, hp⟩ := exists_spectral_profile_of_rank_le_two K hK
  by_cases hd : d = 0
  · apply subset_convexHull ℝ _
    refine ⟨Equiv.refl ι, ?_⟩
    rw [hp, hd, zero_mul]
  · have he : kernelDeterminantValue K U = d * determinantValue a b U := by
      rw [kernelDeterminantValue_eq_sum_realSigned K U hK hU, real_signed_determinant a b U hU,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [hp, mul_left_comm (realSignedWeight U σ : ℂ) d]
    have hD : determinantValue a b U = 0 := by
      rw [he] at hz
      exact (mul_eq_zero.mp hz).resolve_left hd
    rw [← hz]
    exact hull_of_common_factor he hp (holds_of_singular a b hU hD)

/-- A proposed larger rank-two kernel translates the determinant by an
exterior point while keeping zero outside the new matching hull. -/
def SeparationPreservingDeterminantSuspension : Prop :=
  ∀ (n : ℕ) (K U : Matrix (Fin n) (Fin n) ℂ) (z : ℂ), K.rank ≤ 2 → IsUnitary U →
    z ∉ convexHull ℝ (Set.range (kernelMatchingProduct K)) →
    ∃ (m : ℕ) (K' U' : Matrix (Fin m) (Fin m) ℂ) (d : ℂ),
      n < m ∧ K'.rank ≤ 2 ∧ IsUnitary U' ∧ d ≠ 0 ∧
      kernelDeterminantValue K' U' = d * (kernelDeterminantValue K U - z) ∧
      0 ∉ convexHull ℝ (Set.range (kernelMatchingProduct K'))

/-- The proposed determinant suspension would imply the unrestricted conjecture. -/
theorem mocIsTrue_of_determinantSuspension (h : SeparationPreservingDeterminantSuspension) :
    MOCIsTrue := by
  intro n
  apply rankTwoKernelInclusion_iff_conjecture.mp
  intro K U hK hU
  by_contra hz
  obtain ⟨m, K', U', d, _, hK', hU', _, he, hsep⟩ :=
    h n K U (kernelDeterminantValue K U) hK hU hz
  rw [sub_self, mul_zero] at he
  exact hsep (zero_mem_kernelMatchingHull_of_kernelDeterminantValue_eq_zero K' U' hK' hU' he)

end MOC

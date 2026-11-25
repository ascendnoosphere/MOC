import MOC.AlternatingGapMoments

/-! Alternating second moments on partial matching fibres. -/

open Matrix BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matchingProduct_partial_fibre (a b : ι → ℂ) (ρ : Equiv.Perm ι)
    (S : Finset ι) (τ : Equiv.Perm S) :
    matchingProduct a b (ρ * Equiv.Perm.ofSubtype τ) =
      (∏ j ∈ Sᶜ, (a (ρ j) + b j)) *
        matchingProduct (fun i : S => a (ρ i)) (fun i : S => b i) τ := by
  unfold matchingProduct
  rw [← Finset.prod_compl_mul_prod S]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Equiv.Perm.mul_apply,
      Equiv.Perm.ofSubtype_apply_of_not_mem τ (Finset.mem_compl.mp hj)]
  · rw [← Finset.prod_coe_sort S]
    apply Finset.prod_congr rfl
    intro j _
    rw [Equiv.Perm.mul_apply, Equiv.Perm.ofSubtype_apply_of_mem τ j.property]

/-- Freeing any five or more labels, while keeping all other assignments
fixed, gives equal parity second gap moments on that fibre. Parity is
relative to the fixed pivot; no nonzero matching product is required. -/
theorem alternating_projected_gap_second_moment_fibre (a b : ι → ℂ)
    (η : ℂ) (H : ℝ) (ρ : Equiv.Perm ι) (S : Finset ι) (hS : 4 < S.card) :
    (∑ τ : Equiv.Perm S, parityReal τ *
      (H - (η * matchingProduct a b (ρ * Equiv.Perm.ofSubtype τ)).re)^2) = 0 := by
  simp_rw [matchingProduct_partial_fibre, ← mul_assoc]
  exact alternating_projected_gap_second_moment_zero (fun i : S => a (ρ i))
    (fun i : S => b i) _ H (by simpa using hS)

end MOC

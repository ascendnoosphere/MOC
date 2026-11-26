import MOC.SegreConvexity
import MOC.Support

open Matrix

namespace MOC

/-- The conjecture is equivalent to the absence of a strict separator of
the exterior transport by a complex product-tensor evaluation and a real projection. -/
theorem conjecture_iff_no_separating_spectral_witness {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Conjecture ι ↔ ∀ (U : Matrix ι ι ℂ), IsUnitary U →
      ∀ a₀ a₁ b₀ b₁ : ι → ℂ, ¬ ∃ η : ℂ, ∀ σ : Equiv.Perm ι,
        (η * productTensorEvaluation a₀ a₁ b₀ b₁ (subsetPermutationOperator σ)).re <
          (η * productTensorEvaluation a₀ a₁ b₀ b₁ (exteriorTransportOperator U)).re := by
  rw [conjecture_iff_segre_admissible]
  constructor
  · rintro h U hU a₀ a₁ b₀ b₁ ⟨η, hη⟩
    let f : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ η)
    let z := productTensorEvaluation a₀ a₁ b₀ b₁ (exteriorTransportOperator U)
    have hz := h U hU a₀ a₁ b₀ b₁
    have hh : f z < f z := by
      apply convexHull_min _ (convex_halfSpace_lt f.isLinear (f z)) hz
      rintro _ ⟨σ, rfl⟩
      exact hη σ
    exact (lt_irrefl _) hh
  · intro h U hU a₀ a₁ b₀ b₁
    apply mem_hull_of_directional_bound
    intro η
    by_contra! hη
    exact h U hU a₀ a₁ b₀ b₁ ⟨η, hη⟩

end MOC

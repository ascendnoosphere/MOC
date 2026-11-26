import MOC.SegreConvexity
import MOC.Support

/-! The support test on the convex hull of subset permutation operators
uses only functionals from the two spectral lists. -/

open Matrix

namespace MOC.Reformulations

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluate at the square-free spectral vectors, with the subset
complement on the first vector. -/
def spectralSubsetEvaluation (a b : ι → ℂ) :
    Matrix (Finset ι) (Finset ι) ℝ →ₗ[ℝ] ℂ :=
  productTensorEvaluation a (fun _ => 1) (fun _ => 1) b

private theorem spectralSubsetEvaluation_exterior (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    spectralSubsetEvaluation a b (exteriorTransportOperator U) = determinantValue a b U := by
  unfold spectralSubsetEvaluation
  rw [productTensorEvaluation_exterior _ _ _ _ U hU]
  simpa only [mul_one, one_mul] using kernelDeterminantValue_additive a b U hU

private theorem spectralSubsetEvaluation_permutation (a b : ι → ℂ) (p : Equiv.Perm ι) :
    spectralSubsetEvaluation a b (subsetPermutationOperator p) = matchingProduct a b p := by
  simpa only [spectralSubsetEvaluation, productTensorEvaluation_permutation,
    mul_one, one_mul, matchingProduct]

/-- Pair the exterior table and each subset permutation with the two spectral
product vectors. This is exactly the determinant matching-hull test. -/
theorem holds_iff_spectral_subset_evaluation (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) : Holds a b U ↔
    spectralSubsetEvaluation a b (exteriorTransportOperator U) ∈
      convexHull ℝ (Set.range fun p : Equiv.Perm ι =>
        spectralSubsetEvaluation a b (subsetPermutationOperator p)) := by
  unfold Holds
  simp only [spectralSubsetEvaluation_exterior a b U hU, spectralSubsetEvaluation_permutation]

/-- Real support functionals tested by the two spectral product vectors. -/
def spectralSubsetSupport (a b : ι → ℂ) (η : ℂ) :
    Matrix (Finset ι) (Finset ι) ℝ →ₗ[ℝ] ℝ :=
  (Complex.reLm.comp (LinearMap.mulLeft ℝ η)).comp (spectralSubsetEvaluation a b)

/-- It is equivalent to test the exterior table against the permutation
operator polytope in every direction supplied by the two spectral vectors. -/
theorem holds_iff_restricted_subset_operator_support (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U ↔
    ∀ η : ℂ, ∃ P : Matrix (Finset ι) (Finset ι) ℝ,
      P ∈ convexHull ℝ (Set.range (subsetPermutationOperator (ι := ι))) ∧
      spectralSubsetSupport a b η (exteriorTransportOperator U) ≤ spectralSubsetSupport a b η P := by
  classical
  rw [holds_iff_directional]
  constructor
  · intro h η
    obtain ⟨p, hp⟩ := h η
    refine ⟨subsetPermutationOperator p, subset_convexHull ℝ _ ⟨p, rfl⟩, ?_⟩
    simpa only [spectralSubsetSupport, LinearMap.comp_apply, Complex.reLm_coe,
      LinearMap.mulLeft_apply, spectralSubsetEvaluation_exterior a b U hU,
      spectralSubsetEvaluation_permutation] using hp
  · intro h η
    obtain ⟨P, hP, hbound⟩ := h η
    let L := spectralSubsetSupport a b η
    obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
      (fun σ : Equiv.Perm ι => L (subsetPermutationOperator σ)) ⟨1, Finset.mem_univ _⟩
    have hmax : L P ≤ L (subsetPermutationOperator p) := by
      apply convexHull_min _ (convex_halfSpace_le L.isLinear _) hP
      rintro _ ⟨σ, rfl⟩
      exact hp σ (Finset.mem_univ _)
    refine ⟨p, ?_⟩
    simpa only [L, spectralSubsetSupport, LinearMap.comp_apply, Complex.reLm_coe,
      LinearMap.mulLeft_apply, spectralSubsetEvaluation_exterior a b U hU,
      spectralSubsetEvaluation_permutation] using hbound.trans hmax

end
end MOC.Reformulations

import MOC.FourSubsetIndicatorCoordinates
import MOC.RealMatchingSquares

/-! The selected indicator columns span the order-four matching space. -/

open Matrix BigOperators

namespace MOC

private theorem generator_mem (k : Fin 14) :
    fourMatchingEvaluation (Pi.single k (1 : ℝ)) ∈ LinearMap.range fourIndicatorBasis.mulVecLin := by
  refine ⟨fun j => (fourIndicatorCoefficient k j : ℝ), ?_⟩
  funext p
  have hcast := congrArg (Int.cast : ℤ → ℝ) (fourIndicatorCoefficient_identity k p)
  have hsingle : (fun j => (((Pi.single k (1 : ℤ) : Fin 14 → ℤ) j : ℤ) : ℝ)) =
      (Pi.single k (1 : ℝ) : Fin 14 → ℝ) := by
    funext j
    by_cases h : j = k <;> simp [Pi.single_apply, h]
  have hcastEval (m : Fin 14 → ℤ) :
      fourMatchingEvaluation (fun j => (m j : ℝ)) p = (fourMatchingEvaluation (R := ℤ) m p : ℝ) := by
    fin_cases p <;> simp [fourMatchingEvaluation]
  change (∑ j, (fourIndicatorInt j p : ℝ) * (fourIndicatorCoefficient k j : ℝ)) = _
  simpa only [Int.cast_sum, Int.cast_mul, ← hcastEval, hsingle] using hcast

private noncomputable def evaluationMap : (Fin 14 → ℝ) →ₗ[ℝ] (Fin 24 → ℝ) where
  toFun := fourMatchingEvaluation
  map_add' x y := by
    funext p
    fin_cases p <;> simp [fourMatchingEvaluation] <;> ring
  map_smul' a x := by
    funext p
    fin_cases p <;> simp [fourMatchingEvaluation, smul_eq_mul] <;> ring

/-- The selected indicator columns span every matching evaluation. -/
theorem fourMatchingEvaluation_mem_indicatorRange (m : Fin 14 → ℝ) :
    fourMatchingEvaluation m ∈ LinearMap.range fourIndicatorBasis.mulVecLin := by
  let B := LinearMap.range fourIndicatorBasis.mulVecLin
  have hm : m = ∑ j, m j • (Pi.single j (1 : ℝ) : Fin 14 → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply, eq_comm]
  change evaluationMap m ∈ B
  rw [hm, map_sum]
  simp only [map_smul]
  exact B.sum_mem fun j _ => B.smul_mem _ (generator_mem j)

/-- The selected indicators span the full matching function space. -/
theorem fourIndicatorBasis_range : LinearMap.range fourIndicatorBasis.mulVecLin =
    realMatchingFunctionSpace := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    have he : fourIndicatorBasis.mulVecLin v =
        ∑ k, v k • (fun p => fourIndicatorBasis p k) := by
      funext p
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [he]
    exact realMatchingFunctionSpace.sum_mem fun k _ =>
      realMatchingFunctionSpace.smul_mem _ (realMatchingIndicator_mem _ _)
  · rintro _ ⟨m, rfl⟩
    exact fourMatchingEvaluation_mem_indicatorRange m

/-- A positive moment for the selected indicators gives a positive matching jet moment. -/
theorem realMatchingMoment_posSemidef_of_indicator_basis (c : Fin 24 → ℝ)
    (h : (fourIndicatorBasisᵀ * Matrix.diagonal c * fourIndicatorBasis).PosSemidef) :
    (realMatchingMoment c).PosSemidef := by
  have hcol (j : MatchingJetIndex) : ∃ v : Fin 14 → ℝ,
      fourIndicatorBasis.mulVecLin v = realMatchingJet.col j := by
    rw [← LinearMap.mem_range, fourIndicatorBasis_range, ← realMatchingJet_range,
      Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose v hv using hcol
  let C : Matrix (Fin 14) MatchingJetIndex ℝ := Matrix.of fun i j => v j i
  have hC : fourIndicatorBasis * C = realMatchingJet := by
    ext i j
    exact congrFun (hv j) i
  have hgram := h.conjTranspose_mul_mul_same C
  rw [realMatchingMoment, ← hC, Matrix.transpose_mul]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using hgram

end MOC

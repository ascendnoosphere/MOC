import MOC.FourMatchingIndicatorBasis
import MOC.FourMatchingPhysicalPositivity

/-! A thirteen-minor expansion with one signed correction in order four. -/

open BigOperators

namespace MOC

noncomputable section

/-- The matching labels in the thirteen-minor expansion, in row-to-column order. -/
def fourSignedMinorIndex (i : Fin 13) : Fin 24 :=
  ![5, 6, 8, 9, 11, 12, 14, 16, 17, 18, 19, 22, 23] i

/-- The ordinary subset indicators that supply the thirteen weights. -/
def fourSignedMinorFeature (i : Fin 13) : Fin 34 :=
  ![0, 16, 22, 11, 20, 17, 5, 31, 29, 14, 27, 24, 30] i

private def correctionProfileInt (p : Fin 24) : ℤ :=
  ordinaryCostRayInt 18 p - ordinaryCostRayInt 0 p - ordinaryCostRayInt 14 p -
    ordinaryCostRayInt 27 p

private def correctionProfile : Fin 24 → ℝ :=
  ordinaryCostRay 18 - ordinaryCostRay 0 - ordinaryCostRay 14 - ordinaryCostRay 27

/-- The spectral combination in the signed correction. Its last label is 1423. -/
def fourSignedMinorCombination : (Fin 24 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj 18 + LinearMap.proj 8 + LinearMap.proj 17 + LinearMap.proj 5 -
    LinearMap.proj 4

@[simp] theorem fourSignedMinorCombination_apply (g : Fin 24 → ℝ) :
    fourSignedMinorCombination g = g 18 + g 8 + g 17 + g 5 - g 4 := by
  simp only [fourSignedMinorCombination, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.proj_apply]

/-- The coefficient of the indicated matching in the ordinary part of the expansion. -/
def fourSignedMinorWeight (U : Matrix (Fin 4) (Fin 4) ℂ) (i : Fin 13) : ℝ :=
  fourSupportCostValue U (ordinaryCostRay (fourSignedMinorFeature i))

/-- The coefficient of the signed correction. -/
def fourSignedMinorCorrection (U : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  fourSupportCostValue U correctionProfile

theorem fourSignedMinorWeight_eq_minor (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (i : Fin 13) :
    fourSignedMinorWeight U i = subsetMinorSq U
      (ordinaryCostRows (fourSignedMinorFeature i)) (ordinaryCostColumns (fourSignedMinorFeature i)) :=
  fourSupportCostValue_ordinaryRay U hU _

theorem fourSignedMinorWeight_nonneg (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (i : Fin 13) : 0 ≤ fourSignedMinorWeight U i := by
  rw [fourSignedMinorWeight_eq_minor U hU]
  exact subsetMinorSq_nonneg U _ _

theorem fourSignedMinorCorrection_eq_minors (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) :
    fourSignedMinorCorrection U =
      subsetMinorSq U (ordinaryCostRows 18) (ordinaryCostColumns 18) -
      subsetMinorSq U (ordinaryCostRows 0) (ordinaryCostColumns 0) -
      subsetMinorSq U (ordinaryCostRows 14) (ordinaryCostColumns 14) -
      subsetMinorSq U (ordinaryCostRows 27) (ordinaryCostColumns 27) := by
  simp only [fourSignedMinorCorrection, correctionProfile, map_sub,
    fourSupportCostValue_ordinaryRay U hU]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem fourSignedMinorCorrection_eq_neg_mixed (U : Matrix (Fin 4) (Fin 4) ℂ) :
    fourSignedMinorCorrection U = -fourSupportCostValue U (mixedCostRay 29) := by
  have h : ∀ p : Fin 24, correctionProfileInt p = -mixedCostRayInt 29 p := by
    decide +kernel
  have hp : correctionProfile = -mixedCostRay 29 := by
    funext p
    simpa only [correctionProfile, correctionProfileInt, ordinaryCostRay, mixedCostRay,
      Int.cast_sub, Int.cast_neg, Pi.sub_apply, Pi.neg_apply] using
      congrArg (Int.cast : ℤ → ℝ) (h p)
  rw [fourSignedMinorCorrection, hp, map_neg]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
private theorem ordinaryRay_expansion_int (r : Fin 34) (p : Fin 24) :
    ordinaryCostRayInt r p = (∑ i : Fin 13,
      ordinaryCostRayInt r (fourSignedMinorIndex i) *
        ordinaryCostRayInt (fourSignedMinorFeature i) p) +
      (ordinaryCostRayInt r 18 + ordinaryCostRayInt r 8 + ordinaryCostRayInt r 17 +
        ordinaryCostRayInt r 5 - ordinaryCostRayInt r 4) * correctionProfileInt p := by
  revert p
  fin_cases r <;> decide +kernel

private theorem ordinaryRay_expansion (r : Fin 34) :
    ordinaryCostRay r =
      (∑ i : Fin 13, ordinaryCostRay r (fourSignedMinorIndex i) •
        ordinaryCostRay (fourSignedMinorFeature i)) +
      fourSignedMinorCombination (ordinaryCostRay r) • correctionProfile := by
  funext p
  simpa only [ordinaryCostRay, correctionProfileInt, correctionProfile,
    fourSignedMinorCombination_apply, Int.cast_add, Int.cast_sub, Int.cast_sum, Int.cast_mul,
    Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    congrArg (Int.cast : ℤ → ℝ) (ordinaryRay_expansion_int r p)

/-- The expansion is valid on the entire real span of the ordinary subset indicators. -/
theorem fourSignedMinorEvaluation (U : Matrix (Fin 4) (Fin 4) ℂ) (g : Fin 24 → ℝ)
    (hg : g ∈ Submodule.span ℝ (Set.range ordinaryCostRay)) :
    fourSupportCostValue U g =
      (∑ i : Fin 13, fourSignedMinorWeight U i * g (fourSignedMinorIndex i)) +
        fourSignedMinorCorrection U * fourSignedMinorCombination g := by
  let L : (Fin 24 → ℝ) →ₗ[ℝ] ℝ :=
    (∑ i : Fin 13, fourSignedMinorWeight U i • LinearMap.proj (fourSignedMinorIndex i)) +
      fourSignedMinorCorrection U • fourSignedMinorCombination
  have h : fourSupportCostValue U g = L g := by
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨r, rfl⟩ := hg
      have hr := congrArg (fourSupportCostValue U) (ordinaryRay_expansion r)
      simpa only [L, fourSignedMinorWeight, fourSignedMinorCorrection, map_add, map_sum, map_smul,
        LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
        smul_eq_mul, mul_comm] using hr
    | zero => simp only [map_zero]
    | add f g _ _ hf hg => simp only [map_add, hf, hg]
    | smul c g _ hg => simp only [map_smul, hg]
  simpa only [L, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul] using h

/-- Apply the signed expansion to the projection of the matching products. -/
theorem fourSignedMinorProjection (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (η : ℂ) :
    (η * determinantValue a b U).re =
      (∑ i : Fin 13, fourSignedMinorWeight U i *
        (η * matchingProduct a b (fourPerm (fourSignedMinorIndex i)).symm).re) +
      fourSignedMinorCorrection U * fourSignedMinorCombination
        (fun p => (η * matchingProduct a b (fourPerm p).symm).re) := by
  let g (p : Fin 24) := (η * matchingProduct a b (fourPerm p).symm).re
  have hg : g ∈ Submodule.span ℝ (Set.range ordinaryCostRay) := by
    have he : fourMatchingEvaluation
        (fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re) = g :=
      funext (fourMatchingEvaluation_spectral_real_part a b η)
    rw [← he]
    exact fourMatchingEvaluation_mem_ordinarySpan _
  have hneg : (fun p : Fin 24 => 0 - (η * matchingProduct a b (fourPerm p).symm).re) = -g := by
    funext p
    exact zero_sub (g p)
  have hr := fourSupportCostValue_spectral_eq a b η 0 U hU
  rw [hneg, map_neg, zero_sub] at hr
  exact (neg_injective hr).symm.trans (fourSignedMinorEvaluation U g hg)

/-- The thirteen squared-minor weights and one signed correction recover the determinant. -/
theorem fourSignedMinorDeterminant (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) :
    determinantValue a b U =
      (∑ i : Fin 13, (fourSignedMinorWeight U i : ℂ) *
        matchingProduct a b (fourPerm (fourSignedMinorIndex i)).symm) +
      (fourSignedMinorCorrection U : ℂ) *
        (matchingProduct a b (fourPerm 18).symm + matchingProduct a b (fourPerm 8).symm +
          matchingProduct a b (fourPerm 17).symm + matchingProduct a b (fourPerm 5).symm -
          matchingProduct a b (fourPerm 4).symm) := by
  apply Complex.ext
  · simpa only [one_mul, fourSignedMinorCombination_apply, Complex.add_re, Complex.sub_re,
      Complex.re_sum, Complex.re_ofReal_mul] using fourSignedMinorProjection a b U hU 1
  · simpa only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub, neg_neg, fourSignedMinorCombination_apply, Complex.add_im,
      Complex.sub_im, Complex.im_sum, Complex.im_ofReal_mul] using
      fourSignedMinorProjection a b U hU (-Complex.I)

end

end MOC

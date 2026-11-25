import MOC.TwoValues

/-!
# The antipodal center as a single squared minor

The precise center scale follows by applying the subset-image marginal
of Merikoski–Virtanen (DOI: 10.1016/0024-3795(89)90709-X). This proof
does not use a cosine–sine decomposition, and allows singular centers.
-/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spectral diagonal taking value +1 on the marked subset and −1
outside it. -/
def antipodalSigns (I : Finset ι) (i : ι) : ℂ := if i ∈ I then 1 else -1

/-- The nonzero product obtained when all signs align. -/
def antipodalAlignedProduct (J : Finset ι) : ℂ := ∏ j, (2 : ℂ) * antipodalSigns J j

theorem antipodalAlignedProduct_ne_zero (J : Finset ι) : antipodalAlignedProduct J ≠ 0 := by
  unfold antipodalAlignedProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases hj : j ∈ J <;> simp [antipodalSigns, hj]

/-- An antipodal matching is either zero or the common aligned product. -/
theorem matchingProduct_antipodal (I J : Finset ι) (σ : Equiv.Perm ι) :
    matchingProduct (antipodalSigns I) (antipodalSigns J) σ =
      if J.map σ.toEmbedding = I then antipodalAlignedProduct J else 0 := by
  classical
  by_cases him : J.map σ.toEmbedding = I
  · rw [if_pos him]
    unfold matchingProduct antipodalAlignedProduct
    apply Finset.prod_congr rfl
    intro j _
    have he : σ j ∈ I ↔ j ∈ J := by
      rw [← him, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    by_cases hj : j ∈ J <;> simp [antipodalSigns, he, hj] <;> ring
  · rw [if_neg him]
    have hex : ∃ j, ¬ (σ j ∈ I ↔ j ∈ J) := by
      by_contra he
      have hAll (j : ι) : σ j ∈ I ↔ j ∈ J := by
        by_contra hj
        exact he ⟨j, hj⟩
      apply him
      ext i
      simpa only [Finset.mem_map_equiv, Equiv.apply_symm_apply] using (hAll (σ.symm i)).symm
    obtain ⟨j, hj⟩ := hex
    unfold matchingProduct
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    by_cases hji : σ j ∈ I <;> by_cases hjj : j ∈ J <;>
      simp_all [antipodalSigns]

/-- Exact antipodal determinant value, without an invertibility assumption.
Unequal sign counts are covered by the zero convention for squared minors. -/
theorem determinantValue_antipodal_eq_aligned_mul_minor
    (I J : Finset ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    determinantValue (antipodalSigns I) (antipodalSigns J) U =
      antipodalAlignedProduct J * (subsetMinorSq U I J : ℂ) := by
  classical
  rw [← signed_determinant _ _ U hU,
    ← sum_signedWeight_image_eq_subsetMinorSq U hU I J,
    Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  rw [matchingProduct_antipodal]
  split_ifs <;> simp [mul_comm]

/-- The exact center multiplier is a single probability in [0,1]. -/
theorem antipodal_minor_mem_interval
    (I J : Finset ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    subsetMinorSq U I J ∈ Set.Icc 0 1 := by
  classical
  refine ⟨subsetMinorSq_nonneg U I J, ?_⟩
  rw [← sum_subsetMinorSq U hU J]
  exact Finset.single_le_sum (fun K _ => subsetMinorSq_nonneg U K J) (mem_univ I)

/-- The entire center is singular exactly when its matched squared minor vanishes. -/
theorem determinantValue_antipodal_eq_zero_iff
    (I J : Finset ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    determinantValue (antipodalSigns I) (antipodalSigns J) U = 0 ↔
      subsetMinorSq U I J = 0 := by
  rw [determinantValue_antipodal_eq_aligned_mul_minor I J U hU, mul_eq_zero]
  simp [antipodalAlignedProduct_ne_zero]

end

end MOC

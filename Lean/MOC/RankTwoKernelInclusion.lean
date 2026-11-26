import MOC.Geometry
import MOC.MatchingProfileCompactness
import MOC.RankTwoMatchingProfile
import Mathlib.Data.Matrix.Rank

/-! The determinant comparison for complex kernels of rank at most two. -/

open BigOperators Matrix

namespace MOC

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A sum of two products of row and column factors has rank at most two. -/
theorem rank_two_product_kernel_le (a b : ι → ℂ) (u v : κ → ℂ) :
    (Matrix.of fun i j => a i * u j + b i * v j).rank ≤ 2 := by
  let L : Matrix ι (Fin 2) ℂ := Matrix.of fun i k => if k = 0 then a i else b i
  let R : Matrix (Fin 2) κ ℂ := Matrix.of fun k j => if k = 0 then u j else v j
  have h : (Matrix.of fun i j => a i * u j + b i * v j) = L * R := by
    ext i j
    simp [L, R, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h]
  exact (Matrix.rank_mul_le_left L R).trans (by simpa using Matrix.rank_le_card_width L)

/-- The vector-space rank condition is equivalent to the determinant test
on every three-row and three-column submatrix. -/
theorem rank_le_two_iff_vanishing_three_minors (K : Matrix ι ι ℂ) :
    K.rank ≤ 2 ↔ VanishingThreeMinors K := by
  constructor
  · intro h r c
    have hfin : K.eRank ≠ ⊤ := ne_top_of_le_ne_top
      (by simp [ENat.card_eq_coe_fintype_card] : ENat.card ι ≠ ⊤) K.eRank_le_card_width
    have hsub : (K.submatrix r c).rank ≤ K.rank := by
      simpa only [Matrix.eRank_toNat_eq_rank] using ENat.toNat_le_toNat
        (K.eRank_submatrix_le r c) hfin
    by_contra hdet
    have hu := (Matrix.isUnit_iff_isUnit_det (K.submatrix r c)).2 (isUnit_iff_ne_zero.mpr hdet)
    have hr : (K.submatrix r c).rank = 3 := by
      simpa only [Fintype.card_fin] using Matrix.rank_of_isUnit _ hu
    omega
  · intro h
    obtain ⟨a, b, u, v, he⟩ := exists_two_product_factors_of_three_minors_eq_zero K h
    have hK : K = Matrix.of fun i j => a i * u j + b i * v j := by
      ext i j
      exact he i j
    rw [hK]
    exact rank_two_product_kernel_le a b u v

variable [DecidableEq ι]

/-- The determinant of the entrywise product, divided by the mixer determinant. -/
noncomputable def kernelDeterminantValue (K U : Matrix ι ι ℂ) : ℂ :=
  (Matrix.of fun i j => K i j * U i j).det / U.det

/-- The kernel inclusion at a given rank bound. -/
def RankKernelConjecture (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℕ) : Prop :=
  ∀ K U : Matrix ι ι ℂ, K.rank ≤ r → IsUnitary U →
    kernelDeterminantValue K U ∈ convexHull ℝ (Set.range (kernelMatchingProduct K))

theorem kernelDeterminantValue_additive (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    kernelDeterminantValue (Matrix.of fun i j => a i + b j) U = determinantValue a b U :=
  (determinantValue_eq_weightedEntryDet_div a b U hU).symm

theorem kernelDeterminantValue_eq_sum_signed (K U : Matrix ι ι ℂ) :
    kernelDeterminantValue K U =
      ∑ σ : Equiv.Perm ι, signedWeight U σ * kernelMatchingProduct K σ := by
  rw [kernelDeterminantValue, Matrix.det_apply', Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [signedWeight, leibnizTerm, kernelMatchingProduct, Matrix.of_apply,
    Finset.prod_mul_distrib]
  ring

/-- A rank-two kernel has an additive matching profile up to a common factor.
The factor can be zero when there is a zero row or column. -/
theorem exists_spectral_profile_of_rank_le_two (K : Matrix ι ι ℂ) (hK : K.rank ≤ 2) :
    ∃ (d : ℂ) (a b : ι → ℂ), ∀ σ,
      kernelMatchingProduct K σ = d * matchingProduct a b σ := by
  classical
  by_cases hrow : ∀ i, ∃ j, K i j ≠ 0
  · by_cases hcol : ∀ j, ∃ i, K i j ≠ 0
    · obtain ⟨L, R, a, b, _, _, he⟩ := exists_additive_gauge_of_three_minors_eq_zero K
        ((rank_le_two_iff_vanishing_three_minors K).mp hK) hrow hcol
      refine ⟨(∏ i, L i) * ∏ j, R j, a, b, fun σ => ?_⟩
      simp only [kernelMatchingProduct, matchingProduct, he, Finset.prod_mul_distrib,
        Equiv.prod_comp σ L]
    · push_neg at hcol
      obtain ⟨j, hj⟩ := hcol
      refine ⟨0, 0, 0, fun σ => ?_⟩
      rw [zero_mul]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (hj (σ j))
  · push_neg at hrow
    obtain ⟨i, hi⟩ := hrow
    refine ⟨0, 0, 0, fun σ => ?_⟩
    rw [zero_mul]
    exact Finset.prod_eq_zero (Finset.mem_univ (σ.symm i))
      (by simpa only [Equiv.apply_symm_apply] using hi (σ.symm i))

private theorem kernelDeterminantValue_of_spectral_profile (K U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (d : ℂ) (a b : ι → ℂ)
    (hp : ∀ σ, kernelMatchingProduct K σ = d * matchingProduct a b σ) :
    kernelDeterminantValue K U = d * determinantValue a b U := by
  rw [kernelDeterminantValue_eq_sum_signed, ← signed_determinant a b U hU, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hp, mul_left_comm (signedWeight U σ) d]

/-- For a rank-two kernel, the real signed weights give its determinant value. -/
theorem kernelDeterminantValue_eq_sum_realSigned (K U : Matrix ι ι ℂ)
    (hK : K.rank ≤ 2) (hU : IsUnitary U) :
    kernelDeterminantValue K U =
      ∑ σ : Equiv.Perm ι, (realSignedWeight U σ : ℂ) * kernelMatchingProduct K σ := by
  obtain ⟨d, a, b, hp⟩ := exists_spectral_profile_of_rank_le_two K hK
  rw [kernelDeterminantValue_of_spectral_profile K U hU d a b hp,
    ← real_signed_determinant a b U hU, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hp, mul_left_comm (realSignedWeight U σ : ℂ) d]

/-- The rank-two kernel comparison and the normal-matrix conjecture are
equivalent in the same finite order. Zero rows or columns give zero products. -/
theorem rankTwoKernelInclusion_iff_conjecture : RankKernelConjecture ι 2 ↔ Conjecture ι := by
  classical
  constructor
  · intro h a b U hU
    have hK : (Matrix.of fun i j => a i + b j).rank ≤ 2 := by
      simpa only [mul_one, one_mul] using rank_two_product_kernel_le a (fun _ => 1) (fun _ => 1) b
    have hh := h (Matrix.of fun i j => a i + b j) U hK hU
    rw [kernelDeterminantValue_additive a b U hU] at hh
    exact hh
  · intro h K U hK hU
    obtain ⟨d, a, b, hp⟩ := exists_spectral_profile_of_rank_le_two K hK
    exact hull_of_common_factor (kernelDeterminantValue_of_spectral_profile K U hU d a b hp)
      hp (h a b U hU)

end MOC

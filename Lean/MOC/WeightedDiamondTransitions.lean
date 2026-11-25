import MOC.WeightedDiamondAdjacency
import MOC.WeightedDiamondCensus
import Mathlib.Algebra.Module.Submodule.Range

/-! Ray generation across one certified permutation inequality. -/

open BigOperators

namespace MOC

variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype ν]

/-- Replace the kept and adjacent crossing rays by positively rescaled
representatives in the next list. Those representatives generate the clipped cone. -/
theorem exists_conic_weights_after_adjacent_cut (W : Submodule ℝ (ι → ℝ))
    (s : Finset ι) (j : ι) (r : κ → ι → ℝ) (q : ν → ι → ℝ)
    (hzero : ∀ v ∈ W, (∀ i ∈ s, v i = 0) → v = 0)
    (hrW : ∀ k, r k ∈ W) (hr : ∀ k i, i ∈ s → 0 ≤ r k i)
    (hsep : ∀ k l, k ≠ l → ∃ i ∈ s, 0 < r k i ∧ r l i = 0)
    (hgen : ∀ v ∈ W, (∀ i ∈ s, 0 ≤ v i) →
      ∃ w : κ → ℝ, (∀ k, 0 ≤ w k) ∧ v = ∑ k, w k • r k)
    (hq : ∀ k i, i ∈ s → 0 ≤ q k i)
    (hqpos : ∀ k, ∃ i ∈ s, 0 < q k i)
    (hkeep : ∀ k, 0 ≤ r k j → ∃ (l : ν) (c : ℝ), 0 ≤ c ∧ r k = c • q l)
    (hcross : ∀ p n, 0 < r p j → r n j < 0 →
      (∀ k, k ≠ p → k ≠ n → ∃ i ∈ s, r p i = 0 ∧ r n i = 0 ∧ 0 < r k i) →
      ∃ (l : ν) (c : ℝ), 0 ≤ c ∧ r p j • r n - r n j • r p = c • q l)
    (v : ι → ℝ) (hvW : v ∈ W) (hv : ∀ i ∈ s, 0 ≤ v i) (hvj : 0 ≤ v j) :
    ∃ w : ν → ℝ, (∀ k, 0 ≤ w k) ∧ v = ∑ k, w k • q k := by
  classical
  by_cases hz : v = 0
  · exact ⟨fun _ => 0, fun _ => le_rfl, by simp [hz]⟩
  let A : (ι → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ s, LinearMap.proj i
  have hA (u : ι → ℝ) : A u = ∑ i ∈ s, u i := by
    simp only [A, LinearMap.sum_apply, LinearMap.proj_apply]
  have hAn (k : ν) : 0 < A (q k) := by
    rw [hA]
    obtain ⟨i, hi, hpos⟩ := hqpos k
    exact hpos.trans_le (Finset.single_le_sum (fun i hi => hq k i hi) hi)
  have hAv : 0 < A v := by
    rw [hA]
    apply lt_of_le_of_ne (Finset.sum_nonneg hv)
    intro he
    exact hz (hzero v hvW fun i hi =>
      (Finset.sum_eq_zero_iff_of_nonneg hv).mp he.symm i hi)
  refine exists_conic_weights_of_linear_tests q A v hAn hAv fun L hL => ?_
  apply adjacent_halfspace_support_nonneg W s j r hzero hrW hr hsep hgen L ?_ ?_ v hvW hv hvj
  · intro k hk
    obtain ⟨l, c, hc, he⟩ := hkeep k hk
    rw [he, map_smul, smul_eq_mul]
    exact mul_nonneg hc (hL l)
  · intro p n hp hn ha
    obtain ⟨l, c, hc, he⟩ := hcross p n hp hn ha
    rw [he, map_smul, smul_eq_mul]
    exact mul_nonneg hc (hL l)

noncomputable section

/-- Interpret coefficients in the twelve pivot rays as permutation evaluations. -/
def weightedDiamondPivotMap (x : ℝ) : (Fin 12 → ℝ) →ₗ[ℝ] (Fin 24 → ℝ) where
  toFun w := ∑ k, w k • weightedDiamondPivotRay x k
  map_add' u v := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c u := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

/-- The linear subspace determined by the pivot evaluations. -/
def weightedDiamondRaySpace (x : ℝ) : Submodule ℝ (Fin 24 → ℝ) :=
  LinearMap.range (weightedDiamondPivotMap x)

theorem weightedDiamondPivotMap_at_pivot (x : ℝ) (w : Fin 12 → ℝ) (k : Fin 12) :
    weightedDiamondPivotMap x w (weightedDiamondPivot k) = w k * (1 + x) := by
  classical
  change (∑ j, w j • weightedDiamondPivotRay x j) (weightedDiamondPivot k) = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, weightedDiamondPivotRay_at_pivot,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- A vector of permutation evaluations is determined by its twelve pivot values. -/
theorem weightedDiamondRaySpace_eq_zero_of_pivots {x : ℝ} (hx : 0 ≤ x)
    {v : Fin 24 → ℝ} (hv : v ∈ weightedDiamondRaySpace x)
    (hz : ∀ j, v (weightedDiamondPivot j) = 0) : v = 0 := by
  obtain ⟨w, rfl⟩ := hv
  have hw : w = 0 := by
    funext k
    have hh := hz k
    rw [weightedDiamondPivotMap_at_pivot] at hh
    exact (mul_eq_zero.mp hh).resolve_right (by positivity)
  rw [hw, map_zero]

/-- The original rays generate the cone defined by nonnegativity on the pivots. -/
theorem weightedDiamondRaySpace_weights_of_pivots {x : ℝ} (hx : 0 ≤ x)
    {v : Fin 24 → ℝ} (hv : v ∈ weightedDiamondRaySpace x)
    (hn : ∀ j, 0 ≤ v (weightedDiamondPivot j)) :
    ∃ w : Fin 12 → ℝ, (∀ j, 0 ≤ w j) ∧ v = ∑ j, w j • weightedDiamondPivotRay x j := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨w, fun j => ?_, rfl⟩
  have hj := hn j
  rw [weightedDiamondPivotMap_at_pivot] at hj
  exact nonneg_of_mul_nonneg_left hj (by positivity)

/-- Weighted-diamond slacks are in the pivot space. -/
theorem weightedDiamondSlack_mem_raySpace {x : ℝ} (hx : 0 ≤ x) (c : ℝ)
    (f g : Fin 4 → ℝ) (s : Finset (Fin 4) → ℝ) :
    (fun i => c - weightedDiamondScore (1 + x) f g s (fourPerm i)) ∈ weightedDiamondRaySpace x := by
  have hscore (i : Fin 24) : weightedDiamondScore (1 + x) (fun k => c - f k)
      (fun k => -g k) (fun I => -s I) (fourPerm i) =
      c - weightedDiamondScore (1 + x) f g s (fourPerm i) := by
    unfold weightedDiamondScore
    ring
  refine ⟨fun k => (c - weightedDiamondScore (1 + x) f g s
    (fourPerm (weightedDiamondPivot k))) / (1 + x), ?_⟩
  funext i
  change (∑ j, ((c - weightedDiamondScore (1 + x) f g s
    (fourPerm (weightedDiamondPivot j))) / (1 + x)) * weightedDiamondPivotRay x j i) = _
  simpa only [hscore] using
    (weightedDiamondScore_pivot x hx (fun k => c - f k) (fun k => -g k) (fun I => -s I) i).symm

end

end MOC

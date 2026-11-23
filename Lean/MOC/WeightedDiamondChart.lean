import MOC.WeightedDiamondCensusPath
import MOC.WeightedDiamondFacetCoefficients
import Mathlib.Topology.Order.DenselyOrdered

/-! Transport a certified ray census to the order-four support statement. -/

open BigOperators Matrix

namespace MOC
namespace RayCoefficients

/-- Integer coordinates of twice a facet with the chart denominator cleared. -/
def homogeneousFacet (facet : WeightedDiamondFacetIndex) (i : Fin 24) (num den : Poly) : Poly :=
  let a := weightedDiamondBaseCoefficients facet.2 (facet.1⁻¹ * fourPerm i)
  add (add (scale (a 0) (mul den den)) (scale (a 1) (mul num den)))
    (scale (a 2) (mul num num))

/-- A checked ray path with verified final facet identifications gives the
weighted-diamond decomposition at the chart value. -/
theorem weightedDiamondFacetCompleteness_of_chart {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x)
    (num den : Poly) (hden : 0 < eval t den) (hchart : x = eval t num / eval t den)
    {initial final : RayStage} (path : RayCensusPath initial final)
    (hbase : initial.Generates t (weightedDiamondRaySpace x))
    (facet : Fin final.size → WeightedDiamondFacetIndex)
    (scales : Fin final.size → Poly) (hp : ∀ k, positive (scales k) = true)
    (hc : ∀ k i, equal (homogeneousFacet (facet k) i num den)
      (mul (scale 2 (scales k)) (final.rays k i)) = true) :
    WeightedDiamondFacetCompletenessAt x := by
  classical
  intro c f g s hb
  let v (i : Fin 24) := c - weightedDiamondScore (1 + x) f g s (fourPerm i)
  obtain ⟨w, hw, hsum⟩ := (path.generates ht hbase).2.2 v
    (weightedDiamondSlack_mem_raySpace hx c f g s)
    (fun i _ => sub_nonneg.mpr (hb (fourPerm i)))
  let q (k : Fin final.size) := (eval t den) ^ 2 / eval t (scales k)
  have hq (k : Fin final.size) : 0 ≤ q k :=
    div_nonneg (sq_nonneg _) (eval_pos_of_check ht (hp k)).le
  have hr (k : Fin final.size) (i : Fin 24) : rowEval t (final.rays k) i =
      q k * weightedDiamondFacet (facet k) x (diamondPermProfile (fourPerm i)) := by
    have he := eval_eq_of_check t (hc k i)
    have hf := weightedDiamondFacet_homogeneous (facet k) (fourPerm i)
      (eval t num) (eval t den) hden.ne'
    simp only [homogeneousFacet, eval_add, eval_scale, eval_mul, Int.cast_ofNat] at he
    rw [← hchart] at hf
    dsimp only [q, rowEval]
    have hscale := (eval_pos_of_check ht (hp k)).ne'
    field_simp [hscale]
    linear_combination he.symm / 2 + hf.symm / 2
  let d (a : WeightedDiamondFacetIndex) := ∑ k, if facet k = a then w k * q k else 0
  refine ⟨d, fun a => Finset.sum_nonneg (fun k _ => by
    split_ifs <;> simp [mul_nonneg (hw k) (hq k)]), ?_⟩
  intro σ
  obtain ⟨i, rfl⟩ := fourPerm_surjective σ
  have he := congrFun hsum i
  simp only [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  rw [he]
  calc
    _ = ∑ k, (w k * q k) * weightedDiamondFacet (facet k) x (diamondPermProfile (fourPerm i)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hr, mul_assoc]
    _ = _ := by
      simp only [d, Finset.sum_mul, mul_ite, zero_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simp

/-- Bounds on the open chart give the weighted-diamond bound through the
closed endpoint t = 2. -/
theorem weightedDiamond_support_le_two_of_lower_chart
    (hc : ∀ u : ℝ, 0 < u → WeightedDiamondFacetCompletenessAt (u / (1 + u))) :
    ∀ t : ℝ, 1 < t → t ≤ 2 → ∀ U : Matrix (Fin 4) (Fin 4) ℂ,
      IsUnitary U → WeightedDiamondSupportAt t U := by
  intro t ht ht₂ U hU
  have hs : Set.Ioo (1 : ℝ) 2 ⊆ {q : ℝ | WeightedDiamondSupportAt q U} := by
    intro s hs
    have h₁ : 0 < s - 1 := sub_pos.mpr hs.1
    have h₂ : 0 < 2 - s := sub_pos.mpr hs.2
    let u := (s - 1) / (2 - s)
    have hu : 0 < u := div_pos h₁ h₂
    have he : u / (1 + u) = s - 1 := by
      dsimp only [u]
      field_simp [h₂.ne'] <;> ring
    have hh := hc u hu
    rw [he] at hh
    have h := weightedDiamondSupport_of_facetCompleteness (s - 1) h₁.le hh U hU
    rwa [show 1 + (s - 1) = s by ring] at h
  apply closure_minimal hs (isClosed_weightedDiamondSupportAt U)
  rw [closure_Ioo (by norm_num : (1 : ℝ) ≠ 2)]
  exact ⟨ht.le, ht₂⟩

/-- The chart x = u/(1+u) for positive u suffices for the order-four
Hermitian-by-normal case. -/
theorem hermitianByNormal_four_of_lower_diamond_chart
    (hc : ∀ u : ℝ, 0 < u → WeightedDiamondFacetCompletenessAt (u / (1 + u))) :
    HermitianByNormal (Fin 4) :=
  hermitianByNormal_four_of_weightedDiamond_support_le_two
    (weightedDiamond_support_le_two_of_lower_chart hc)

end RayCoefficients
end MOC

import MOC.WeightedDiamondRayCertificate

/-! Assemble the certified cuts and apply the pivot reconstruction. -/

open BigOperators

namespace MOC
namespace RayCoefficients

structure RayStage where
  size : ℕ
  rays : Fin size → Row
  imposed : Finset (Fin 24)

/-- A chain of checked transitions. Each step adds one coordinate inequality. -/
inductive RayCensusPath : RayStage → RayStage → Prop
  | refl (stage : RayStage) : RayCensusPath stage stage
  | cons {old next final : RayStage} {j : Fin 24}
      (plan : RayCutPlan old.size next.size)
      (h : plan.Valid old.rays next.rays old.imposed j)
      (hnext : next.imposed = insert j old.imposed)
      (tail : RayCensusPath next final) : RayCensusPath old final

def RayStage.Generates (stage : RayStage) (t : ℝ) (W : Submodule ℝ (Fin 24 → ℝ)) : Prop :=
  (∀ k, rowEval t (stage.rays k) ∈ W) ∧
  (∀ v ∈ W, (∀ i ∈ stage.imposed, v i = 0) → v = 0) ∧
  ∀ v ∈ W, (∀ i ∈ stage.imposed, 0 ≤ v i) →
    ∃ w : Fin stage.size → ℝ, (∀ k, 0 ≤ w k) ∧ v = ∑ k, w k • rowEval t (stage.rays k)

/-- Iterating the cut theorem preserves exact generation at each stage. -/
theorem RayCensusPath.generates {old final : RayStage} (path : RayCensusPath old final)
    {t : ℝ} (ht : 0 < t) {W : Submodule ℝ (Fin 24 → ℝ)}
    (h : old.Generates t W) : final.Generates t W := by
  induction path with
  | refl => exact h
  | @cons old next final j plan hplan hnext tail ih =>
    obtain ⟨hold, hzero, hgen⟩ := h
    apply ih
    refine ⟨hplan.next_mem ht W hold, ?_, ?_⟩
    · intro v hv he
      exact hzero v hv fun i hi => he i (hnext ▸ Finset.mem_insert_of_mem hi)
    · intro v hv hn
      rw [hnext] at hn
      exact hplan.generate ht W hzero hold hgen v hv
        (fun i hi => hn i (Finset.mem_insert_of_mem hi)) (hn j (Finset.mem_insert_self j _))

/-- The twelve pivot rays generate the first stage after any positive rescaling. -/
theorem pivotStage_generates (x : ℝ) (hx : 0 ≤ x) (t : ℝ) (rows : Fin 12 → Row)
    (scale : Fin 12 → ℝ) (hs : ∀ k, 0 < scale k)
    (he : ∀ k, weightedDiamondPivotRay x k = scale k • rowEval t (rows k)) :
    (⟨12, rows, Finset.univ.image weightedDiamondPivot⟩ : RayStage).Generates
      t (weightedDiamondRaySpace x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hp : weightedDiamondPivotRay x k ∈ weightedDiamondRaySpace x := by
      classical
      refine ⟨fun j => if j = k then 1 else 0, ?_⟩
      change (∑ j, (if j = k then (1 : ℝ) else 0) • weightedDiamondPivotRay x j) = _
      simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [he k] at hp
    have hm := (weightedDiamondRaySpace x).smul_mem (scale k)⁻¹ hp
    simpa only [smul_smul, inv_mul_cancel₀ (hs k).ne', one_smul] using hm
  · intro v hv hz
    exact weightedDiamondRaySpace_eq_zero_of_pivots hx hv
      (fun j => hz _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  · intro v hv hn
    obtain ⟨w, hw, hwv⟩ := weightedDiamondRaySpace_weights_of_pivots hx hv
      (fun j => hn _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
    refine ⟨fun k => w k * scale k, fun k => mul_nonneg (hw k) (hs k).le, ?_⟩
    simp only [hwv, he, smul_smul]

/-- Clear the positive chart denominator when checking a pivot row. -/
theorem chart_pivotStage_generates (t : ℝ) (ht : 0 < t) (x : ℝ) (hx : 0 ≤ x)
    (num den : Poly) (hden : 0 < eval t den) (hchart : x = eval t num / eval t den)
    (rows : Fin 12 → Row) (scales : Fin 12 → Poly) (hs : ∀ k, positive (scales k) = true)
    (hc : ∀ k i, equal
      (add (scale (weightedDiamondPivotCoefficients k i).1 den)
        (scale (weightedDiamondPivotCoefficients k i).2 num))
      (mul (scales k) (rows k i)) = true) :
    (⟨12, rows, Finset.univ.image weightedDiamondPivot⟩ : RayStage).Generates
      t (weightedDiamondRaySpace x) := by
  refine pivotStage_generates x hx t rows (fun k => eval t (scales k) / eval t den)
    (fun k => div_pos (eval_pos_of_check ht (hs k)) hden) ?_
  intro k
  funext i
  have he := eval_eq_of_check t (hc k i)
  simp only [eval_add, eval_scale, eval_mul] at he
  have hnum : eval t num = x * eval t den :=
    ((eq_div_iff hden.ne').mp hchart).symm
  rw [hnum] at he
  change weightedDiamondPivotRay x k i = (eval t (scales k) / eval t den) * eval t (rows k i)
  apply mul_left_cancel₀ hden.ne'
  rw [weightedDiamondPivotRay_eq_coefficients]
  calc
    _ = (weightedDiamondPivotCoefficients k i).1 * eval t den +
        (weightedDiamondPivotCoefficients k i).2 * (x * eval t den) := by ring
    _ = eval t (scales k) * eval t (rows k i) := he
    _ = _ := by
      rw [← mul_assoc, mul_comm (eval t den), div_mul_cancel₀ _ hden.ne']

/-- A checked path from a pivot stage through every coordinate generates all
nonnegative slacks of the weighted-diamond score. -/
theorem rayCensusPath_slack (x : ℝ) (hx : 0 ≤ x) (t : ℝ) (ht : 0 < t)
    (rows : Fin 12 → Row) (scale : Fin 12 → ℝ) (hs : ∀ k, 0 < scale k)
    (he : ∀ k, weightedDiamondPivotRay x k = scale k • rowEval t (rows k))
    (final : RayStage)
    (path : RayCensusPath ⟨12, rows, Finset.univ.image weightedDiamondPivot⟩ final)
    (c : ℝ) (f g : Fin 4 → ℝ) (s : Finset (Fin 4) → ℝ)
    (hscore : ∀ i : Fin 24, weightedDiamondScore (1 + x) f g s (fourPerm i) ≤ c) :
    ∃ w : Fin final.size → ℝ, (∀ k, 0 ≤ w k) ∧
      (fun i => c - weightedDiamondScore (1 + x) f g s (fourPerm i)) =
        ∑ k, w k • rowEval t (final.rays k) := by
  have hgen := (path.generates ht (pivotStage_generates x hx t rows scale hs he)).2.2
  apply hgen _ (weightedDiamondSlack_mem_raySpace hx c f g s)
  intro i _
  exact sub_nonneg.mpr (hscore i)

end RayCoefficients
end MOC

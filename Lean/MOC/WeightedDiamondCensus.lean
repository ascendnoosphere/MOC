import MOC.ContactCensus
import MOC.WeightedDiamondPolynomial

/-! The initial coordinate cone for the weighted-diamond facet census. -/

open BigOperators

namespace MOC

/-- Permutation evaluations that determine a weighted-diamond score. -/
def weightedDiamondPivot : Fin 12 → Fin 24 := ![0, 1, 2, 3, 4, 6, 7, 8, 9, 12, 13, 18]

private def pivotConstant : Fin 12 → Fin 24 → ℤ :=
  ![![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0],
    ![0, 1, 0, 0, 0, -1, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, -1, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0, 1],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 1, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, -1, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1]]

private def pivotSlope : Fin 12 → Fin 24 → ℤ :=
  ![![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 0, 0, -1, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, -2, -1, 0, 0, -1, 0, -1, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 1, 0],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, 0, 0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 0, -1, -1, -2, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, -1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1]]

/-- Initial rays, normalized to have value `1 + x` at their own pivot. -/
def weightedDiamondPivotRay (x : ℝ) (j : Fin 12) (i : Fin 24) : ℝ :=
  (pivotConstant j i : ℝ) + x * (pivotSlope j i : ℝ)

/-- Integer constant and linear coefficient of a pivot ray coordinate. -/
def weightedDiamondPivotCoefficients (j : Fin 12) (i : Fin 24) : ℤ × ℤ :=
  (pivotConstant j i, pivotSlope j i)

theorem weightedDiamondPivotRay_eq_coefficients (x : ℝ) (j : Fin 12) (i : Fin 24) :
    weightedDiamondPivotRay x j i = (weightedDiamondPivotCoefficients j i).1 +
      x * (weightedDiamondPivotCoefficients j i).2 := rfl

set_option maxRecDepth 6000 in
private theorem pivotValueCoefficients (j k : Fin 12) :
    pivotConstant j (weightedDiamondPivot k) = (if j = k then 1 else 0) ∧
      pivotSlope j (weightedDiamondPivot k) = (if j = k then 1 else 0) := by
  fin_cases j <;> fin_cases k <;> decide +kernel

/-- The initial rays are nonnegative on the pivot constraints, with one
positive pivot evaluation each. -/
theorem weightedDiamondPivotRay_at_pivot (x : ℝ) (j k : Fin 12) :
    weightedDiamondPivotRay x j (weightedDiamondPivot k) = if j = k then 1 + x else 0 := by
  obtain ⟨h₀, h₁⟩ := pivotValueCoefficients j k
  unfold weightedDiamondPivotRay
  rw [h₀, h₁]
  split_ifs <;> simp

private abbrev ScoreCoordinate := Fin 4 ⊕ (Fin 4 ⊕ Finset (Fin 4))

private def scoreConstant (i : Fin 24) : ScoreCoordinate → ℤ
  | .inl k => if fourPerm i 0 = k then 1 else 0
  | .inr (.inl k) => if fourPerm i 3 = k then 1 else 0
  | .inr (.inr I) => (if ({0, 1} : Finset (Fin 4)).map (fourPerm i).toEmbedding = I then 1 else 0) +
      (if ({0, 2} : Finset (Fin 4)).map (fourPerm i).toEmbedding = I then 1 else 0)

private def scoreSlope (i : Fin 24) : ScoreCoordinate → ℤ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr I) => if ({0, 2} : Finset (Fin 4)).map (fourPerm i).toEmbedding = I then 1 else 0

set_option maxRecDepth 6000 in
set_option maxHeartbeats 10000000 in
private theorem pivotCoefficients (i : Fin 24) : ∀ k : ScoreCoordinate,
    (∑ j, scoreConstant (weightedDiamondPivot j) k * pivotConstant j i) = scoreConstant i k ∧
    (∑ j, (scoreConstant (weightedDiamondPivot j) k * pivotSlope j i +
      scoreSlope (weightedDiamondPivot j) k * pivotConstant j i)) = scoreConstant i k + scoreSlope i k ∧
    (∑ j, scoreSlope (weightedDiamondPivot j) k * pivotSlope j i) = scoreSlope i k := by
  fin_cases i <;> decide +kernel

private def scoreGenerator (x : ℝ) (i : Fin 24) (k : ScoreCoordinate) : ℝ :=
  (scoreConstant i k : ℝ) + x * (scoreSlope i k : ℝ)

private theorem scoreGenerator_reconstruct (x : ℝ) (i : Fin 24) (k : ScoreCoordinate) :
    (1 + x) * scoreGenerator x i k =
      ∑ j, scoreGenerator x (weightedDiamondPivot j) k * weightedDiamondPivotRay x j i := by
  obtain ⟨h₀, h₁, h₂⟩ := pivotCoefficients i k
  have h₀' := congrArg (fun n : ℤ => (n : ℝ)) h₀
  have h₁' := congrArg (fun n : ℤ => (n : ℝ)) h₁
  have h₂' := congrArg (fun n : ℤ => (n : ℝ)) h₂
  simp only [Int.cast_sum, Int.cast_add, Int.cast_mul] at h₀' h₁' h₂'
  calc
    _ = (scoreConstant i k : ℝ) + x * ((scoreConstant i k : ℝ) + (scoreSlope i k : ℝ)) +
        x ^ 2 * (scoreSlope i k : ℝ) := by unfold scoreGenerator; ring
    _ = _ := by
      rw [← h₁', ← h₂', ← h₀']
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      unfold scoreGenerator weightedDiamondPivotRay
      ring

private theorem score_eq_generators (x : ℝ) (f g : Fin 4 → ℝ) (s : Finset (Fin 4) → ℝ) (i : Fin 24) :
    weightedDiamondScore (1 + x) f g s (fourPerm i) =
      ∑ k : ScoreCoordinate, Sum.elim f (Sum.elim g s) k * scoreGenerator x i k := by
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, scoreGenerator, scoreConstant,
    scoreSlope, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_zero, add_zero, mul_add, Finset.sum_add_distrib]
  simp_rw [← mul_assoc, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', weightedDiamondScore] <;> ring

/-- The pivot evaluations give an exact nonnegative ray decomposition whenever
those twelve scores are nonnegative. -/
theorem weightedDiamondScore_pivot (x : ℝ) (hx : 0 ≤ x)
    (f g : Fin 4 → ℝ) (s : Finset (Fin 4) → ℝ) (i : Fin 24) :
    weightedDiamondScore (1 + x) f g s (fourPerm i) =
      ∑ j, (weightedDiamondScore (1 + x) f g s (fourPerm (weightedDiamondPivot j)) /
        (1 + x)) * weightedDiamondPivotRay x j i := by
  let d : ScoreCoordinate → ℝ := Sum.elim f (Sum.elim g s)
  have hx' : 1 + x ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hx)
  have hm : (1 + x) * weightedDiamondScore (1 + x) f g s (fourPerm i) =
      ∑ j, weightedDiamondScore (1 + x) f g s (fourPerm (weightedDiamondPivot j)) *
        weightedDiamondPivotRay x j i := by
    simp_rw [score_eq_generators]
    change (1 + x) * (∑ k, d k * scoreGenerator x i k) = _
    rw [Finset.mul_sum]
    simp_rw [mul_left_comm (1 + x), scoreGenerator_reconstruct x i, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  apply mul_left_cancel₀ hx'
  rw [hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, mul_comm (1 + x), div_mul_cancel₀ _ hx']

/-- The twelve pivot constraints supply a nonnegative decomposition of a
score slack in the initial cone of the census. -/
theorem weightedDiamondSlack_pivot (x : ℝ) (hx : 0 ≤ x) (c : ℝ)
    (f g : Fin 4 → ℝ) (s : Finset (Fin 4) → ℝ)
    (hn : ∀ j, weightedDiamondScore (1 + x) f g s
      (fourPerm (weightedDiamondPivot j)) ≤ c) :
    ∃ w : Fin 12 → ℝ, (∀ j, 0 ≤ w j) ∧ ∀ i,
      c - weightedDiamondScore (1 + x) f g s (fourPerm i) =
        ∑ j, w j * weightedDiamondPivotRay x j i := by
  refine ⟨fun j => (c - weightedDiamondScore (1 + x) f g s
    (fourPerm (weightedDiamondPivot j))) / (1 + x),
    fun j => div_nonneg (sub_nonneg.mpr (hn j)) (add_nonneg zero_le_one hx), ?_⟩
  have hscore (i : Fin 24) : weightedDiamondScore (1 + x) (fun k => c - f k)
      (fun k => -g k) (fun I => -s I) (fourPerm i) =
      c - weightedDiamondScore (1 + x) f g s (fourPerm i) := by
    unfold weightedDiamondScore
    ring
  intro i
  simpa only [hscore] using weightedDiamondScore_pivot x hx (fun k => c - f k)
    (fun k => -g k) (fun I => -s I) i

end MOC

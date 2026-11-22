import MOC.WeightedDiamondFirstCut

namespace MOC.RayCoefficients

private def initialScales : Fin 12 → Poly :=
  ![[1], [1], [1], [1], [1, 2], [1], [1], [1, 2], [1, 2], [1], [1], [1, 2]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem initialIdentity (k : Fin 12) : ∀ i : Fin 24, equal
    (add (scale (weightedDiamondPivotCoefficients k i).1 [1, 1])
      (scale (weightedDiamondPivotCoefficients k i).2 [0, 1]))
    (mul (initialScales k) (weightedDiamondLowerRays0 k i)) = true := by
  fin_cases k <;> decide +kernel

/-- The first cut in the lower parameter chart generates the complete cone
obtained by adding the inequality at permutation label five to the pivots. -/
theorem weightedDiamondLowerFirstCut_generates (t : ℝ) (ht : 0 < t) :
    (⟨16, weightedDiamondLowerRays1, insert 5 {0, 1, 2, 3, 4, 6, 7, 8, 9, 12, 13, 18}⟩ :
      RayStage).Generates t (weightedDiamondRaySpace (t / (1 + t))) := by
  have hd : 0 < eval t [1, 1] := by
    simp only [eval, Int.cast_one, mul_zero, add_zero, mul_one]
    exact add_pos zero_lt_one ht
  have hchart : t / (1 + t) = eval t [0, 1] / eval t [1, 1] := by simp [eval]
  have hs : ∀ k, positive (initialScales k) = true := by decide +kernel
  have h := chart_pivotStage_generates t ht _ (div_nonneg ht.le (by positivity))
    [0, 1] [1, 1] hd hchart weightedDiamondLowerRays0 initialScales hs initialIdentity
  have hpivots : Finset.univ.image weightedDiamondPivot =
      ({0, 1, 2, 3, 4, 6, 7, 8, 9, 12, 13, 18} : Finset (Fin 24)) := by decide +kernel
  rw [hpivots] at h
  exact weightedDiamondLowerCut0.generates ht h

end MOC.RayCoefficients

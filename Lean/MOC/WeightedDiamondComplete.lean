import MOC.WeightedDiamondLowerFinal
import MOC.WeightedDiamondLowerFacets

namespace MOC.RayCoefficients

/-- Every slack on the positive lower chart is a nonnegative sum of facets. -/
theorem weightedDiamond_lower_complete (u : ℝ) (hu : 0 < u) :
    WeightedDiamondFacetCompletenessAt (u / (1 + u)) := by
  have hd : 0 < eval u [1, 1] := by
    simp only [eval, Int.cast_one, mul_zero, add_zero, mul_one]
    exact add_pos zero_lt_one hu
  have hx : 0 ≤ u / (1 + u) := div_nonneg hu.le (by positivity)
  exact weightedDiamondFacetCompleteness_of_chart hu hx
    [0, 1] [1, 1] hd (by simp [eval]) lowerCompletePath
    (weightedDiamondLowerFirstCut_generates u hu)
    lowerFacet lowerScale lowerScale_positive lowerFacet_matches

end MOC.RayCoefficients

namespace MOC

/-- In order four, a real spectrum admits every complex partner and every unitary. -/
theorem hermitianByNormal_four : HermitianByNormal (Fin 4) :=
  RayCoefficients.hermitianByNormal_four_of_lower_diamond_chart
    RayCoefficients.weightedDiamond_lower_complete

end MOC

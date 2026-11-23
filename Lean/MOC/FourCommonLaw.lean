import MOC.WeightedDiamondComplete
import MOC.FourCommonLawReduction

namespace MOC

/-- At a fixed unitary, one law represents all complex partners of a real
spectrum of order four. The spectrum may have repeated entries. -/
theorem commonWeights_four_real (a : Fin 4 → ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : HasCommonWeights (fun i => (a i : ℂ)) U :=
  commonWeights_four_real_of_lower_chart RayCoefficients.weightedDiamond_lower_complete a U hU

end MOC

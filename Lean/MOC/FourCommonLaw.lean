import MOC.WeightedDiamondComplete
import MOC.FourCommonLawReduction
import MOC.CommonLawTransport

namespace MOC

/-- At a fixed unitary, one law represents all complex partners of a real
spectrum of order four. The spectrum may have repeated entries. -/
theorem commonWeights_four_real (a : Fin 4 → ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : HasCommonWeights (fun i => (a i : ℂ)) U :=
  commonWeights_four_real_of_lower_chart RayCoefficients.weightedDiamond_lower_complete a U hU

/-- A fixed first spectrum on a circle or line has one law for every partner
at each order-four relative unitary. -/
theorem commonWeights_four_circle (a : Fin 4 → ℂ) (hc : SpectrumOnGeneralizedCircle a)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) : HasCommonWeights a U :=
  commonWeights_on_circle_of_real U hU (fun x => commonWeights_four_real x U hU) a hc

end MOC

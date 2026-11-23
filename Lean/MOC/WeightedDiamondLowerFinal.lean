import MOC.WeightedDiamondLowerCut01
import MOC.WeightedDiamondLowerCut02
import MOC.WeightedDiamondLowerCut03
import MOC.WeightedDiamondLowerCut04
import MOC.WeightedDiamondLowerCut05
import MOC.WeightedDiamondLowerCut06
import MOC.WeightedDiamondLowerCut07
import MOC.WeightedDiamondLowerCut08
import MOC.WeightedDiamondLowerCut09
import MOC.WeightedDiamondLowerCut10
import MOC.WeightedDiamondLowerCut11

/-! Assemble all eleven remaining cuts of the positive parameter chart. -/

namespace MOC.RayCoefficients

abbrev lowerFinalStage := lowerStage12

theorem lowerCompletePath : RayCensusPath lowerStage1 lowerFinalStage := by
  refine .cons (next := lowerStage2) LowerCut1.plan LowerCut1.valid rfl ?_
  refine .cons (next := lowerStage3) LowerCut2.plan LowerCut2.valid rfl ?_
  refine .cons (next := lowerStage4) LowerCut3.plan LowerCut3.valid rfl ?_
  refine .cons (next := lowerStage5) LowerCut4.plan LowerCut4.valid rfl ?_
  refine .cons (next := lowerStage6) LowerCut5.plan LowerCut5.valid rfl ?_
  refine .cons (next := lowerStage7) LowerCut6.plan LowerCut6.valid rfl ?_
  refine .cons (next := lowerStage8) LowerCut7.plan LowerCut7.valid rfl ?_
  refine .cons (next := lowerStage9) LowerCut8.plan LowerCut8.valid rfl ?_
  refine .cons (next := lowerStage10) LowerCut9.plan LowerCut9.valid rfl ?_
  refine .cons (next := lowerStage11) LowerCut10.plan LowerCut10.valid rfl ?_
  refine .cons (next := lowerStage12) LowerCut11.plan LowerCut11.valid rfl ?_
  exact .refl _

end MOC.RayCoefficients

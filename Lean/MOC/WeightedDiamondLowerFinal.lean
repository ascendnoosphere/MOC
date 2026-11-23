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

theorem lowerCompletePath : RayCensusPath lowerStage1 lowerFinalStage :=
  .cons LowerCut1.plan LowerCut1.valid rfl (
    .cons LowerCut2.plan LowerCut2.valid rfl (
    .cons LowerCut3.plan LowerCut3.valid rfl (
    .cons LowerCut4.plan LowerCut4.valid rfl (
    .cons LowerCut5.plan LowerCut5.valid rfl (
    .cons LowerCut6.plan LowerCut6.valid rfl (
    .cons LowerCut7.plan LowerCut7.valid rfl (
    .cons LowerCut8.plan LowerCut8.valid rfl (
    .cons LowerCut9.plan LowerCut9.valid rfl (
    .cons LowerCut10.plan LowerCut10.valid rfl (
    .cons LowerCut11.plan LowerCut11.valid rfl (
    .refl _)))))))))))

end MOC.RayCoefficients

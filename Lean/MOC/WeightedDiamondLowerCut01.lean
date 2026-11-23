import MOC.WeightedDiamondLowerRows
import MOC.WeightedDiamondPackedCut

/-! Add the inequality at permutation 19 to the order-four ray census. -/

namespace MOC.RayCoefficients

namespace LowerCut1

set_option maxRecDepth 32000
set_option maxHeartbeats 60000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

private def edges : Array (Crossing 16 20) :=
  #[.keep 14 [1, 4, 4], .keep 15 [1, 2], .keep 16 [1, 2], .keep 17 [1, 4, 4], .keep 18 [1], .keep 19 [1]]

private def edgeIndex : Array (Array ℕ) :=
  #[
    #[0, 1],
    #[2, 3],
    #[4, 5]]

private def maskTable : Array ℕ :=
  #[33, 40, 48, 64, 128, 256, 512, 4096, 8192, 262144, 3, 5, 10, 12, 18, 20]

private def kept : Array (Fin 20) :=
  #[0, 1, 2, 3, 0, 4, 5, 0, 6, 7, 8, 9, 10, 11, 12, 13]

private def origin : Array (RayOrigin 16) :=
  #[.kept 0, .kept 1, .kept 2, .kept 3, .kept 5, .kept 6, .kept 8, .kept 9, .kept 10, .kept 11, .kept 12, .kept 13, .kept 14, .kept 15, .crossing 3 4, .crossing 3 7, .crossing 8 4, .crossing 8 7, .crossing 9 4, .crossing 9 7]

private def mask (p : Fin 16) : ℕ := maskTable.getD p.val 0

def plan : RayCutPlan 16 20 where
  kept p := kept.getD p.val 0
  crossing p k := edges.getD ((edgeIndex.getD (positiveIndex.getD p.val 0) #[]).getD
    (negativeIndex.getD k.val 0) 0) (.skip p)
  origin l := origin.getD l.val (.kept 0)

private abbrev old := lowerStage1.rays
private abbrev nextRows := lowerStage2.rays
private abbrev imposed := lowerStage1.imposed

private theorem oldSigns : ∀ p i, i ∈ imposed → zero (old p i) = true ∨ positive (old p i) = true := by
  apply checkRayBlocks
  intro k
  fin_cases k <;> decide +kernel

private theorem mask_eq : ∀ p i, (mask p).testBit i.val =
    (decide (i ∈ imposed) && positive (old p i)) := by
  apply checkRayBlocks
  intro k
  fin_cases k <;> decide +kernel

private theorem separate : ∀ p k, p ≠ k → let i := separationIndex mask p k
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply checkRayBlocks
  intro k
  fin_cases k <;> decide +kernel

private theorem crossing : ∀ p k, positive (old p 19) = true → negative (old k 19) = true →
    maskCrossing old nextRows imposed 19 mask p k (plan.crossing p k) := by
  apply checkRayBlocks
  intro k
  fin_cases k <;> decide +kernel

theorem valid : plan.Valid old nextRows imposed 19 := by
  obtain ⟨sep, cross⟩ := validateRayMasks plan mask oldSigns mask_eq separate crossing
  refine ⟨oldSigns, ?_, ?_, ?_, sep, ?_, cross, ?_⟩ <;> apply checkRayBlocks <;>
    intro k <;> fin_cases k <;> decide +kernel

end LowerCut1

end MOC.RayCoefficients

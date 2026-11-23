import MOC.WeightedDiamondLowerRows
import MOC.WeightedDiamondPackedCut

/-! Add the inequality at permutation 10 to the order-four ray census. -/

namespace MOC.RayCoefficients

namespace LowerCut4

set_option maxRecDepth 32000
set_option maxHeartbeats 60000000

private def positiveIndex : Array ℕ :=
  #[0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 5, 6, 0, 0, 0, 0, 0, 0, 7, 8, 0, 9, 0, 0, 0, 10, 11, 12, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0]

private def edges : Array (Crossing 34 71) :=
  #[.keep 28 [1], .keep 29 [1, 1], .keep 30 [1, 1], .skip 6, .skip 7, .keep 31 [1], .keep 32 [1], .keep 33 [1], .skip 9, .keep 34 [1], .skip 21, .keep 35 [1], .keep 36 [1], .keep 37 [1], .keep 38 [1], .skip 13, .keep 39 [0, 1], .keep 40 [1], .keep 41 [1], .keep 42 [1, 2], .skip 8, .skip 3, .keep 43 [1, 2], .keep 44 [1, 3, 2], .keep 45 [1, 3, 2], .skip 4, .keep 46 [1], .skip 19, .keep 47 [0, 1], .keep 48 [1], .keep 49 [1], .keep 50 [1, 2], .skip 10, .skip 5, .keep 51 [1], .keep 52 [1], .keep 53 [1], .keep 54 [1], .keep 55 [1], .keep 56 [1, 1], .keep 57 [1, 1], .skip 11, .keep 58 [1], .keep 59 [1], .skip 18, .keep 60 [1, 1], .keep 61 [1], .keep 62 [1], .keep 63 [1], .keep 64 [1], .keep 65 [1, 1], .keep 66 [1], .keep 67 [1], .keep 68 [1], .skip 16, .keep 69 [1], .keep 70 [1]]

private def edgeIndex : Array (Array ℕ) :=
  #[
    #[0, 1, 2, 3, 4, 4],
    #[5, 6, 7, 8, 9, 10],
    #[11, 12, 13, 3, 14, 15],
    #[16, 17, 18, 19, 20, 21],
    #[22, 23, 24, 25, 26, 27],
    #[28, 29, 30, 31, 32, 33],
    #[34, 35, 36, 4, 37, 10],
    #[38, 39, 40, 21, 41, 42],
    #[43, 44, 45, 21, 4, 4],
    #[46, 47, 48, 21, 32, 32],
    #[49, 50, 15, 33, 4, 4],
    #[51, 52, 53, 33, 20, 20],
    #[54, 55, 56, 8, 20, 20]]

private def maskTable : Array ℕ :=
  #[16417, 48, 16640, 33280, 565248, 786432, 49155, 5, 10, 32786, 4160, 8320, 61440, 282624, 524385, 524608, 276, 557123, 195, 12300, 45076, 266260, 552, 262784, 737, 780, 960, 266764, 532520, 532748, 278659, 262290, 466, 28712]

private def kept : Array (Fin 71) :=
  #[0, 1, 2, 3, 4, 5, 6, 0, 0, 7, 0, 8, 9, 10, 11, 12, 13, 0, 14, 0, 15, 16, 17, 18, 19, 20, 21, 0, 22, 23, 24, 25, 26, 27]

private def origin : Array (RayOrigin 34) :=
  #[.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 9, .kept 11, .kept 12, .kept 13, .kept 14, .kept 15, .kept 16, .kept 18, .kept 20, .kept 21, .kept 22, .kept 23, .kept 24, .kept 25, .kept 26, .kept 28, .kept 29, .kept 30, .kept 31, .kept 32, .kept 33, .crossing 0 7, .crossing 0 8, .crossing 0 10, .crossing 1 7, .crossing 1 8, .crossing 1 10, .crossing 1 19, .crossing 2 7, .crossing 2 8, .crossing 2 10, .crossing 2 19, .crossing 9 7, .crossing 9 8, .crossing 9 10, .crossing 9 17, .crossing 11 7, .crossing 11 8, .crossing 11 10, .crossing 11 19, .crossing 15 7, .crossing 15 8, .crossing 15 10, .crossing 15 17, .crossing 16 7, .crossing 16 8, .crossing 16 10, .crossing 16 19, .crossing 23 7, .crossing 23 8, .crossing 23 10, .crossing 23 27, .crossing 24 7, .crossing 24 10, .crossing 26 7, .crossing 26 8, .crossing 26 10, .crossing 30 7, .crossing 30 8, .crossing 31 7, .crossing 31 8, .crossing 31 10, .crossing 32 8, .crossing 32 10]

private def mask (p : Fin 34) : ℕ := maskTable.getD p.val 0

def plan : RayCutPlan 34 71 where
  kept p := kept.getD p.val 0
  crossing p k := edges.getD ((edgeIndex.getD (positiveIndex.getD p.val 0) #[]).getD
    (negativeIndex.getD k.val 0) 0) (.skip p)
  origin l := origin.getD l.val (.kept 0)

private abbrev old := lowerStage4.rays
private abbrev nextRows := lowerStage5.rays
private abbrev imposed := lowerStage4.imposed

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

private theorem crossing : ∀ p k, positive (old p 10) = true → negative (old k 10) = true →
    maskCrossing old nextRows imposed 10 mask p k (plan.crossing p k) := by
  apply checkRayBlocks
  intro k
  fin_cases k <;> decide +kernel

theorem valid : plan.Valid old nextRows imposed 10 := by
  obtain ⟨sep, cross⟩ := validateRayMasks plan mask oldSigns mask_eq separate crossing
  refine ⟨oldSigns, ?_, ?_, ?_, sep, ?_, cross, ?_⟩ <;> apply checkRayBlocks <;>
    intro k <;> fin_cases k <;> decide +kernel

end LowerCut4

end MOC.RayCoefficients

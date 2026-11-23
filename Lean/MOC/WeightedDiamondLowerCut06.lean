import MOC.WeightedDiamondLowerRows
import MOC.WeightedDiamondPackedCut

/-! Add the inequality at permutation 21 to the order-four ray census. -/

namespace MOC.RayCoefficients

namespace LowerCut6

set_option maxRecDepth 32000
set_option maxHeartbeats 60000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 6, 7, 0, 0, 0, 0, 0, 8, 9, 0, 0, 0, 0, 0, 0, 10, 0, 0, 11, 0, 0, 0, 0, 12, 0, 0, 13, 0, 14, 0, 0, 15, 0, 16, 0, 0, 17, 18, 0, 19, 0, 0, 0, 0, 0, 20, 0, 0, 21, 0, 22, 0, 0, 23, 0, 0, 24, 0, 25, 0, 0, 26, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 5, 0, 0, 0, 0, 6, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 8, 9, 10, 11, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 14, 0, 15, 16, 0, 0, 17, 18, 19, 20, 0, 21, 22, 0, 0, 23, 24, 0, 0, 25, 26]

private def edges : Array (Crossing 91 108) :=
  #[.skip 1, .keep 64 [1], .skip 2, .skip 27, .skip 16, .skip 18, .skip 7, .skip 8, .keep 65 [1], .skip 14, .keep 66 [1], .keep 67 [1], .keep 68 [1], .keep 69 [1], .keep 70 [1], .skip 35, .skip 20, .skip 32, .skip 19, .skip 34, .skip 21, .keep 71 [1], .keep 72 [1], .skip 39, .skip 3, .skip 5, .keep 73 [1], .skip 57, .skip 64, .skip 11, .skip 9, .keep 74 [1], .keep 75 [1], .skip 15, .keep 76 [1], .skip 40, .keep 77 [1], .keep 78 [1], .keep 79 [1], .skip 65, .skip 67, .skip 22, .keep 80 [1], .skip 26, .keep 81 [1], .skip 13, .skip 54, .keep 82 [1], .skip 33, .keep 83 [1, 2], .skip 12, .skip 23, .keep 84 [1], .keep 85 [1], .keep 86 [1], .skip 28, .keep 87 [1, 2], .skip 10, .skip 45, .skip 0, .skip 48, .keep 88 [2, 3], .keep 89 [1, 4, 4], .skip 24, .keep 90 [1], .skip 25, .keep 91 [1, 3, 2], .keep 92 [1, 3, 2], .keep 93 [1], .keep 94 [1], .skip 30, .keep 95 [1, 2], .skip 56, .skip 29, .skip 31, .skip 6, .skip 4, .keep 96 [1], .skip 49, .skip 80, .skip 83, .keep 97 [1], .skip 71, .skip 44, .skip 74, .skip 17, .skip 51, .keep 98 [1], .keep 99 [1, 3, 2], .skip 77, .keep 100 [1, 2], .keep 101 [1], .skip 61, .skip 62, .keep 102 [1], .skip 38, .skip 73, .keep 103 [1, 3, 2], .keep 104 [1, 2], .keep 105 [1, 3, 2], .skip 69, .keep 106 [1], .skip 37, .keep 107 [2, 6, 4]]

private def edgeIndex : Array (Array ℕ) :=
  #[
    #[0, 1, 0, 0, 0, 2, 3, 0, 2, 2, 0, 0, 0, 4, 2, 4, 4, 5, 2, 0, 0, 2, 2, 0, 0, 0, 0],
    #[6, 7, 4, 8, 9, 10, 11, 12, 13, 14, 15, 15, 0, 4, 4, 4, 4, 5, 16, 6, 6, 17, 7, 18, 9, 19, 19],
    #[6, 7, 20, 21, 9, 7, 22, 9, 23, 24, 25, 15, 26, 20, 20, 20, 20, 27, 27, 28, 19, 7, 7, 9, 9, 25, 19],
    #[29, 30, 31, 32, 33, 30, 34, 33, 23, 35, 36, 35, 37, 20, 38, 20, 20, 39, 40, 41, 41, 30, 30, 33, 33, 42, 23],
    #[2, 7, 43, 3, 7, 44, 7, 17, 45, 24, 30, 45, 46, 43, 43, 43, 7, 45, 2, 2, 2, 47, 7, 48, 7, 30, 45],
    #[49, 0, 0, 0, 0, 2, 15, 50, 24, 24, 41, 51, 0, 0, 0, 0, 0, 0, 24, 51, 51, 2, 2, 50, 50, 41, 51],
    #[0, 20, 52, 53, 20, 3, 54, 55, 45, 35, 25, 45, 0, 4, 4, 45, 4, 5, 29, 0, 0, 43, 20, 55, 20, 25, 45],
    #[56, 2, 0, 0, 0, 2, 35, 50, 16, 16, 25, 51, 0, 4, 2, 4, 4, 57, 16, 51, 51, 2, 2, 50, 50, 25, 51],
    #[16, 30, 0, 0, 0, 2, 58, 50, 16, 16, 41, 16, 0, 4, 2, 4, 4, 5, 16, 16, 16, 2, 2, 50, 50, 41, 16],
    #[0, 59, 0, 0, 0, 59, 60, 0, 45, 16, 0, 0, 0, 4, 59, 45, 4, 61, 16, 0, 0, 59, 59, 0, 0, 0, 0],
    #[59, 62, 43, 3, 63, 3, 64, 3, 45, 3, 30, 45, 55, 46, 18, 43, 63, 46, 2, 2, 2, 43, 63, 43, 63, 30, 45],
    #[0, 65, 66, 67, 68, 65, 69, 70, 45, 70, 45, 45, 71, 72, 18, 73, 74, 72, 50, 50, 50, 65, 63, 73, 74, 45, 45],
    #[6, 75, 55, 55, 9, 75, 45, 15, 45, 24, 45, 45, 55, 55, 75, 55, 9, 45, 50, 50, 50, 75, 75, 19, 9, 45, 45],
    #[6, 76, 57, 57, 76, 75, 76, 48, 24, 24, 25, 45, 0, 0, 24, 24, 24, 0, 24, 76, 6, 75, 76, 48, 76, 25, 45],
    #[29, 20, 55, 57, 20, 35, 77, 35, 45, 35, 25, 45, 50, 18, 18, 45, 18, 78, 78, 50, 50, 23, 79, 23, 80, 25, 45],
    #[6, 76, 57, 57, 76, 75, 76, 48, 24, 24, 25, 45, 0, 24, 24, 24, 24, 24, 24, 76, 6, 75, 76, 48, 76, 25, 45],
    #[50, 30, 55, 33, 33, 30, 81, 33, 45, 58, 45, 45, 55, 82, 18, 83, 82, 84, 78, 50, 50, 30, 30, 45, 33, 45, 45],
    #[50, 30, 33, 33, 33, 30, 58, 33, 18, 18, 33, 33, 0, 4, 30, 4, 4, 4, 85, 50, 50, 30, 30, 33, 33, 33, 33],
    #[0, 4, 45, 55, 4, 65, 60, 55, 45, 60, 45, 45, 0, 4, 45, 45, 4, 5, 5, 0, 0, 45, 4, 45, 4, 45, 45],
    #[50, 18, 45, 55, 18, 86, 87, 86, 45, 88, 45, 45, 50, 18, 45, 45, 18, 89, 90, 50, 50, 45, 18, 45, 18, 45, 45],
    #[59, 30, 41, 59, 30, 59, 30, 59, 2, 59, 59, 59, 41, 43, 2, 43, 30, 45, 2, 2, 2, 2, 2, 2, 2, 30, 2],
    #[2, 7, 75, 24, 7, 24, 7, 24, 75, 24, 24, 24, 2, 2, 75, 75, 7, 2, 2, 2, 2, 75, 7, 75, 7, 75, 75],
    #[24, 7, 55, 24, 9, 24, 91, 24, 45, 24, 24, 24, 55, 27, 75, 92, 93, 27, 78, 50, 50, 75, 7, 45, 9, 45, 45],
    #[24, 7, 18, 24, 9, 24, 9, 24, 45, 24, 24, 24, 50, 50, 75, 18, 9, 50, 50, 50, 50, 75, 7, 18, 9, 45, 45],
    #[0, 20, 45, 57, 20, 57, 94, 57, 45, 57, 25, 57, 55, 20, 45, 45, 20, 39, 95, 50, 50, 45, 20, 45, 20, 25, 45],
    #[29, 2, 50, 0, 50, 2, 40, 29, 18, 29, 25, 29, 50, 18, 2, 18, 18, 18, 18, 50, 50, 2, 2, 50, 50, 25, 50],
    #[0, 65, 55, 4, 55, 4, 96, 4, 45, 4, 45, 45, 55, 97, 18, 98, 99, 100, 18, 50, 50, 45, 18, 45, 18, 45, 45],
    #[2, 30, 41, 59, 30, 2, 30, 2, 2, 2, 30, 2, 41, 43, 2, 43, 30, 45, 2, 2, 2, 2, 2, 2, 2, 30, 2],
    #[0, 65, 45, 55, 55, 65, 101, 55, 45, 102, 45, 45, 55, 82, 45, 45, 102, 103, 78, 50, 50, 45, 18, 45, 18, 45, 45]]

private def maskTable : Array ℕ :=
  #[19489, 3120, 17664, 35328, 565248, 786432, 49155, 35858, 61440, 282624, 526433, 527680, 1300, 195, 45076, 266260, 2600, 265856, 3809, 780, 4032, 532520, 263314, 3538, 28712, 16421, 16427, 22625, 53, 58, 6256, 12348, 22848, 32791, 32794, 38994, 559187, 12480, 524613, 524618, 530752, 559427, 6484, 262789, 262794, 268992, 268940, 2789, 6881, 965, 970, 7104, 268498, 6610, 25761, 279715, 9392, 42624, 49925, 49930, 41605, 41610, 45708, 33557, 42130, 533729, 532709, 533952, 533836, 9896, 17194, 8877, 8874, 12972, 272000, 280195, 9953, 10176, 9682, 1498, 20805, 20810, 29004, 536908, 4437, 4446, 12636, 275084, 8933, 266458, 4570]

private def kept : Array (Fin 108) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 0, 0, 23, 24, 25, 26, 0, 0, 0, 0, 27, 28, 29, 30, 0, 31, 32, 33, 34, 0, 35, 36, 37, 38, 39, 40, 41, 0, 0, 0, 0, 42, 43, 0, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 0, 0, 56, 0, 0, 57, 58, 0, 0, 0, 0, 59, 0, 0, 60, 61, 0, 0, 62, 63, 0, 0]

private def origin : Array (RayOrigin 91) :=
  #[.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 8, .kept 9, .kept 10, .kept 11, .kept 12, .kept 13, .kept 14, .kept 15, .kept 16, .kept 17, .kept 18, .kept 19, .kept 20, .kept 21, .kept 22, .kept 25, .kept 26, .kept 27, .kept 28, .kept 33, .kept 34, .kept 35, .kept 36, .kept 38, .kept 39, .kept 40, .kept 41, .kept 43, .kept 44, .kept 45, .kept 46, .kept 47, .kept 48, .kept 49, .kept 54, .kept 55, .kept 57, .kept 58, .kept 59, .kept 60, .kept 61, .kept 62, .kept 63, .kept 64, .kept 65, .kept 66, .kept 67, .kept 68, .kept 71, .kept 74, .kept 75, .kept 80, .kept 83, .kept 84, .kept 87, .kept 88, .crossing 0 24, .crossing 3 30, .crossing 3 32, .crossing 3 37, .crossing 3 42, .crossing 3 50, .crossing 3 51, .crossing 4 30, .crossing 4 37, .crossing 4 56, .crossing 5 29, .crossing 5 30, .crossing 5 37, .crossing 5 52, .crossing 5 56, .crossing 5 70, .crossing 5 89, .crossing 6 32, .crossing 6 81, .crossing 7 23, .crossing 10 29, .crossing 10 30, .crossing 10 37, .crossing 11 23, .crossing 18 76, .crossing 25 24, .crossing 25 37, .crossing 28 29, .crossing 28 30, .crossing 28 31, .crossing 28 37, .crossing 28 56, .crossing 38 37, .crossing 43 37, .crossing 49 37, .crossing 49 51, .crossing 49 77, .crossing 60 37, .crossing 66 37, .crossing 71 69, .crossing 71 72, .crossing 71 73, .crossing 88 37, .crossing 88 76]

private def mask (p : Fin 91) : ℕ := maskTable.getD p.val 0

def plan : RayCutPlan 91 108 where
  kept p := kept.getD p.val 0
  crossing p k := edges.getD ((edgeIndex.getD (positiveIndex.getD p.val 0) #[]).getD
    (negativeIndex.getD k.val 0) 0) (.skip p)
  origin l := origin.getD l.val (.kept 0)

private abbrev old := lowerStage6.rays
private abbrev nextRows := lowerStage7.rays
private abbrev imposed := lowerStage6.imposed

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

private theorem crossing : ∀ p k, positive (old p 21) = true → negative (old k 21) = true →
    maskCrossing old nextRows imposed 21 mask p k (plan.crossing p k) := by
  apply checkRayBlocks
  intro k
  fin_cases k <;> decide +kernel

theorem valid : plan.Valid old nextRows imposed 21 := by
  obtain ⟨sep, cross⟩ := validateRayMasks plan mask oldSigns mask_eq separate crossing
  refine ⟨oldSigns, ?_, ?_, ?_, sep, ?_, cross, ?_⟩ <;> apply checkRayBlocks <;>
    intro k <;> fin_cases k <;> decide +kernel

end LowerCut6

end MOC.RayCoefficients

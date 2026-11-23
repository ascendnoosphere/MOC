import MOC.WeightedDiamondLowerRows
import MOC.WeightedDiamondPackedCut

/-! Add the inequality at permutation 11 to the order-four ray census. -/

namespace MOC.RayCoefficients

namespace LowerCut5

set_option maxRecDepth 32000
set_option maxHeartbeats 60000000

private def positiveIndex : Array ℕ :=
  #[0, 1, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 5, 0, 0, 0, 0, 6, 7, 8, 0, 9, 0, 0, 0, 0, 10, 0, 0, 0, 11, 0, 0, 12, 0, 0, 0, 13, 0, 0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 16, 17, 0, 0, 18, 0, 0, 0, 19, 20, 21, 22, 0, 0, 23, 0, 0, 0, 0, 24, 0, 25]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 5, 0, 0, 0, 0, 6, 7, 0, 8, 0, 0, 0, 0, 9, 10, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 13, 14, 15, 0, 16, 0]

private def edges : Array (Crossing 71 91) :=
  #[.keep 54 [1], .skip 2, .keep 55 [1, 2], .skip 8, .skip 1, .skip 24, .keep 56 [1], .skip 13, .skip 0, .skip 25, .skip 26, .keep 57 [1], .skip 4, .skip 6, .keep 58 [1], .keep 59 [1], .skip 9, .keep 60 [1], .keep 61 [1], .keep 62 [1], .keep 63 [1], .skip 20, .skip 15, .skip 39, .skip 40, .keep 64 [0, 1], .keep 65 [1], .skip 22, .skip 28, .skip 29, .keep 66 [1], .skip 14, .skip 31, .skip 5, .keep 67 [0, 1], .keep 68 [1], .keep 69 [1], .keep 70 [1], .keep 71 [1], .keep 72 [1], .keep 73 [1, 2], .skip 32, .keep 74 [1], .keep 75 [1, 2], .skip 21, .keep 76 [1], .keep 77 [1], .skip 18, .keep 78 [0, 1], .keep 79 [1, 3], .skip 11, .skip 27, .skip 10, .skip 34, .skip 38, .keep 80 [0, 1, 2], .keep 81 [1, 2], .keep 82 [1], .skip 35, .skip 36, .skip 7, .skip 37, .skip 12, .keep 83 [1, 4, 4], .skip 23, .skip 45, .skip 47, .skip 48, .skip 49, .keep 84 [0, 1, 4, 4], .keep 85 [1, 4, 4], .keep 86 [1, 4, 4], .skip 16, .skip 52, .skip 56, .skip 46, .keep 87 [2, 7, 6], .skip 19, .skip 17, .keep 88 [0, 1], .skip 53, .skip 62, .keep 89 [1, 2], .skip 67, .skip 44, .skip 68, .keep 90 [1, 5, 6]]

private def edgeIndex : Array (Array ℕ) :=
  #[
    #[0, 1, 2, 1, 1, 1, 3, 3, 3, 4, 4, 4, 5, 5, 4, 4, 4],
    #[6, 7, 8, 8, 1, 1, 3, 3, 3, 7, 7, 7, 8, 8, 9, 9, 10],
    #[11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 13, 13, 23, 24, 24],
    #[25, 12, 13, 1, 1, 1, 3, 3, 3, 7, 7, 7, 13, 13, 9, 9, 10],
    #[26, 27, 8, 28, 29, 27, 30, 31, 27, 32, 32, 27, 33, 33, 33, 33, 31],
    #[34, 35, 1, 1, 1, 1, 3, 3, 3, 7, 7, 7, 1, 1, 33, 33, 10],
    #[36, 21, 8, 21, 37, 21, 38, 39, 40, 21, 21, 21, 28, 29, 32, 41, 41],
    #[42, 33, 43, 1, 1, 1, 3, 3, 3, 7, 7, 3, 5, 5, 9, 9, 44],
    #[45, 3, 8, 8, 8, 8, 3, 3, 3, 4, 4, 4, 8, 8, 4, 4, 4],
    #[46, 3, 1, 1, 1, 1, 3, 3, 3, 7, 7, 3, 1, 1, 7, 47, 10],
    #[48, 3, 1, 1, 1, 1, 3, 3, 3, 7, 7, 3, 1, 1, 7, 9, 49],
    #[8, 50, 8, 28, 29, 51, 28, 31, 51, 28, 28, 51, 52, 52, 52, 52, 31],
    #[4, 27, 8, 28, 41, 51, 32, 41, 53, 32, 41, 53, 52, 52, 31, 41, 41],
    #[1, 54, 1, 55, 56, 57, 58, 59, 54, 58, 59, 54, 52, 52, 52, 52, 59],
    #[60, 12, 13, 13, 61, 16, 31, 24, 22, 23, 24, 22, 13, 13, 31, 24, 24],
    #[12, 12, 33, 13, 13, 12, 12, 12, 12, 23, 23, 12, 33, 33, 33, 33, 31],
    #[62, 63, 1, 61, 61, 64, 65, 65, 64, 66, 67, 64, 33, 33, 33, 33, 67],
    #[12, 12, 1, 13, 13, 12, 12, 12, 12, 23, 23, 12, 33, 33, 33, 33, 31],
    #[7, 68, 1, 61, 61, 61, 65, 65, 65, 69, 70, 71, 52, 52, 31, 72, 73],
    #[47, 33, 52, 52, 52, 52, 65, 65, 65, 72, 72, 72, 52, 52, 31, 74, 74],
    #[47, 33, 52, 52, 52, 52, 75, 75, 76, 72, 72, 72, 52, 52, 72, 72, 72],
    #[77, 50, 8, 28, 31, 78, 79, 31, 78, 32, 31, 78, 31, 31, 31, 31, 31],
    #[77, 50, 8, 28, 31, 78, 65, 31, 78, 32, 31, 78, 52, 52, 31, 31, 31],
    #[44, 21, 1, 61, 61, 21, 65, 65, 21, 80, 21, 21, 52, 52, 31, 74, 81],
    #[9, 33, 52, 52, 52, 52, 31, 65, 72, 31, 72, 72, 52, 52, 31, 82, 83],
    #[10, 84, 1, 31, 61, 59, 31, 65, 84, 31, 80, 84, 52, 52, 31, 85, 86]]

private def maskTable : Array ℕ :=
  #[17441, 1072, 17664, 33280, 565248, 786432, 49155, 33810, 9344, 61440, 282624, 524385, 525632, 1300, 195, 45076, 266260, 552, 263808, 1761, 780, 1984, 532520, 532748, 279683, 263314, 1490, 28712, 16421, 16427, 20577, 53, 58, 4208, 12348, 16645, 16650, 20800, 28940, 32791, 32794, 36946, 557139, 8325, 8330, 12480, 12428, 524613, 524618, 528704, 557379, 277, 286, 4436, 12572, 262789, 262794, 266944, 266892, 741, 4833, 965, 970, 5056, 278663, 278667, 262295, 262298, 266450, 474, 4562]

private def kept : Array (Fin 91) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 0, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 0, 0, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 32, 0, 33, 34, 35, 36, 0, 0, 37, 0, 38, 39, 40, 41, 0, 0, 42, 0, 43, 44, 45, 46, 47, 48, 49, 50, 51, 0, 0, 0, 0, 52, 0, 53]

private def origin : Array (RayOrigin 71) :=
  #[.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 9, .kept 10, .kept 11, .kept 12, .kept 13, .kept 14, .kept 15, .kept 16, .kept 17, .kept 18, .kept 19, .kept 20, .kept 21, .kept 22, .kept 25, .kept 26, .kept 27, .kept 28, .kept 29, .kept 30, .kept 31, .kept 32, .kept 33, .kept 34, .kept 37, .kept 39, .kept 40, .kept 41, .kept 42, .kept 45, .kept 47, .kept 48, .kept 49, .kept 50, .kept 53, .kept 55, .kept 56, .kept 57, .kept 58, .kept 59, .kept 60, .kept 61, .kept 62, .kept 63, .kept 68, .kept 70, .crossing 0 8, .crossing 0 24, .crossing 1 8, .crossing 3 8, .crossing 3 35, .crossing 3 36, .crossing 3 43, .crossing 3 44, .crossing 3 46, .crossing 3 51, .crossing 7 8, .crossing 11 8, .crossing 11 43, .crossing 12 8, .crossing 12 23, .crossing 17 8, .crossing 17 36, .crossing 17 43, .crossing 17 44, .crossing 17 46, .crossing 18 8, .crossing 18 24, .crossing 19 8, .crossing 21 8, .crossing 26 8, .crossing 26 69, .crossing 37 35, .crossing 37 36, .crossing 37 38, .crossing 49 23, .crossing 53 51, .crossing 53 52, .crossing 53 54, .crossing 58 46, .crossing 59 43, .crossing 68 67, .crossing 70 69]

private def mask (p : Fin 71) : ℕ := maskTable.getD p.val 0

def plan : RayCutPlan 71 91 where
  kept p := kept.getD p.val 0
  crossing p k := edges.getD ((edgeIndex.getD (positiveIndex.getD p.val 0) #[]).getD
    (negativeIndex.getD k.val 0) 0) (.skip p)
  origin l := origin.getD l.val (.kept 0)

private abbrev old := lowerStage5.rays
private abbrev nextRows := lowerStage6.rays
private abbrev imposed := lowerStage5.imposed

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

private theorem crossing : ∀ p k, positive (old p 11) = true → negative (old k 11) = true →
    maskCrossing old nextRows imposed 11 mask p k (plan.crossing p k) := by
  apply checkRayBlocks
  intro k
  fin_cases k <;> decide +kernel

theorem valid : plan.Valid old nextRows imposed 11 := by
  obtain ⟨sep, cross⟩ := validateRayMasks plan mask oldSigns mask_eq separate crossing
  refine ⟨oldSigns, ?_, ?_, ?_, sep, ?_, cross, ?_⟩ <;> apply checkRayBlocks <;>
    intro k <;> fin_cases k <;> decide +kernel

end LowerCut5

end MOC.RayCoefficients

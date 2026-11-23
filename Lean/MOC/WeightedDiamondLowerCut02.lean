import MOC.WeightedDiamondLowerRows
import MOC.WeightedDiamondPackedCut

/-! Add the inequality at permutation 14 to the order-four ray census. -/

namespace MOC.RayCoefficients

namespace LowerCut2

set_option maxRecDepth 32000
set_option maxHeartbeats 60000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 4]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 3, 0, 0, 0, 0, 0]

private def edges : Array (Crossing 20 28) :=
  #[.keep 16 [1, 4, 4], .skip 1, .skip 2, .keep 17 [1], .keep 18 [1], .keep 19 [1], .keep 20 [1], .keep 21 [1], .keep 22 [1], .skip 9, .keep 23 [1], .skip 6, .keep 24 [1], .keep 25 [1], .skip 15, .skip 7, .keep 26 [1], .keep 27 [1, 4, 4]]

private def edgeIndex : Array (Array ℕ) :=
  #[
    #[0, 1, 2, 3],
    #[4, 5, 6, 7],
    #[8, 9, 9, 10],
    #[11, 12, 13, 14],
    #[15, 16, 17, 14]]

private def maskTable : Array ℕ :=
  #[33, 40, 48, 524352, 256, 512, 532480, 786432, 3, 5, 10, 12, 18, 20, 192, 4160, 8320, 12288, 262272, 266240]

private def separators : Array ℕ :=
  #[204459774230359580886565027840, 204459774230359580886565030915, 204459774230359580886565027972, 776947142075366406908311260787, 327135638768575329418495664392, 368027593614647245595515069737, 776947142075366407142387404403, 776947142075366406715038322291, 40891954844917867673287689249, 81783909618284728097005701186, 122675864538140313238180564003, 122675864538106536240975285315, 163567819268995514248567325828, 163567819234407869110361917572, 285004526693257073315238092007, 252786403505521617059640127884, 531347583205913911317811869101, 531091290932155609938142868909, 278017372693703789101001034322, 15574084365203170994185390674]

private def kept : Array (Fin 28) :=
  #[0, 1, 2, 0, 3, 4, 5, 6, 7, 8, 9, 0, 10, 0, 0, 11, 12, 13, 14, 15]

private def origin : Array (RayOrigin 20) :=
  #[.kept 0, .kept 1, .kept 2, .kept 4, .kept 5, .kept 6, .kept 7, .kept 8, .kept 9, .kept 10, .kept 12, .kept 15, .kept 16, .kept 17, .kept 18, .kept 19, .crossing 0 3, .crossing 0 14, .crossing 4 3, .crossing 4 11, .crossing 4 13, .crossing 4 14, .crossing 8 3, .crossing 8 14, .crossing 17 11, .crossing 17 13, .crossing 19 11, .crossing 19 13]

private def mask (p : Fin 20) : ℕ := maskTable.getD p.val 0

private def separator (p k : Fin 20) : Fin 24 :=
  Fin.ofNat' 24 (((separators.getD p.val 0) >>> (5 * k.val)) % 32)

local instance : NeZero lowerStage2.size := ⟨by decide +kernel⟩
local instance : NeZero lowerStage3.size := ⟨by decide +kernel⟩

def plan : RayCutPlan 20 28 where
  kept p := kept.getD p.val 0
  crossing p k := edges.getD ((edgeIndex.getD (positiveIndex.getD p.val 0) #[]).getD
    (negativeIndex.getD k.val 0) 0) (.skip p)
  origin l := origin.getD l.val (.kept 0)

private abbrev old : Fin 20 → Row := lowerStage2.rays
private abbrev nextRows : Fin 28 → Row := lowerStage3.rays
private abbrev imposed := lowerStage2.imposed

private theorem oldSigns : ∀ p i, i ∈ imposed → zero (old p i) = true ∨ positive (old p i) = true := by
  apply checkRayBlocks (n := 20)
  intro k
  fin_cases k <;> decide +kernel

private theorem mask_eq : ∀ p i, (mask p).testBit i.val =
    (decide (i ∈ imposed) && positive (old p i)) := by
  apply checkRayBlocks (n := 20)
  intro k
  fin_cases k <;> decide +kernel

private theorem separate : ∀ p k, p ≠ k → let i := separator p k
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply checkRayBlocks (n := 20)
  intro k
  fin_cases k <;> decide +kernel

private theorem crossing : ∀ p k, positive (old p 14) = true → negative (old k 14) = true →
    maskCrossing old nextRows imposed 14 mask p k (plan.crossing p k) := by
  apply checkRayBlocks (n := 20)
  intro k
  fin_cases k <;> decide +kernel

theorem valid : plan.Valid old nextRows imposed 14 := by
  obtain ⟨sep, cross⟩ := validateRayMasks plan mask separator oldSigns mask_eq separate crossing
  refine ⟨oldSigns, ?_, ?_, ?_, sep, ?_, cross, ?_⟩ <;> apply checkRayBlocks <;>
    intro k <;> fin_cases k <;> decide +kernel

end LowerCut2

end MOC.RayCoefficients

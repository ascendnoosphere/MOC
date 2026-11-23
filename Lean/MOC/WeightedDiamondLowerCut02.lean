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

private def columns : Array ℕ :=
  #[769, 5376, 10752, 3074, 12292, 7, 49160, 344064, 16, 32, 0, 0, 688128, 196672, 0, 0, 0, 0, 786560, 200, 0, 0, 0, 0]

private def zeros : Array (List (Fin 24)) :=
  #[[1, 2, 6, 13, 18, 3, 4, 8, 9], [0, 4, 6, 13, 18, 1, 2, 8, 9], [0, 3, 6, 13, 18, 1, 2, 8, 9], [0, 3, 4, 7, 12, 8, 9, 13, 18], [0, 3, 4, 6, 13, 18, 9], [0, 3, 4, 6, 13, 18, 8], [0, 3, 4, 6, 18, 7, 8, 9, 12], [0, 3, 4, 6, 13, 7, 8, 9, 12], [2, 5, 6, 13, 18, 3, 4, 8, 9], [1, 5, 6, 13, 18, 3, 4, 8, 9], [0, 4, 6, 13, 18, 2, 5, 8, 9], [0, 4, 6, 13, 18, 1, 5, 8, 9], [0, 3, 6, 13, 18, 2, 5, 8, 9], [0, 3, 6, 13, 18, 1, 5, 8, 9], [0, 3, 4, 12, 19, 8, 9, 13, 18], [0, 3, 4, 7, 19, 8, 9, 13, 18], [0, 3, 4, 6, 18, 8, 9, 12, 19], [0, 3, 4, 6, 18, 7, 8, 9, 19], [0, 3, 4, 6, 13, 8, 9, 12, 19], [0, 3, 4, 6, 13, 7, 8, 9, 19]]

private def positiveRays : Array (Fin 20) :=
  #[0, 4, 8, 17, 19]

private def negativeRays : Array (Fin 20) :=
  #[3, 11, 13, 14]

private def kept : Array (Fin 28) :=
  #[0, 1, 2, 0, 3, 4, 5, 6, 7, 8, 9, 0, 10, 0, 0, 11, 12, 13, 14, 15]

private def origin : Array (RayOrigin 20) :=
  #[.kept 0, .kept 1, .kept 2, .kept 4, .kept 5, .kept 6, .kept 7, .kept 8, .kept 9, .kept 10, .kept 12, .kept 15, .kept 16, .kept 17, .kept 18, .kept 19, .crossing 0 3, .crossing 0 14, .crossing 4 3, .crossing 4 11, .crossing 4 13, .crossing 4 14, .crossing 8 3, .crossing 8 14, .crossing 17 11, .crossing 17 13, .crossing 19 11, .crossing 19 13]

private def mask (p : Fin 20) : ℕ := maskTable.getD p.val 0

private def column (i : Fin 24) : ℕ := columns.getD i.val 0
private def zeroCoords (k : Fin 20) : List (Fin 24) := zeros.getD k.val []
private def positiveRay (i : Fin 5) : Fin 20 := positiveRays.getD i.val 0
private def negativeRay (i : Fin 4) : Fin 20 := negativeRays.getD i.val 0
private def positiveOf (p : Fin 20) : Fin 5 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 20) : Fin 4 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

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
  apply IntegerRayCut.blocks (n := 20)
  intro k
  fin_cases k <;> decide +kernel

private theorem mask_eq : ∀ p i, (mask p).testBit i.val =
    (decide (i ∈ imposed) && positive (old p i)) := by
  apply IntegerRayCut.blocks (n := 20)
  intro k
  fin_cases k <;> decide +kernel

private theorem separate : ∀ p k, p ≠ k → ∃ i : Fin 24,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply IntegerRayCut.separates_of_cover mask column zeroCoords 1048575 <;>
    apply IntegerRayCut.blocks <;> intro k <;> fin_cases k <;> decide +kernel

private theorem crossing (p k : Fin 20) (hp : positive (old p 14) = true)
    (hk : negative (old k 14) = true) :
    maskCrossing old nextRows imposed 14 mask p k (plan.crossing p k) := by
  have hitP : ∀ p, positive (old p 14) = true → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, negative (old k 14) = true → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, maskCrossing old nextRows imposed 14 mask (positiveRay u) (negativeRay v)
      (plan.crossing (positiveRay u) (negativeRay v)) := by
    apply IntegerRayCut.blocks
    intro k
    fin_cases k <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

theorem valid : plan.Valid old nextRows imposed 14 := by
  obtain ⟨sep, cross⟩ := validateRayMasks plan mask oldSigns mask_eq separate crossing
  refine ⟨oldSigns, ?_, ?_, ?_, sep, ?_, cross, ?_⟩ <;> apply IntegerRayCut.blocks <;>
    intro k <;> fin_cases k <;> decide +kernel

end LowerCut2

end MOC.RayCoefficients

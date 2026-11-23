import MOC.WeightedDiamondLowerRows
import MOC.WeightedDiamondPackedCut

/-! Add the inequality at permutation 15 to the order-four ray census. -/

namespace MOC.RayCoefficients

namespace LowerCut3

set_option maxRecDepth 32000
set_option maxHeartbeats 60000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 3, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 6, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 3, 0, 4, 0, 0, 0, 0, 5, 0]

private def edges : Array (Crossing 28 34) :=
  #[.keep 22 [1], .keep 23 [1], .keep 24 [1], .keep 25 [1], .keep 26 [1], .keep 27 [1], .keep 28 [1, 4, 4], .skip 6, .skip 12, .keep 29 [1], .skip 0, .keep 30 [1], .skip 3, .skip 8, .skip 2, .keep 31 [1, 4, 4], .skip 9, .keep 32 [1], .keep 33 [1], .skip 15, .skip 16, .skip 18, .skip 20, .skip 11, .skip 24]

private def edgeIndex : Array (Array ℕ) :=
  #[
    #[0, 1, 2, 3, 4, 5],
    #[6, 7, 8, 9, 8, 7],
    #[10, 11, 10, 12, 12, 13],
    #[14, 15, 14, 16, 17, 16],
    #[18, 8, 10, 12, 12, 19],
    #[16, 7, 20, 13, 21, 7],
    #[14, 8, 14, 22, 23, 24]]

private def maskTable : Array ℕ :=
  #[16417, 40, 48, 16640, 512, 532480, 786432, 16387, 5, 10, 18, 4160, 8320, 28672, 262272, 282624, 524385, 225, 524608, 268, 276, 448, 524355, 195, 12300, 12308, 266252, 266260]

private def columns : Array ℕ :=
  #[12779905, 12584576, 253231360, 84410882, 168821764, 196615, 15140864, 10637312, 3932168, 16, 0, 0, 251701248, 50343968, 41097, 0, 0, 0, 201375808, 4522080, 0, 0, 0, 0]

private def zeros : Array (List (Fin 24)) :=
  #[[2, 6, 1, 13, 18, 3, 4, 8, 9], [0, 12, 8, 1, 7, 19, 4, 9], [0, 12, 8, 1, 7, 19, 3, 9], [0, 12, 3, 4, 7, 19, 9], [0, 12, 8, 1, 5, 7, 19], [0, 12, 8, 1, 5, 7, 9, 18], [0, 12, 8, 1, 5, 7, 9, 13], [2, 6, 5, 13, 18, 3, 4, 8, 9], [6, 12, 1, 5, 8, 7, 19, 9], [0, 12, 8, 4, 7, 19, 5, 9], [0, 12, 8, 3, 7, 19, 5, 9], [0, 2, 7, 14, 19, 1, 5, 9], [0, 12, 8, 1, 5, 18, 9, 19], [0, 2, 6, 18, 1, 5, 7, 8, 9, 19], [0, 12, 8, 1, 5, 13, 9, 19], [0, 2, 6, 13, 1, 5, 7, 8, 9, 19], [2, 1, 7, 14, 3, 4, 8, 9, 12, 13, 18], [2, 1, 14, 19, 3, 4, 8, 9, 12, 13, 18], [0, 12, 3, 4, 7, 9, 13, 14, 18], [0, 12, 4, 7, 19, 1, 5, 9, 14], [0, 12, 3, 7, 19, 1, 5, 9, 14], [0, 12, 3, 4, 19, 9, 13, 14, 18], [2, 5, 7, 14, 3, 4, 8, 9, 12, 13, 18], [2, 5, 14, 19, 3, 4, 8, 9, 12, 13, 18], [0, 4, 8, 18, 1, 5, 6, 7, 9, 14, 19], [0, 3, 8, 18, 1, 5, 6, 7, 9, 14, 19], [0, 4, 8, 13, 1, 5, 6, 7, 9, 14, 19], [0, 3, 8, 13, 1, 5, 6, 7, 9, 14, 19]]

private def positiveRays : Array (Fin 28) :=
  #[4, 5, 7, 10, 13, 22, 25]

private def negativeRays : Array (Fin 28) :=
  #[1, 14, 17, 19, 21, 26]

private def kept : Array (Fin 34) :=
  #[0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 13, 14, 0, 15, 0, 16, 0, 17, 18, 19, 20, 0, 21]

private def origin : Array (RayOrigin 28) :=
  #[.kept 0, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 8, .kept 9, .kept 10, .kept 11, .kept 12, .kept 13, .kept 15, .kept 16, .kept 18, .kept 20, .kept 22, .kept 23, .kept 24, .kept 25, .kept 27, .crossing 4 1, .crossing 4 14, .crossing 4 17, .crossing 4 19, .crossing 4 21, .crossing 4 26, .crossing 5 1, .crossing 5 19, .crossing 7 14, .crossing 10 14, .crossing 10 21, .crossing 13 1]

private def mask (p : Fin 28) : ℕ := maskTable.getD p.val 0

private def column (i : Fin 24) : ℕ := columns.getD i.val 0
private def zeroCoords (k : Fin 28) : List (Fin 24) := zeros.getD k.val []
private def positiveRay (i : Fin 7) : Fin 28 := positiveRays.getD i.val 0
private def negativeRay (i : Fin 6) : Fin 28 := negativeRays.getD i.val 0
private def positiveOf (p : Fin 28) : Fin 7 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 28) : Fin 6 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

local instance : NeZero lowerStage3.size := ⟨by decide +kernel⟩
local instance : NeZero lowerStage4.size := ⟨by decide +kernel⟩

def plan : RayCutPlan 28 34 where
  kept p := kept.getD p.val 0
  crossing p k := edges.getD ((edgeIndex.getD (positiveIndex.getD p.val 0) #[]).getD
    (negativeIndex.getD k.val 0) 0) (.skip p)
  origin l := origin.getD l.val (.kept 0)

private abbrev old : Fin 28 → Row := lowerStage3.rays
private abbrev nextRows : Fin 34 → Row := lowerStage4.rays
private abbrev imposed := lowerStage3.imposed

private theorem oldSigns : ∀ p i, i ∈ imposed → zero (old p i) = true ∨ positive (old p i) = true := by
  refine IntegerRayCut.blocks (n := 28)
    (P := fun p => ∀ i, i ∈ imposed → zero (old p i) = true ∨ positive (old p i) = true) ?_
  intro k
  fin_cases k <;> decide +kernel

private theorem mask_eq : ∀ p i, (mask p).testBit i.val =
    (decide (i ∈ imposed) && positive (old p i)) := by
  refine IntegerRayCut.blocks (n := 28) (P := fun p => ∀ i : Fin 24,
    (mask p).testBit i.val = (decide (i ∈ imposed) && positive (old p i))) ?_
  intro k
  fin_cases k <;> decide +kernel

private theorem separate : ∀ p k, p ≠ k → ∃ i : Fin 24,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply IntegerRayCut.separates_of_cover mask column zeroCoords 268435455 <;>
    apply IntegerRayCut.blocks <;> intro k <;> fin_cases k <;> decide +kernel

private theorem crossing (p k : Fin 28) (hp : positive (old p 15) = true)
    (hk : negative (old k 15) = true) :
    maskCrossing old nextRows imposed 15 mask p k (plan.crossing p k) := by
  have hitP : ∀ p, positive (old p 15) = true → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, negative (old k 15) = true → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, maskCrossing old nextRows imposed 15 mask (positiveRay u) (negativeRay v)
      (plan.crossing (positiveRay u) (negativeRay v)) := by
    apply IntegerRayCut.blocks
    intro k
    fin_cases k <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

theorem valid : plan.Valid old nextRows imposed 15 := by
  obtain ⟨sep, cross⟩ := validateRayMasks plan mask oldSigns mask_eq separate crossing
  refine ⟨oldSigns, ?_, ?_, ?_, sep, ?_, cross, ?_⟩ <;> apply IntegerRayCut.blocks <;>
    intro k <;> fin_cases k <;> decide +kernel

end LowerCut3

end MOC.RayCoefficients

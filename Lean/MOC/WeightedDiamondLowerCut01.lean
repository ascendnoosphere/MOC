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

private def columns : Array ℕ :=
  #[3073, 21504, 43008, 12290, 49156, 7, 8, 16, 32, 64, 0, 0, 128, 256, 0, 0, 0, 0, 512, 0, 0, 0, 0, 0]

private def zeros : Array (List (Fin 24)) :=
  #[[1, 2, 3, 4, 6, 7, 8, 9, 12, 13, 18], [0, 4, 1, 2, 6, 7, 8, 9, 12, 13, 18], [0, 3, 1, 2, 6, 7, 8, 9, 12, 13, 18], [0, 3, 4, 7, 8, 9, 12, 13, 18], [0, 3, 4, 6, 8, 9, 12, 13, 18], [0, 3, 4, 6, 7, 9, 12, 13, 18], [0, 3, 4, 6, 7, 8, 12, 13, 18], [0, 3, 4, 6, 7, 8, 9, 13, 18], [0, 3, 4, 6, 7, 8, 9, 12, 18], [0, 3, 4, 6, 7, 8, 9, 12, 13], [2, 5, 3, 4, 6, 7, 8, 9, 12, 13, 18], [1, 5, 3, 4, 6, 7, 8, 9, 12, 13, 18], [0, 4, 2, 5, 6, 7, 8, 9, 12, 13, 18], [0, 4, 1, 5, 6, 7, 8, 9, 12, 13, 18], [0, 3, 2, 5, 6, 7, 8, 9, 12, 13, 18], [0, 3, 1, 5, 6, 7, 8, 9, 12, 13, 18]]

private def positiveRays : Array (Fin 16) :=
  #[3, 8, 9]

private def negativeRays : Array (Fin 16) :=
  #[4, 7]

private def kept : Array (Fin 20) :=
  #[0, 1, 2, 3, 0, 4, 5, 0, 6, 7, 8, 9, 10, 11, 12, 13]

private def origin : Array (RayOrigin 16) :=
  #[.kept 0, .kept 1, .kept 2, .kept 3, .kept 5, .kept 6, .kept 8, .kept 9, .kept 10, .kept 11, .kept 12, .kept 13, .kept 14, .kept 15, .crossing 3 4, .crossing 3 7, .crossing 8 4, .crossing 8 7, .crossing 9 4, .crossing 9 7]

private def mask (p : Fin 16) : ℕ := maskTable.getD p.val 0

private def column (i : Fin 24) : ℕ := columns.getD i.val 0
private def zeroCoords (k : Fin 16) : List (Fin 24) := zeros.getD k.val []
private def positiveRay (i : Fin 3) : Fin 16 := positiveRays.getD i.val 0
private def negativeRay (i : Fin 2) : Fin 16 := negativeRays.getD i.val 0
private def positiveOf (p : Fin 16) : Fin 3 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 16) : Fin 2 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

local instance : NeZero lowerStage1.size := ⟨by decide +kernel⟩
local instance : NeZero lowerStage2.size := ⟨by decide +kernel⟩

def plan : RayCutPlan 16 20 where
  kept p := kept.getD p.val 0
  crossing p k := edges.getD ((edgeIndex.getD (positiveIndex.getD p.val 0) #[]).getD
    (negativeIndex.getD k.val 0) 0) (.skip p)
  origin l := origin.getD l.val (.kept 0)

private abbrev old : Fin 16 → Row := lowerStage1.rays
private abbrev nextRows : Fin 20 → Row := lowerStage2.rays
private abbrev imposed := lowerStage1.imposed

private theorem oldSigns : ∀ p i, i ∈ imposed → zero (old p i) = true ∨ positive (old p i) = true := by
  apply IntegerRayCut.blocks (n := 16)
  intro k
  fin_cases k <;> decide +kernel

private theorem mask_eq : ∀ p i, (mask p).testBit i.val =
    (decide (i ∈ imposed) && positive (old p i)) := by
  apply IntegerRayCut.blocks (n := 16)
  intro k
  fin_cases k <;> decide +kernel

private theorem separate : ∀ p k, p ≠ k → ∃ i : Fin 24,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply IntegerRayCut.separates_of_cover mask column zeroCoords 65535 <;>
    apply IntegerRayCut.blocks <;> intro k <;> fin_cases k <;> decide +kernel

private theorem crossing (p k : Fin 16) (hp : positive (old p 19) = true)
    (hk : negative (old k 19) = true) :
    maskCrossing old nextRows imposed 19 mask p k (plan.crossing p k) := by
  have hitP : ∀ p, positive (old p 19) = true → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, negative (old k 19) = true → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, maskCrossing old nextRows imposed 19 mask (positiveRay u) (negativeRay v)
      (plan.crossing (positiveRay u) (negativeRay v)) := by
    apply IntegerRayCut.blocks
    intro k
    fin_cases k <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

theorem valid : plan.Valid old nextRows imposed 19 := by
  obtain ⟨sep, cross⟩ := validateRayMasks plan mask oldSigns mask_eq separate crossing
  refine ⟨oldSigns, ?_, ?_, ?_, sep, ?_, cross, ?_⟩ <;> apply IntegerRayCut.blocks <;>
    intro k <;> fin_cases k <;> decide +kernel

end LowerCut1

end MOC.RayCoefficients

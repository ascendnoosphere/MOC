import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 9 in cut 19. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut19

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage18.count := ⟨by decide +kernel⟩
local instance : NeZero stage19.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 2, 3, 0, 0, 0, 0, 4, 5, 0, 6, 7, 8, 0, 9, 0, 0, 10, 11, 0, 0, 12, 13, 14, 0, 15, 16, 17, 18, 0, 0, 0, 19, 20, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0]

private def crossRows : Array ℕ :=
  #[2130433, 532621, 532625, 8688461, 266305, 532621, 532615, 532625, 532625, 532627, 65, 532631, 4161, 532611, 532609, 65, 532615, 532610, 532610, 532611, 65]

private def masks : Array ℕ :=
  #[272450, 4718610, 135556, 4582251977, 2155913216, 293995001, 271846505, 5452660736, 1080047814, 361209856, 338690084, 6511132982, 6444522753, 276798465, 4649360641, 5385952713, 294108617, 298816921, 7541359097, 1373634809, 5391850697, 6444289403, 6452446521, 7546312089, 1374393497, 4649320758, 7520230761, 7586462182, 7524162561, 4649323899, 4657743161, 7587077413, 7519346157, 1349524717, 2432205881, 369067065, 7536451049, 4582219259, 1350278277, 1440985220, 1373879501, 1374141641]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 0, 0, 0, 37]

private def mask (p : Fin 42) : ℕ := masks.getD p.val 0
private def keep (p : Fin 42) : Fin 38 := Fin.ofNat' 38 (kept.getD p.val 0)
private def cross (p k : Fin 42) : Choice 42 38 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (6 * negativeIndex.getD k.val 0)) &&& 63
  if x < 42 then .skip (Fin.ofNat' 42 x)
  else .edge (Fin.ofNat' 38 (x-42)) (((x-42) / 38+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 42) := #[0, 3, 5, 6, 11, 12, 14, 15, 16, 18, 21, 22, 25, 26, 27, 29, 30, 31, 32, 36, 37]
private def negativeRows : Array (Fin 42) := #[24, 38, 39, 40]
private def positiveRay (i : Fin 21) : Fin 42 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 4) : Fin 42 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 42) : Fin 21 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 42) : Fin 4 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 42) (hp : 0 < stage18.ray p 9)
    (hk : stage18.ray k 9 < 0) :
    CrossOK stage18 stage19 9 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage18.ray p 9 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage18.ray k 9 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage18 stage19 9 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[3848122921064, 138145696003, 1939345509636, 3570829066344, 190655105058, 274582998112, 3518320443753, 4342373384492, 214461569068, 0, 3848122134600, 3795613512009, 4344855654668, 3848424981265, 0, 4178294567448, 4367840440968, 4296636887596, 2441255055977, 468015282186, 549728582728, 4258948195648, 4183593459970, 3900934390320, 4090480280232, 0, 588041440896, 0, 4322398791272, 0, 4207417262464, 92826507280, 214730856584]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [5, 22, 13, 26, 31, 30, 2], [0, 26, 1, 2], [10, 26, 22, 31, 2, 13], [16, 31, 7, 1, 26], [0, 2, 13, 22], [0, 26, 18, 31, 4, 17], [0, 2, 1, 31, 30], [0, 13, 4, 30, 17], [0, 13, 17, 22, 30, 21], [3, 26, 22, 13, 2], [3, 26, 31, 2, 1], [3, 2, 22, 13, 31, 30], [20, 23, 22, 26, 2, 13], [20, 30, 4, 26, 31, 2, 1], [20, 30, 13, 5, 2, 1], [10, 26, 22, 18, 2, 13], [10, 26, 13, 8, 1], [20, 23, 1, 17, 26], [16, 21, 23, 2, 22, 13], [16, 6, 2, 22, 13], [20, 6, 28, 26, 2, 13, 1], [20, 6, 26, 8, 31, 1], [0, 13, 22, 31, 30, 21, 7], [28, 7, 4, 26, 13, 22, 17], [0, 17, 22, 18, 23, 4, 16, 28], [3, 26, 17, 13, 4], [12, 23, 2, 22, 31, 30, 21, 13], [12, 6, 31, 22, 2, 30, 13], [3, 17, 1, 22, 23, 28, 24], [16, 4, 13, 28, 17], [16, 31, 18, 4, 26, 13, 17], [16, 6, 2, 13, 1, 32], [12, 32, 6, 31, 2, 13, 1], [28, 19, 2, 23, 26, 22, 13, 17], [15, 30, 26, 22, 31, 2, 23, 21, 13], [3, 26, 18, 31, 1, 8], [0, 1, 18, 31, 5, 32, 8], [20, 18, 4, 26, 31, 1, 32, 8], [20, 4, 2, 32, 26, 31, 1, 8]]
private def zeros (k : Fin 42) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 4398046511103 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage18 stage19 9 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage18)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage19 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut19

import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 15 in cut 17. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut17

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage16.count := ⟨by decide +kernel⟩
local instance : NeZero stage17.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 3, 4, 5, 6, 0, 0, 7, 8, 0, 0, 0, 0, 0, 9, 10, 11, 0, 12, 0, 13, 0, 0, 14, 15, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0]

private def crossRows : Array ℕ :=
  #[8606875921, 86033563648, 0, 4311810305, 8606843665, 4311810305, 8606843651, 0, 4311810305, 47261746452, 4311810305, 4311810305, 30081680152, 4311810305, 8607040773, 30081679879, 17297309696, 4311810305, 17314086912, 4311810305, 4311810305]

private def masks : Array ℕ :=
  #[272450, 4718610, 135300, 4582218953, 2155880448, 293994745, 271846505, 5452660736, 1080047814, 361177088, 338690084, 6511132726, 1350114305, 6444489729, 276765697, 4649327617, 5385750779, 5385952457, 294075593, 298783897, 7541358841, 1373634809, 5391850697, 4582149371, 6444289147, 6452413497, 7546279065, 1374360729, 4649320502, 7520197737, 7586461926, 7524129793, 4649257215, 4649323643, 4657710137, 7587044389, 7519345901, 1349524717, 1440817152, 1442382905, 1373715657, 2432173113, 369034297, 5391784191, 7603230975, 7536450793]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 16, 17, 18, 19, 20, 21, 0, 22, 23, 24, 25, 26, 27, 28, 29, 0, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 0, 0, 40]

private def mask (p : Fin 46) : ℕ := masks.getD p.val 0
private def keep (p : Fin 46) : Fin 42 := Fin.ofNat' 42 (kept.getD p.val 0)
private def cross (p k : Fin 46) : Choice 46 42 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 46 then .skip (Fin.ofNat' 46 x)
  else .edge (Fin.ofNat' 42 (x-46)) (((x-46) / 42+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 46) := #[3, 4, 9, 12, 13, 14, 15, 18, 19, 25, 26, 27, 29, 31, 34, 35, 38, 39, 40, 41, 42]
private def negativeRows : Array (Fin 46) := #[16, 23, 32, 43, 44]
private def positiveRay (i : Fin 21) : Fin 46 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 5) : Fin 46 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 46) : Fin 21 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 46) : Fin 5 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 46) (hp : 0 < stage16.ray p 15)
    (hk : stage16.ray k 15 < 0) :
    CrossOK stage16 stage17 15 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage16.ray p 15 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage16.ray k 15 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage16 stage17 15 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[70092524089448, 26402531379459, 26634434383108, 70056016805992, 33565701638178, 68992000658528, 62892849693033, 62883907961132, 0, 0, 43699946844232, 62929353830729, 62916645548300, 1375463539473, 0, 0, 41569852781192, 4428590408236, 39613314884201, 7214463514634, 60198051970120, 70338283066688, 17457102737666, 8538633798192, 67925394293416, 0, 22880632999552, 0, 8689132820072, 0, 63741281636736, 55082537199632, 61709952985224]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [5, 22, 13, 26, 31, 30, 2], [0, 26, 1, 2], [10, 1, 26, 31, 22, 2], [24, 31, 22, 2, 13], [0, 2, 13, 22], [0, 26, 18, 31, 4, 17], [0, 2, 22, 31, 30, 1], [0, 13, 4, 30, 17], [0, 13, 17, 22, 30, 21], [3, 26, 18, 31, 2, 4], [3, 26, 22, 13, 2], [3, 26, 31, 1, 30, 2], [3, 21, 1, 31, 30, 2, 23], [10, 26, 22, 23, 2, 13], [20, 23, 1, 26, 22, 2], [20, 30, 4, 26, 31, 2, 1], [20, 30, 13, 5, 2, 1], [10, 1, 28, 26, 2, 13], [10, 1, 26, 31, 17], [20, 23, 1, 17, 26], [16, 2, 23, 22, 31, 30, 21, 13], [24, 21, 2, 23, 22, 13, 17], [11, 24, 2, 22, 13], [20, 6, 28, 26, 2, 13, 1], [20, 6, 26, 31, 18, 2, 1], [0, 13, 22, 31, 30, 21, 7], [24, 2, 22, 23, 1, 17, 28], [0, 16, 22, 18, 23, 4, 17, 28], [3, 26, 18, 2, 23, 4, 28], [10, 30, 23, 22, 31, 21, 13, 16, 12], [12, 23, 2, 30, 22, 31, 21, 13, 7], [11, 22, 31, 2, 30, 13, 6], [3, 28, 1, 17, 22, 23, 24], [24, 19, 13, 28, 17], [24, 31, 18, 1, 26, 17, 16], [0, 2, 18, 31, 4, 32], [11, 17, 31, 2, 13, 1, 6, 32], [20, 4, 18, 26, 2, 31, 32], [11, 24, 2, 13, 1, 32], [11, 30, 31, 2, 7, 13, 1, 32], [10, 26, 23, 18, 13, 17, 19], [10, 28, 13, 22, 18, 23, 17, 16, 19], [28, 4, 2, 19, 13, 26, 22, 17]]
private def zeros (k : Fin 46) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 70368744177663 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage16 stage17 15 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage16)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage17 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut17

import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 8 in cut 18. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut18

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage17.count := ⟨by decide +kernel⟩
local instance : NeZero stage18.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 4, 0, 5, 6, 7, 8, 9, 0, 0, 10, 11, 12, 0, 13, 14, 15, 0, 16, 17, 18, 19, 0, 0, 0, 0, 0, 0, 20, 21]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[172140752, 25248654, 35980422, 2113665, 6406670, 6407047, 35701635, 262227086, 36062350, 8503828, 16385, 8503837, 8503833, 16513, 8487430, 8405512, 16385, 6407047, 8503818, 8503837, 8487430, 16385]

private def masks : Array ℕ :=
  #[272450, 4718610, 135300, 4582251721, 2155913216, 293994745, 271846505, 5452660736, 1080047814, 361209856, 338690084, 6511132726, 1350147073, 6444522497, 276798465, 4649360385, 5385952457, 294108361, 298816665, 7541358841, 1373634809, 5391850697, 6444289147, 6452446265, 7546311833, 1374393497, 4649320502, 7520230505, 7586461926, 7524162561, 4649323643, 4657742905, 7587077157, 7519345901, 1349524717, 1440849920, 1442415673, 1373748425, 2432205881, 369067065, 7536450793, 4582219003]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 0, 0, 0, 34, 35, 36, 37]

private def mask (p : Fin 42) : ℕ := masks.getD p.val 0
private def keep (p : Fin 42) : Fin 42 := Fin.ofNat' 42 (kept.getD p.val 0)
private def cross (p k : Fin 42) : Choice 42 42 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (7 * negativeIndex.getD k.val 0)) &&& 127
  if x < 42 then .skip (Fin.ofNat' 42 x)
  else .edge (Fin.ofNat' 42 (x-42)) (((x-42) / 42+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 42) := #[2, 3, 5, 11, 13, 15, 16, 17, 18, 19, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 40, 41]
private def negativeRows : Array (Fin 42) := #[12, 35, 36, 37]
private def positiveRay (i : Fin 22) : Fin 42 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 4) : Fin 42 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 42) : Fin 22 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 42) : Fin 4 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 42) (hp : 0 < stage17.ray p 8)
    (hk : stage17.ray k 8 < 0) :
    CrossOK stage17 stage18 8 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage17.ray p 8 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage17.ray k 8 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage17 stage18 8 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[4363351224424, 2200436738307, 30400318724, 4358519324776, 3095729539106, 4225657998432, 3463228096873, 3462066536748, 0, 0, 4363349651528, 3468058423625, 3467031081228, 172067259153, 0, 1072324604440, 4097116205704, 2752118252076, 3851717960297, 3100694083594, 4226193357896, 2195704534336, 1082922389762, 1067360059952, 4092151693992, 0, 660686802560, 0, 3284678399592, 0, 1371088163200, 1388243855376, 3315679733896]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [5, 22, 13, 26, 31, 30, 2], [0, 26, 1, 2], [10, 26, 22, 31, 2, 13], [16, 31, 7, 1, 26], [0, 2, 13, 22], [0, 26, 18, 31, 4, 17], [0, 2, 22, 31, 30, 1], [0, 13, 4, 30, 17], [0, 13, 17, 22, 30, 21], [3, 26, 18, 31, 2, 4], [3, 26, 22, 13, 2], [3, 26, 31, 1, 30, 2], [3, 21, 1, 31, 30, 2, 23], [20, 23, 22, 26, 2, 13], [20, 30, 4, 26, 31, 2, 1], [20, 30, 13, 5, 2, 1], [10, 26, 22, 18, 2, 13], [10, 26, 13, 17, 31, 1], [20, 23, 1, 17, 26], [16, 21, 23, 2, 22, 13], [16, 6, 2, 22, 13], [20, 6, 28, 26, 2, 13, 1], [20, 6, 26, 31, 18, 2, 1], [0, 13, 22, 31, 30, 21, 7], [28, 7, 4, 26, 13, 22, 17], [0, 16, 22, 18, 23, 4, 17, 28], [3, 26, 18, 2, 23, 4, 28], [12, 23, 2, 22, 31, 30, 21, 13], [12, 21, 1, 31, 30, 13, 6], [3, 28, 1, 17, 22, 23, 24], [16, 4, 13, 28, 17], [16, 31, 18, 4, 26, 13, 17], [0, 2, 18, 31, 4, 32], [12, 18, 31, 2, 13, 1, 6, 32], [20, 17, 4, 26, 1, 31, 32], [16, 6, 2, 13, 1, 32], [12, 32, 13, 6, 31, 30, 2, 1], [28, 19, 2, 23, 26, 22, 13, 17], [15, 30, 26, 22, 31, 2, 23, 21, 13]]
private def zeros (k : Fin 42) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 4398046511103 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage17 stage18 8 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage17)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage18 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut18

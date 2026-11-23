import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 12 in cut 12. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut12

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage11.count := ⟨by decide +kernel⟩
local instance : NeZero stage12.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 4, 5, 6, 7, 8, 0, 9, 10, 11, 0, 0, 12, 13, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 0, 17, 18, 19]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[105579071364958, 6622940694032, 16777472, 8826292340737, 17622502739984, 17622519582209, 161658526174866, 12124877490951, 12124877556481, 3311470314243, 3311470314240, 17605322804737, 2246453168907, 3328717555463, 3328734201857, 8809112340481, 8809112340481, 7726763869959, 16778240, 8826292275201]

private def masks : Array ℕ :=
  #[270402, 4194322, 131204, 269944009, 2155880448, 283123712, 277217529, 271844457, 1140916224, 1080041670, 344399872, 338690084, 2215641142, 1349583873, 2148992001, 276235265, 337052673, 2150630437, 275776549, 1074004219, 1074201801, 277292233, 281478297, 3229614329, 2428633273, 1075839213, 1076167913, 1352933609, 279322857, 1356857593, 283246777, 1352925433, 1080100041, 269878523, 336855163, 2492465209, 347349097, 351273017, 347340921, 2148795515, 2156921913, 284165177, 348586169, 345440313, 3234006169, 1357055129, 337051702, 3224700009, 3291488486, 3228632065]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 0, 0, 0, 0, 0, 34, 35, 36, 37, 0, 38, 39, 40, 41, 42, 43]

private def mask (p : Fin 50) : ℕ := masks.getD p.val 0
private def keep (p : Fin 50) : Fin 49 := Fin.ofNat' 49 (kept.getD p.val 0)
private def cross (p k : Fin 50) : Choice 50 49 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 50 then .skip (Fin.ofNat' 50 x)
  else .edge (Fin.ofNat' 49 (x-50)) (((x-50) / 49+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 50) := #[2, 3, 9, 13, 14, 15, 16, 17, 18, 20, 21, 22, 25, 26, 32, 44, 45, 47, 48, 49]
private def negativeRows : Array (Fin 50) := #[34, 35, 36, 37, 38, 43]
private def positiveRay (i : Fin 20) : Fin 50 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 6) : Fin 50 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 50) : Fin 20 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 50) : Fin 6 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 50) (hp : 0 < stage11.ray p 12)
    (hk : stage11.ray k 12 < 0) :
    CrossOK stage11 stage12 12 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage11.ray p 12 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage11.ray k 12 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage11 stage12 12 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[774056185946312, 352419247034883, 351843754842628, 211106232008904, 140663966928962, 510169092856000, 423139082765001, 338666760700492, 0, 0, 760325250474120, 0, 0, 281544100939313, 0, 0, 840031253161224, 136349398189132, 225222120293577, 0, 1068716712786056, 1023035406985888, 622466947129890, 69788820833392, 0, 0, 365570436439296, 0, 121491629124840, 0, 1037946200793856, 1004438257029136, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [5, 22, 13, 26, 31, 30, 2], [0, 26, 22, 18, 2], [0, 26, 1, 31, 2], [21, 16, 31, 1, 2], [23, 16, 1, 2], [0, 2, 13, 22], [0, 26, 23, 18, 4, 17], [0, 2, 22, 31, 30, 1], [0, 13, 4, 30, 17], [0, 13, 17, 22, 30, 21], [3, 2, 18, 31, 26, 23, 4], [3, 21, 26, 13, 22, 2], [3, 2, 13, 30, 26, 31, 4], [3, 21, 1, 31, 30, 2, 23], [3, 16, 13, 26, 22, 17], [3, 16, 13, 26, 31, 4, 17], [28, 31, 21, 17, 26, 22, 13], [5, 22, 13, 20, 26, 2], [5, 22, 26, 31, 30, 2, 1, 20], [5, 30, 13, 20, 2, 1], [28, 10, 1, 2, 26, 13], [18, 21, 26, 30, 2, 10, 13, 1], [28, 31, 18, 22, 26, 17], [28, 31, 1, 2, 26, 22, 17], [20, 4, 16, 2, 22, 31, 1, 17], [20, 30, 22, 16, 31, 2, 4, 1], [18, 20, 17, 13, 16, 31, 2, 1], [18, 30, 20, 31, 2, 13, 1], [20, 17, 22, 13, 16, 31, 2, 1], [5, 17, 13, 20, 26, 4], [21, 23, 16, 26, 22, 31, 30, 2, 13], [21, 17, 31, 30, 22, 13], [18, 21, 7, 1, 30, 10, 13], [4, 10, 7, 16, 22, 31, 2, 1], [18, 30, 31, 2, 10, 13, 1, 17], [7, 10, 13, 1, 16, 22, 31, 2], [28, 30, 2, 23, 22, 13, 17], [28, 30, 1, 2, 18, 13], [18, 30, 31, 2, 26, 13, 1, 17], [21, 20, 6, 31, 30, 2, 10, 13, 1], [21, 7, 31, 1, 30, 10, 13], [5, 18, 21, 26, 2, 13, 1], [5, 18, 31, 2, 26, 13, 1, 20, 6], [0, 13, 22, 31, 30, 21, 7], [28, 7, 4, 13, 26, 22, 2, 17], [0, 28, 22, 18, 23, 4, 17, 16], [3, 2, 18, 23, 26, 4, 28]]
private def zeros (k : Fin 50) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 1125899906842623 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage11 stage12 12 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage11)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage12 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut12

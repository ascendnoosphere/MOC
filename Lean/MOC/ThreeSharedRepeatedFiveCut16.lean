import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 19 in cut 16. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut16

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage15.count := ⟨by decide +kernel⟩
local instance : NeZero stage16.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 3, 4, 5, 6, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 8, 9, 10, 11, 12, 13, 14, 0, 15, 16, 17, 18, 19, 0, 0, 0, 20, 0, 0, 21, 22]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[34628178011, 8674215426, 4462741340, 176194717210, 8640467202, 8640660226, 8640463618, 8674149634, 83886850, 100667408, 17280799764, 8674087170, 8674149634, 83886594, 17280830230, 17280801306, 83886594, 83886850, 8674149122, 17280796423, 43050731015, 17280796180, 8674149122]

private def masks : Array ℕ :=
  #[272450, 4194322, 135300, 4581694665, 2155880448, 293994745, 271846505, 5452660736, 1080047814, 361177088, 338690084, 6510608438, 1349590017, 6443965441, 276241409, 4648803329, 5385750779, 5385952457, 294075593, 298259609, 7541358841, 5387589869, 5387918569, 1369712873, 1373634809, 5664671993, 5391850697, 4581625083, 6443764859, 6451889209, 7545754777, 1373836441, 4648796214, 7519673449, 7586461926, 7523605505, 4648732927, 4648799355, 4657185849, 7586520101, 7519345901, 1349524717, 1440817152, 1441858617, 1373649133, 1373715657, 2431648825, 368510009]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 0, 0, 0, 21, 0, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 0, 40, 41, 42]

private def mask (p : Fin 48) : ℕ := masks.getD p.val 0
private def keep (p : Fin 48) : Fin 46 := Fin.ofNat' 46 (kept.getD p.val 0)
private def cross (p k : Fin 48) : Choice 48 46 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 48 then .skip (Fin.ofNat' 48 x)
  else .edge (Fin.ofNat' 46 (x-48)) (((x-48) / 46+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 48) := #[1, 3, 11, 12, 13, 14, 15, 19, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 43, 46, 47]
private def negativeRows : Array (Fin 48) := #[21, 22, 23, 25, 44]
private def positiveRay (i : Fin 23) : Fin 48 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 5) : Fin 48 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 48) : Fin 23 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 48) : Fin 5 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 48) (hp : 0 < stage15.ray p 19)
    (hk : stage15.ray k 19 < 0) :
    CrossOK stage15 stage16 19 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage15.ray p 19 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage15.ray k 19 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage15 stage16 19 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[277055455359080, 228035987715, 21530673155332, 276471339745384, 220391869581346, 241854909058144, 56307557532009, 56164481958188, 0, 0, 259394487906376, 56891655319881, 56688273977612, 57191793165073, 0, 0, 190128610800264, 141226176078380, 141231859425897, 0, 224297016687688, 280987630064960, 279313618850050, 277355626758704, 207197006955176, 0, 154983894912640, 0, 279763626022504, 0, 69882472501632, 72080021268496, 2196849797256]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [5, 22, 13, 26, 31, 30, 2], [0, 26, 1, 2], [11, 16, 31, 22, 2], [24, 31, 22, 2, 13], [0, 2, 13, 22], [0, 26, 18, 31, 4, 17], [0, 2, 22, 31, 30, 1], [0, 13, 4, 30, 17], [0, 13, 17, 22, 30, 21], [3, 26, 18, 31, 2, 4], [3, 26, 22, 13, 2], [3, 26, 31, 1, 30, 2], [3, 21, 1, 31, 30, 2, 23], [10, 28, 2, 31, 26, 22, 13], [5, 22, 13, 20, 26, 2], [5, 22, 32, 26, 31, 2, 1], [11, 5, 30, 13, 2, 1], [11, 28, 26, 22, 2, 10, 13], [10, 28, 1, 31, 26, 17], [28, 31, 1, 2, 26, 22, 17], [10, 2, 4, 26, 31, 1], [11, 16, 31, 2, 18, 1], [10, 2, 13, 22, 26, 31, 1, 17], [5, 17, 13, 20, 26, 4], [30, 16, 31, 2, 22, 23, 21, 13], [24, 21, 2, 23, 22, 13, 17], [11, 24, 2, 22, 13], [11, 28, 5, 26, 2, 13, 1], [11, 5, 26, 31, 18, 2, 1], [0, 13, 22, 31, 30, 21, 7], [24, 2, 22, 23, 1, 17, 28], [0, 16, 22, 18, 23, 4, 17, 28], [3, 26, 18, 2, 23, 4, 28], [10, 30, 23, 22, 31, 21, 13, 16, 12], [30, 23, 2, 12, 22, 31, 21, 13, 7], [11, 22, 31, 2, 30, 13, 6], [3, 28, 1, 17, 22, 23, 24], [24, 22, 18, 26, 23, 17], [24, 31, 18, 1, 26, 17, 16], [0, 2, 18, 31, 4, 32], [11, 17, 31, 2, 13, 1, 6, 32], [10, 4, 26, 18, 31, 1, 17, 32], [5, 17, 1, 32, 26, 31, 20], [11, 24, 2, 13, 1, 32], [11, 30, 31, 2, 7, 13, 1, 32]]
private def zeros (k : Fin 48) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 281474976710655 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage15 stage16 19 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage15)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage16 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut16

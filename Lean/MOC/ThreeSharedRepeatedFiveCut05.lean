import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 0 in cut 5. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut05

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage04.count := ⟨by decide +kernel⟩
local instance : NeZero stage05.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 0, 7, 8, 0, 0, 9, 10, 11, 12, 13, 14]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[8487039, 65922, 65923, 558468, 8849286, 65928, 131721, 65846, 134027, 9342348, 168079, 65853, 65938, 131731, 65940]

private def masks : Array ℕ :=
  #[67108864, 270338, 4194322, 1073741824, 131076, 262194, 394240, 2147484672, 6292480, 8790016, 12714000, 2155880448, 14688256, 8781872, 2155872304, 2147491846, 6299654, 2097188, 2147483702, 2360352, 10756128, 14680112, 10747952]

private def kept : Array ℕ :=
  #[0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 14, 15, 16, 17, 18, 19]

private def mask (p : Fin 23) : ℕ := masks.getD p.val 0
private def keep (p : Fin 23) : Fin 42 := Fin.ofNat' 42 (kept.getD p.val 0)
private def cross (p k : Fin 23) : Choice 23 42 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 23 then .skip (Fin.ofNat' 23 x)
  else .edge (Fin.ofNat' 42 (x-23)) (((x-23) / 42+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 23) := #[3, 5, 6, 7, 8, 9, 10, 13, 14, 17, 18, 19, 20, 21, 22]
private def negativeRows : Array (Fin 23) := #[0, 15, 16]
private def positiveRay (i : Fin 15) : Fin 23 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 3) : Fin 23 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 23) : Fin 15 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 23) : Fin 3 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 23) (hp : 0 < stage04.ray p 0)
    (hk : stage04.ray k 0 < 0) :
    CrossOK stage04 stage05 0 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage04.ray p 0 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage04.ray k 0 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage04 stage05 0 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[0, 360486, 491536, 0, 6579236, 8282144, 0, 0, 0, 0, 524736, 0, 0, 1153538, 0, 0, 0, 9808, 5775970, 0, 0, 8065280, 2168068, 7372288, 0, 0, 1, 0, 0, 0, 8, 313472, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[5, 13, 22, 10, 30, 2], [5, 22, 31, 17, 26, 30], [5, 13, 10, 17, 26, 30], [5, 13, 22, 10, 26, 2], [5, 13, 22, 10, 26, 30], [23, 2, 10, 26, 22, 30, 13], [5, 13, 22, 26, 31, 30, 2], [5, 13, 22, 17, 26, 30], [5, 13, 17, 26, 31, 30, 4], [5, 22, 31, 26, 30, 2, 10, 1], [5, 13, 10, 26, 30, 2, 1], [5, 22, 18, 2, 26, 30, 10], [5, 1, 17, 31, 26, 30, 10], [21, 31, 1, 26, 22, 30, 2, 10, 13], [18, 22, 2, 26, 30, 10, 13], [5, 22, 18, 26, 30, 23, 10, 17], [5, 23, 10, 26, 18, 31, 30, 4, 17], [23, 1, 10, 26, 30, 17], [23, 18, 22, 26, 30, 21, 10, 13, 17], [23, 1, 2, 26, 22, 31, 30, 17], [4, 2, 10, 26, 22, 31, 30, 1, 17], [18, 31, 2, 26, 30, 10, 13, 1, 17], [13, 22, 31, 17, 26, 30, 2, 10, 1]]
private def zeros (k : Fin 23) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 8388607 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage04 stage05 0 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage04)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage05 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut05

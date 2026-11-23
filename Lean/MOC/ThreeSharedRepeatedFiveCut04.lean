import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 17 in cut 4. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut04

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage03.count := ⟨by decide +kernel⟩
local instance : NeZero stage04.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 3, 0, 0, 4, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[623125282, 148766977, 22348033, 39191042, 136904961]

private def masks : Array ℕ :=
  #[67108864, 270338, 4194322, 2147491842, 1073741824, 4, 6299650, 2097184, 262194, 263168, 2147483698, 2147484672, 6292480, 8658944, 12582928, 2155880448, 14688256, 8650800, 2155872304]

private def kept : Array ℕ :=
  #[0, 1, 2, 0, 3, 4, 0, 0, 5, 6, 0, 7, 8, 9, 10, 11, 12, 13, 14]

private def mask (p : Fin 19) : ℕ := masks.getD p.val 0
private def keep (p : Fin 19) : Fin 23 := Fin.ofNat' 23 (kept.getD p.val 0)
private def cross (p k : Fin 19) : Choice 19 23 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 19 then .skip (Fin.ofNat' 19 x)
  else .edge (Fin.ofNat' 23 (x-19)) (((x-19) / 23+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 19) := #[5, 9, 13, 14, 17]
private def negativeRows : Array (Fin 19) := #[3, 6, 7, 10]
private def positiveRay (i : Fin 5) : Fin 19 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 4) : Fin 19 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 19) : Fin 5 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 19) : Fin 4 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 19) (hp : 0 < stage03.ray p 17)
    (hk : stage03.ray k 17 < 0) :
    CrossOK stage03 stage04 17 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage03.ray p 17 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage03.ray k 17 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage03 stage04 17 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[0, 1358, 32, 0, 410884, 394624, 0, 0, 0, 0, 6656, 0, 0, 106570, 0, 0, 0, 0, 140034, 0, 0, 69824, 86084, 516096, 0, 0, 1, 0, 0, 0, 16, 297992, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[23, 1, 10, 5, 30, 2], [23, 22, 31, 5, 26, 30, 2, 10], [23, 18, 31, 21, 26, 30, 2], [23, 18, 22, 5, 26, 30, 2, 10], [23, 1, 10, 26, 5, 2], [23, 1, 10, 26, 5, 30], [23, 18, 31, 26, 5, 30, 2, 10, 4], [23, 1, 10, 26, 30, 2], [23, 22, 31, 26, 30, 2, 21, 10, 13], [23, 1, 21, 26, 31, 30, 2], [23, 18, 22, 26, 30, 2, 21, 10, 13], [23, 1, 21, 26, 18, 30, 2], [23, 1, 26, 18, 31, 5, 30, 2], [4, 21, 31, 26, 30, 2, 10, 1], [13, 5, 10, 26, 30, 2, 1], [4, 21, 18, 26, 30, 2, 10, 1], [4, 18, 31, 26, 5, 30, 2, 10, 1], [13, 22, 31, 26, 30, 2, 21, 10, 1], [13, 18, 22, 26, 30, 2, 21, 10, 1]]
private def zeros (k : Fin 19) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 524287 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage03 stage04 17 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage03)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage04 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut04

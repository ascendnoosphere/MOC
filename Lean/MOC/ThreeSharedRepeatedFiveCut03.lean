import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 1 in cut 3. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut03

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage02.count := ⟨by decide +kernel⟩
local instance : NeZero stage03.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 1, 2, 0, 0, 0, 3, 0, 4, 0, 5, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[27, 28, 181, 182, 183, 70]

private def masks : Array ℕ :=
  #[67108864, 270336, 4194320, 2147491840, 1073741824, 4, 8388608, 6299648, 2097184, 262192, 263168, 2147483696, 2147484672, 6292480]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 0, 6, 7, 8, 9, 10, 11, 12]

private def mask (p : Fin 14) : ℕ := masks.getD p.val 0
private def keep (p : Fin 14) : Fin 19 := Fin.ofNat' 19 (kept.getD p.val 0)
private def cross (p k : Fin 14) : Choice 14 19 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 14 then .skip (Fin.ofNat' 14 x)
  else .edge (Fin.ofNat' 19 (x-14)) (((x-14) / 19+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 14) := #[1, 2, 3, 7, 9, 11]
private def negativeRows : Array (Fin 14) := #[6]
private def positiveRay (i : Fin 6) : Fin 14 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 1) : Fin 14 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 14) : Fin 6 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 14) : Fin 1 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 14) (hp : 0 < stage02.ray p 1)
    (hk : stage02.ray k 1 < 0) :
    CrossOK stage02 stage03 1 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage02.ray p 1 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage02.ray k 1 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage02 stage03 1 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[0, 0, 32, 0, 2564, 2816, 0, 0, 0, 0, 13312, 0, 0, 138, 0, 0, 0, 0, 1538, 0, 0, 8576, 8324, 64, 0, 0, 1, 0, 0, 0, 16, 6152, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[18, 22, 31, 5, 30, 2, 23], [22, 31, 5, 26, 30, 2, 23, 10], [18, 31, 21, 26, 30, 2, 23], [18, 22, 5, 26, 30, 2, 23, 10], [18, 22, 31, 26, 5, 2, 23], [18, 22, 31, 26, 5, 30, 23], [18, 22, 31, 26, 5, 30, 2], [18, 31, 26, 5, 30, 2, 23, 10, 4], [18, 22, 31, 26, 30, 2, 23], [22, 31, 26, 30, 2, 23, 21, 10, 13], [22, 31, 5, 26, 30, 2, 23, 13], [18, 22, 26, 30, 2, 23, 21, 10, 13], [18, 22, 5, 26, 30, 2, 23, 13], [18, 31, 26, 5, 30, 2, 23, 4, 13]]
private def zeros (k : Fin 14) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 16383 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage02 stage03 1 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage02)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage03 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut03

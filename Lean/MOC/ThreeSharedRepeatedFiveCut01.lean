import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 4 in cut 1. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut01

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage00.count := ⟨by decide +kernel⟩
local instance : NeZero stage01.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 1, 0, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[19, 42]

private def masks : Array ℕ :=
  #[67108864, 262144, 4194304, 2147483648, 32, 1073741824, 4, 8388608, 2097152, 1024]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 0, 8]

private def mask (p : Fin 10) : ℕ := masks.getD p.val 0
private def keep (p : Fin 10) : Fin 11 := Fin.ofNat' 11 (kept.getD p.val 0)
private def cross (p k : Fin 10) : Choice 10 11 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (6 * negativeIndex.getD k.val 0)) &&& 63
  if x < 10 then .skip (Fin.ofNat' 10 x)
  else .edge (Fin.ofNat' 11 (x-10)) (((x-10) / 11+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 10) := #[2, 4]
private def negativeRows : Array (Fin 10) := #[8]
private def positiveRay (i : Fin 2) : Fin 10 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 1) : Fin 10 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 10) : Fin 2 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 10) : Fin 1 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 10) (hp : 0 < stage00.ray p 4)
    (hk : stage00.ray k 4 < 0) :
    CrossOK stage00 stage01 4 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage00.ray p 4 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage00.ray k 4 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage00 stage01 4 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[0, 0, 64, 0, 0, 16, 0, 0, 0, 0, 512, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 256, 4, 128, 0, 0, 1, 0, 0, 0, 32, 8, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[18, 22, 31, 5, 30, 2, 23, 21, 10], [26, 22, 31, 5, 30, 2, 23, 21, 10], [26, 18, 31, 5, 30, 2, 23, 21, 10], [26, 18, 22, 5, 30, 2, 23, 21, 10], [26, 18, 22, 31, 30, 2, 23, 21, 10], [26, 18, 22, 31, 5, 2, 23, 21, 10], [26, 18, 22, 31, 5, 30, 23, 21, 10], [26, 18, 22, 31, 5, 30, 2, 21, 10], [26, 18, 22, 31, 5, 30, 2, 23, 10], [26, 18, 22, 31, 5, 30, 2, 23, 21]]
private def zeros (k : Fin 10) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 1023 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage00 stage01 4 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage00)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage01 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut01

import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 13 in cut 2. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut02

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage01.count := ⟨by decide +kernel⟩
local instance : NeZero stage02.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]

private def crossRows : Array ℕ :=
  #[1364, 3314, 3330]

private def masks : Array ℕ :=
  #[67108864, 262144, 4194320, 2147483648, 48, 1073741824, 4, 8388608, 1024, 6291456, 2097184]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 0, 4, 5, 6, 0, 7, 8]

private def mask (p : Fin 11) : ℕ := masks.getD p.val 0
private def keep (p : Fin 11) : Fin 14 := Fin.ofNat' 14 (kept.getD p.val 0)
private def cross (p k : Fin 11) : Choice 11 14 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (6 * negativeIndex.getD k.val 0)) &&& 63
  if x < 11 then .skip (Fin.ofNat' 11 x)
  else .edge (Fin.ofNat' 14 (x-11)) (((x-11) / 14+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 11) := #[1, 3, 9]
private def negativeRows : Array (Fin 11) := #[4, 8]
private def positiveRay (i : Fin 3) : Fin 11 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 2) : Fin 11 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 11) : Fin 3 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 11) : Fin 2 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 11) (hp : 0 < stage01.ray p 13)
    (hk : stage01.ray k 13 < 0) :
    CrossOK stage01 stage02 13 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage01.ray p 13 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage01.ray k 13 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage01 stage02 13 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[0, 0, 64, 0, 20, 1040, 0, 0, 0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1536, 516, 128, 0, 0, 1, 0, 0, 0, 32, 8, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[22, 5, 18, 31, 30, 2, 23, 10], [22, 5, 26, 31, 30, 2, 23, 10], [5, 26, 18, 31, 30, 2, 23, 21, 10], [22, 5, 26, 18, 30, 2, 23, 10], [22, 26, 18, 31, 30, 2, 23, 21, 10], [22, 5, 26, 18, 31, 2, 23, 10], [22, 5, 26, 18, 31, 30, 23, 10], [22, 5, 26, 18, 31, 30, 2, 10], [22, 5, 26, 18, 31, 30, 2, 23], [5, 26, 18, 31, 30, 2, 23, 10, 4], [22, 26, 18, 31, 30, 2, 23, 10, 4]]
private def zeros (k : Fin 11) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 2047 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage01 stage02 13 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage01)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage02 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut02

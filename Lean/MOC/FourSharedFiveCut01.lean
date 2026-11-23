import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 13 in cut 1. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut01

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage00.count := ⟨by decide +kernel⟩
local instance : NeZero stage01.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 2, 0, 0, 0, 0, 3]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0]

private def crossRows : Array ℕ :=
  #[2103554, 535044, 2111750, 2115848]

private def masks : Array ℕ :=
  #[8589934592, 4398046511104, 70368744177664, 2048, 274877906944, 4294967296, 137438953472, 262144, 2, 512]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 0, 0, 6, 7]

private def mask (p : Fin 10) : ℕ := masks.getD p.val 0
private def keep (p : Fin 10) : Fin 16 := Fin.ofNat' 16 (kept.getD p.val 0)
private def cross (p k : Fin 10) : Choice 10 16 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (11 * negativeIndex.getD k.val 0)) &&& 2047
  if x < 10 then .skip (Fin.ofNat' 10 x)
  else .edge (Fin.ofNat' 16 (x-10)) (((x-10) / 16+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 10) := #[0, 3, 4, 9]
private def negativeRows : Array (Fin 10) := #[6, 7]
private def positiveRay (i : Fin 4) : Fin 10 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 2) : Fin 10 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 10) : Fin 4 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 10) : Fin 2 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 10) (hp : 0 < stage00.ray p 13)
    (hk : stage00.ray k 13 < 0) :
    CrossOK stage00 stage01 13 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage00.ray p 13 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage00.ray k 13 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage00 stage01 13 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[0, 256, 0, 0, 0, 0, 0, 0, 0, 512, 0, 8, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 1, 0, 0, 0, 64, 16, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[42, 46, 11, 38, 32, 37, 18, 1, 9], [33, 46, 11, 38, 32, 37, 18, 1, 9], [33, 42, 11, 38, 32, 37, 18, 1, 9], [33, 42, 46, 38, 32, 37, 18, 1, 9], [33, 42, 46, 11, 32, 37, 18, 1, 9], [33, 42, 46, 11, 38, 37, 18, 1, 9], [33, 42, 46, 11, 38, 32, 18, 1, 9], [33, 42, 46, 11, 38, 32, 37, 1, 9], [33, 42, 46, 11, 38, 32, 37, 18, 9], [33, 42, 46, 11, 38, 32, 37, 18, 1]]
private def zeros (k : Fin 10) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 1023 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage00 stage01 13 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage00)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage01 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut01

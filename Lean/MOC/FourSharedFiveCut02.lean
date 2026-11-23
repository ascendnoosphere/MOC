import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 47 in cut 2. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut02

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage01.count := ⟨by decide +kernel⟩
local instance : NeZero stage02.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 5]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[603436, 605486, 4100, 4100, 7175, 7175]

private def masks : Array ℕ :=
  #[8589942784, 4398046511104, 70368744177664, 10240, 274877915136, 4294967296, 2, 8704, 146028888064, 8590196736, 137438955520, 264192, 412316860416, 274878169088, 137438953984, 262656]

private def kept : Array ℕ :=
  #[0, 0, 1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

private def mask (p : Fin 16) : ℕ := masks.getD p.val 0
private def keep (p : Fin 16) : Fin 18 := Fin.ofNat' 18 (kept.getD p.val 0)
private def cross (p k : Fin 16) : Choice 16 18 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (10 * negativeIndex.getD k.val 0)) &&& 1023
  if x < 16 then .skip (Fin.ofNat' 16 x)
  else .edge (Fin.ofNat' 18 (x-16)) (((x-16) / 18+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 16) := #[4, 7, 12, 13, 14, 15]
private def negativeRows : Array (Fin 16) := #[0, 3]
private def positiveRay (i : Fin 6) : Fin 16 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 2) : Fin 16 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 16) : Fin 6 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 16) : Fin 2 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 16) (hp : 0 < stage01.ray p 47)
    (hk : stage01.ray k 47 < 0) :
    CrossOK stage01 stage02 47 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage01.ray p 47 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage01.ray k 47 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage01 stage02 47 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[0, 64, 0, 0, 0, 0, 0, 0, 0, 49280, 0, 3080, 0, 153, 0, 0, 0, 0, 43520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 769, 0, 0, 0, 21760, 12304, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[37, 18, 42, 46, 11, 38, 32, 1, 9], [37, 18, 13, 46, 32, 1], [37, 18, 13, 42, 32, 1], [37, 18, 33, 42, 46, 38, 32, 1, 9], [37, 18, 33, 42, 46, 11, 32, 1, 9], [37, 18, 13, 42, 46, 1], [37, 18, 13, 42, 46, 32], [37, 18, 33, 42, 46, 11, 38, 32, 1], [18, 13, 42, 46, 11, 38, 32, 1, 9], [37, 13, 42, 46, 11, 38, 32, 1, 9], [18, 13, 33, 42, 46, 38, 32, 1, 9], [37, 13, 33, 42, 46, 38, 32, 1, 9], [18, 13, 33, 42, 46, 11, 32, 1, 9], [37, 13, 33, 42, 46, 11, 32, 1, 9], [18, 13, 33, 42, 46, 11, 38, 32, 1], [37, 13, 33, 42, 46, 11, 38, 32, 1]]
private def zeros (k : Fin 16) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 65535 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage01 stage02 47 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage01)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage02 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut02

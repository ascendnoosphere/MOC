import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 7 in cut 11. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut11

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage10.count := ⟨by decide +kernel⟩
local instance : NeZero stage11.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 5, 0, 0, 6, 0, 7, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 4, 0, 5, 0, 0]

private def crossRows : Array ℕ :=
  #[3207974602493606, 11844970742331996, 199218459838561, 422969321195524, 845733176543236, 12069341312371204, 70520146497544, 70508089709578]

private def masks : Array ℕ :=
  #[4294967296, 42950459392, 1126037345802241, 141012400078848, 140737489142272, 1126174885423105, 1125899974486529, 74801251090433, 70403204847617, 4398046511106, 268290, 1130478342504449, 1271447792123905, 1271172881187329, 283467849794, 211106300174913, 70549132808257, 211243671491137, 70686672429121, 70411761492545, 70403204594241, 1126355173908545, 70368811301443, 1267058335555649, 1267058302526017, 211381211112001]

private def kept : Array ℕ :=
  #[0, 0, 1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 12, 13, 14, 0, 15, 16, 0, 17, 0, 18, 19]

private def mask (p : Fin 26) : ℕ := masks.getD p.val 0
private def keep (p : Fin 26) : Fin 40 := Fin.ofNat' 40 (kept.getD p.val 0)
private def cross (p k : Fin 26) : Choice 26 40 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (9 * negativeIndex.getD k.val 0)) &&& 511
  if x < 26 then .skip (Fin.ofNat' 26 x)
  else .edge (Fin.ofNat' 40 (x-26)) (((x-26) / 40+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 26) := #[0, 2, 6, 13, 15, 17, 20, 22]
private def negativeRows : Array (Fin 26) := #[1, 3, 14, 18, 21, 23]
private def positiveRay (i : Fin 8) : Fin 26 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 6) : Fin 26 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 26) : Fin 8 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 26) : Fin 6 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 26) (hp : 0 < stage10.ray p 7)
    (hk : stage10.ray k 7 < 0) :
    CrossOK stage10 stage11 7 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage10.ray p 7 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage10.ray k 7 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage10 stage11 7 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[67090916, 4212224, 0, 0, 0, 0, 67092480, 0, 0, 56270928, 0, 5244260, 5440772, 66895968, 0, 0, 0, 0, 1306, 19441746, 0, 0, 0, 0, 0, 43258280, 39616992, 0, 0, 0, 0, 0, 1, 28133378, 0, 4000130, 0, 27473924, 61100072, 0, 0, 0, 14976, 0, 0, 0, 39813504, 58896408, 0, 0, 27277412]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[0, 18, 1], [0, 1, 47, 32], [13, 42, 18, 46, 32], [0, 1, 19, 32], [0, 1, 33, 38, 32], [6, 42, 18, 32, 37, 9], [6, 42, 18, 38, 32, 37], [13, 37, 18, 32, 1], [13, 37, 42, 47, 33, 32, 1], [0, 18, 33, 32], [0, 33, 47, 42, 32], [13, 18, 46, 47, 11, 32, 1], [13, 18, 46, 19, 11, 32, 1], [13, 18, 46, 33, 11, 38, 32, 1], [0, 18, 42, 32], [33, 11, 42, 38, 32, 37, 18], [13, 42, 18, 11, 32, 9], [13, 42, 18, 33, 11, 32], [9, 37, 18, 42, 11, 32, 1], [38, 12, 42, 18, 11, 32, 47], [33, 47, 1, 50, 42, 32, 18], [46, 47, 11, 42, 32, 18, 1], [33, 47, 25, 50, 42, 32, 18], [46, 19, 11, 42, 32, 18, 1], [46, 42, 11, 18, 32, 1, 25, 35], [33, 11, 42, 18, 32, 37, 19]]
private def zeros (k : Fin 26) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 67108863 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage10 stage11 7 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage10)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage11 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut11

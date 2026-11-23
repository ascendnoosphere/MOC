import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 14 in cut 22. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut22

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage21.count := ⟨by decide +kernel⟩
local instance : NeZero stage22.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 4, 5, 6, 0, 0, 7, 0, 0, 8, 0, 0, 0, 0, 9, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[120462262, 128916922, 2146304, 6340670, 8577087, 6340673, 141590660, 35922628, 150044804, 6340680]

private def masks : Array ℕ :=
  #[272962, 138936338, 135556, 2692784128, 428213241, 271847017, 5452660736, 1616918726, 495427584, 338690084, 6511133494, 6444523265, 411016193, 5385953225, 428326857, 433034649, 8078230521, 2044723449, 5928721609, 6444289915, 6989317945, 8217400729, 8061033473, 1886395629, 3103294521, 503284793, 2045230281, 8060936191, 6939445049]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 0, 18, 19, 20, 0, 21, 22, 23, 24]

private def mask (p : Fin 29) : ℕ := masks.getD p.val 0
private def keep (p : Fin 29) : Fin 44 := Fin.ofNat' 44 (kept.getD p.val 0)
private def cross (p k : Fin 29) : Choice 29 44 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (7 * negativeIndex.getD k.val 0)) &&& 127
  if x < 29 then .skip (Fin.ofNat' 29 x)
  else .edge (Fin.ofNat' 44 (x-29)) (((x-29) / 44+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 29) := #[2, 6, 7, 8, 13, 14, 15, 18, 21, 26]
private def negativeRows : Array (Fin 29) := #[5, 19, 20, 24]
private def positiveRay (i : Fin 10) : Fin 29 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 4) : Fin 29 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 29) : Fin 10 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 29) : Fin 4 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 29) (hp : 0 < stage21.ray p 14)
    (hk : stage21.ray k 14 < 0) :
    CrossOK stage21 stage22 14 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage21.ray p 14 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage21.ray k 14 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage21 stage22 14 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[536868912, 134743171, 142608004, 532668464, 456885266, 463144496, 210722993, 212328596, 406449172, 404319281, 536672288, 214726817, 216332420, 67125641, 0, 393271560, 375716160, 371259668, 369686833, 460889090, 467148320, 264639136, 266768514, 389267736, 371712336, 0, 301991744, 388157714, 394449712, 234291336, 216473792, 427363336, 410856512]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [0, 26, 1, 2], [10, 26, 29, 1, 2], [22, 8, 26, 13], [0, 2, 13, 22], [0, 26, 18, 31, 4, 17], [0, 2, 1, 31, 30], [0, 13, 4, 30, 17], [0, 13, 22, 30, 21, 17], [3, 26, 22, 13, 2], [3, 26, 31, 1, 2], [22, 5, 13, 26, 31, 2], [22, 5, 32, 26, 31, 2, 1], [5, 11, 26, 31, 2, 1], [10, 26, 22, 18, 2, 13], [10, 26, 13, 8, 1], [18, 31, 2, 4, 26], [22, 23, 26, 17, 21, 13], [18, 22, 26, 7, 13], [18, 5, 21, 26, 2, 13, 1], [3, 26, 18, 2, 23, 4], [18, 31, 24, 1, 26, 17], [18, 30, 2, 13, 1, 32], [6, 31, 12, 30, 2, 13, 1], [5, 32, 1, 8, 26, 31, 20], [18, 23, 26, 16, 13, 17, 28, 27], [22, 6, 2, 13, 30, 12, 29]]
private def zeros (k : Fin 29) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 536870911 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage21 stage22 14 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage21)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage22 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut22

import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 29 in cut 21. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut21

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage20.count := ⟨by decide +kernel⟩
local instance : NeZero stage21.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 4, 0, 5, 6, 0, 7, 0, 0, 8, 9, 0, 0, 10, 11]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 4, 0, 0, 0, 5, 0, 0]

private def crossRows : Array ℕ :=
  #[2416067724, 0, 173151437189, 35704029573, 35167158669, 127551063557, 36240901004, 36240901004, 34898723074, 40267433477, 805306765, 34630287489]

private def masks : Array ℕ :=
  #[272962, 138936338, 135556, 4716470217, 2155913216, 428213241, 271847017, 5452660736, 1080047814, 495427584, 338690084, 6511133494, 6444523265, 411016193, 4783578881, 5385953225, 428326857, 433034649, 7541359609, 1507852537, 5391850697, 6444289915, 6452447033, 7680529817, 4783538998, 7524162561, 4783542139, 4791961401, 1349524717, 2566423609, 503284793, 4716437499, 1508359369, 7524065279]

private def kept : Array ℕ :=
  #[0, 1, 2, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 13, 14, 15, 16, 17, 18, 19, 20, 21, 0, 22, 0, 0, 23, 24, 25, 0, 26, 27]

private def mask (p : Fin 34) : ℕ := masks.getD p.val 0
private def keep (p : Fin 34) : Fin 29 := Fin.ofNat' 29 (kept.getD p.val 0)
private def cross (p k : Fin 34) : Choice 34 29 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (7 * negativeIndex.getD k.val 0)) &&& 127
  if x < 34 then .skip (Fin.ofNat' 34 x)
  else .edge (Fin.ofNat' 29 (x-34)) (((x-34) / 29+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 34) := #[4, 8, 18, 19, 20, 22, 23, 25, 28, 29, 32, 33]
private def negativeRows : Array (Fin 34) := #[3, 14, 24, 26, 27, 31]
private def positiveRay (i : Fin 12) : Fin 34 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 6) : Fin 34 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 34) : Fin 12 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 34) : Fin 6 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 34) (hp : 0 < stage20.ray p 29)
    (hk : stage20.ray k 29 < 0) :
    CrossOK stage20 stage21 29 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage20.ray p 29 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage20.ray k 29 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage20 stage21 29 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[17163087976, 10823403779, 8875150596, 17129504872, 12581734434, 12841651296, 15371960681, 15311274284, 10970716204, 10962196585, 17162301512, 15404757321, 15344070924, 4295033617, 0, 6086160920, 7777546888, 7742943788, 7736652393, 12614531082, 12874447944, 14799086912, 14807605506, 6053364272, 7744766632, 0, 1291865728, 8280302122, 8540350056, 0, 13197148544, 9175308304, 11005122696]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [5, 22, 13, 26, 31, 30, 2], [0, 26, 1, 2], [10, 26, 22, 31, 2, 13], [16, 4, 2, 13], [0, 2, 13, 22], [0, 26, 18, 31, 4, 17], [0, 2, 1, 31, 30], [0, 1, 23, 30, 17], [0, 13, 17, 22, 30, 21], [3, 26, 22, 13, 2], [3, 26, 31, 1, 2], [3, 2, 22, 13, 31, 30], [20, 23, 22, 26, 2, 13], [20, 30, 4, 26, 31, 2, 1], [20, 6, 26, 31, 2, 1], [10, 26, 22, 18, 2, 13], [10, 26, 13, 8, 1], [18, 31, 2, 4, 26], [16, 21, 23, 2, 22, 13], [18, 22, 26, 7, 13], [18, 5, 21, 26, 2, 13, 1], [0, 13, 22, 31, 30, 21, 7], [3, 26, 18, 2, 23, 4], [12, 23, 2, 22, 31, 30, 21, 13], [11, 22, 31, 2, 30, 13, 6], [18, 31, 24, 1, 26, 17], [18, 30, 2, 13, 1, 32], [8, 11, 31, 30, 2, 13, 1], [15, 30, 26, 22, 31, 2, 23, 21, 13], [20, 8, 1, 26, 31, 5, 32], [18, 23, 26, 16, 13, 17, 28, 27]]
private def zeros (k : Fin 34) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 17179869183 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage20 stage21 29 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage20)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage21 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut21

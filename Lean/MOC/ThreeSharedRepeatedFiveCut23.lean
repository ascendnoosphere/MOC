import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 25 in cut 23. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut23

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage22.count := ⟨by decide +kernel⟩
local instance : NeZero stage23.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 4, 0, 0, 0, 5, 0, 0, 6, 0, 0, 7, 0, 0, 8, 9, 0, 0, 10, 11, 0, 0, 0, 0, 12, 13, 0, 0, 14, 15, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 5, 6, 7, 0, 0, 8, 9, 0, 0, 10]

private def crossRows : Array ℕ :=
  #[790039828909113206605, 110982365498228988062678, 25973383262275777987205, 212714132226214855298, 4731880341619028832351, 3551288157951664107873, 12996526089824679101060, 3551288734121531081220, 3634730891637446754562, 3551288157951879659778, 3681208039817749856901, 3552152849107503940228, 3551288157951668322820, 3551288157951668438404, 3551288157951668504458, 3551288157951668520964]

private def masks : Array ℕ :=
  #[272962, 138936338, 151940, 2692784128, 428213241, 5452677120, 1616935110, 495443968, 338690084, 6511133494, 6444523265, 411016193, 5385969609, 428343241, 433051033, 8078230521, 2044723449, 5928737993, 8217417113, 8061033473, 1886395629, 503284793, 2045246665, 8060936191, 6939445049, 271982573, 6444425215, 6989453245, 3103430077, 5724507753, 7601983355, 8147011385, 8555955257, 498577001, 5657534441, 7535009787, 431472617, 7413405625, 3120534969, 6198468329, 8078041083, 8218449849, 8488981945, 2046279401]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 12, 13, 14, 15, 0, 16, 17, 0, 18, 19, 20, 21, 0, 22, 23, 24, 0, 25, 26, 27, 28, 0, 0, 0, 29, 30, 0, 0, 31, 32, 0]

private def mask (p : Fin 44) : ℕ := masks.getD p.val 0
private def keep (p : Fin 44) : Fin 63 := Fin.ofNat' 63 (kept.getD p.val 0)
private def cross (p k : Fin 44) : Choice 44 63 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (7 * negativeIndex.getD k.val 0)) &&& 127
  if x < 44 then .skip (Fin.ofNat' 44 x)
  else .edge (Fin.ofNat' 63 (x-44)) (((x-44) / 63+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 44) := #[1, 3, 7, 9, 14, 18, 21, 24, 27, 28, 31, 32, 37, 38, 41, 42]
private def negativeRows : Array (Fin 44) := #[12, 17, 20, 25, 29, 34, 35, 36, 39, 40, 43]
private def positiveRay (i : Fin 16) : Fin 44 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 11) : Fin 44 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 44) : Fin 16 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 44) : Fin 11 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 44) (hp : 0 < stage22.ray p 25)
    (hk : stage22.ray k 25 < 0) :
    CrossOK stage22 stage23 25 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage22.ray p 25 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage22.ray k 25 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage22 stage23 25 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[17592186043408, 1135020606019, 512754500, 17592185516048, 8151271588370, 17592180900624, 10575934632017, 17575523643476, 8232907372052, 12914689881617, 17592185945088, 10575935061057, 17575524072516, 8873406636233, 4616420, 15889658047624, 17591673191584, 15934855347348, 10988260719761, 8151272017410, 17592181329664, 15217924442432, 17459327223874, 15889657618584, 17591672762544, 0, 16661873568, 15887375886482, 14255859526032, 17461606842440, 17102037553248, 8151269934600, 8443596281376]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [0, 26, 1, 2], [10, 26, 29, 1, 2], [0, 2, 13, 22], [0, 26, 18, 31, 4, 17], [0, 2, 1, 31, 30], [0, 13, 4, 14], [0, 13, 14, 22, 21], [3, 26, 22, 13, 2], [3, 26, 31, 1, 2], [5, 15, 22, 26, 2, 13], [5, 22, 32, 26, 31, 2, 1], [5, 11, 26, 31, 2, 1], [10, 26, 22, 18, 2, 13], [10, 26, 13, 8, 1], [5, 17, 13, 19, 26], [5, 11, 26, 18, 2, 13, 1], [3, 26, 18, 2, 23, 4], [16, 4, 13, 17, 26], [7, 32, 13, 2, 1, 12], [5, 32, 1, 8, 26, 31, 20], [16, 23, 18, 26, 14, 28, 27], [7, 21, 1, 30, 13, 12], [16, 4, 13, 26, 22, 14], [16, 29, 28, 26, 22, 13, 14], [16, 6, 26, 22, 13, 14], [16, 6, 26, 13, 1, 32, 14], [7, 19, 13, 2, 14], [7, 15, 2, 22, 21, 13, 14], [7, 18, 22, 2, 13, 14], [7, 18, 2, 13, 1, 12, 8, 14], [7, 19, 30, 31, 2, 1, 14], [23, 19, 2, 14, 26, 22, 13], [28, 29, 26, 2, 22, 13, 15, 14], [32, 22, 26, 2, 31, 4, 1, 14], [30, 21, 2, 13, 26, 1, 6, 11, 14], [9, 30, 26, 2, 13, 1, 11, 14], [17, 31, 26, 1, 2, 23, 14], [17, 26, 2, 23, 13, 28, 15, 27, 14], [18, 21, 26, 2, 13, 1, 6, 14], [18, 2, 26, 6, 13, 1, 11, 9, 14], [8, 26, 1, 32, 31, 2, 4, 19, 14]]
private def zeros (k : Fin 44) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 17592186044415 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage22 stage23 25 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage22)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage23 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut23

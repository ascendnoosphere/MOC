import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 25 in cut 23. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut23

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

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

private theorem valid : Valid stage22 stage23 25 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage22)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage23 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut23

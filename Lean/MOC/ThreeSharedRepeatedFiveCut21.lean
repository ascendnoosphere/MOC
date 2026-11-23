import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 29 in cut 21. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut21

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

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

private theorem valid : Valid stage20 stage21 29 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage20)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage21 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut21

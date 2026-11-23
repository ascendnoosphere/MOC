import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 14 in cut 22. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut22

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

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

private theorem valid : Valid stage21 stage22 14 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage21)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage22 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut22

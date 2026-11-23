import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 27 in cut 20. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut20

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 5, 0, 6, 7, 0, 8, 0, 0, 0, 9, 10, 0, 0, 0, 11, 12, 0, 0, 0, 13, 14, 0, 15, 16]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 3, 0, 0, 0, 4, 0, 0]

private def crossRows : Array ℕ :=
  #[5517788181, 1614839814, 1614839811, 1078001668, 809664518, 809615366, 1077968899, 809533443, 1648477190, 3225452684, 541179910, 1614905350, 809615366, 1656914054, 809615366, 1614839811, 1077968899]

private def masks : Array ℕ :=
  #[272962, 4718610, 135556, 4582252489, 2155913216, 293995513, 271847017, 5452660736, 1080047814, 361209856, 338690084, 6511133494, 6444523265, 276798465, 4649361153, 5385953225, 294109129, 298816921, 7541359609, 1373634809, 5391850697, 6444289915, 6452447033, 7546312089, 4649321270, 7520231273, 7586462694, 7524162561, 4649324411, 4657743673, 7587077925, 7519346669, 1349524717, 2432205881, 369067065, 7536451561, 4582219771, 1374141641]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 25, 26, 27, 0, 0, 28, 29, 30, 0, 31, 32]

private def mask (p : Fin 38) : ℕ := masks.getD p.val 0
private def keep (p : Fin 38) : Fin 34 := Fin.ofNat' 34 (kept.getD p.val 0)
private def cross (p k : Fin 38) : Choice 38 34 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (7 * negativeIndex.getD k.val 0)) &&& 127
  if x < 38 then .skip (Fin.ofNat' 38 x)
  else .edge (Fin.ofNat' 34 (x-38)) (((x-38) / 34+1 : ℕ) : ℤ)

private theorem valid : Valid stage19 stage20 27 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage19)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage20 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut20

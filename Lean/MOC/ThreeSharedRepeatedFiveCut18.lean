import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 8 in cut 18. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut18

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 4, 0, 5, 6, 7, 8, 9, 0, 0, 10, 11, 12, 0, 13, 14, 15, 0, 16, 17, 18, 19, 0, 0, 0, 0, 0, 0, 20, 21]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[172140752, 25248654, 35980422, 2113665, 6406670, 6407047, 35701635, 262227086, 36062350, 8503828, 16385, 8503837, 8503833, 16513, 8487430, 8405512, 16385, 6407047, 8503818, 8503837, 8487430, 16385]

private def masks : Array ℕ :=
  #[272450, 4718610, 135300, 4582251721, 2155913216, 293994745, 271846505, 5452660736, 1080047814, 361209856, 338690084, 6511132726, 1350147073, 6444522497, 276798465, 4649360385, 5385952457, 294108361, 298816665, 7541358841, 1373634809, 5391850697, 6444289147, 6452446265, 7546311833, 1374393497, 4649320502, 7520230505, 7586461926, 7524162561, 4649323643, 4657742905, 7587077157, 7519345901, 1349524717, 1440849920, 1442415673, 1373748425, 2432205881, 369067065, 7536450793, 4582219003]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 0, 0, 0, 34, 35, 36, 37]

private def mask (p : Fin 42) : ℕ := masks.getD p.val 0
private def keep (p : Fin 42) : Fin 42 := Fin.ofNat' 42 (kept.getD p.val 0)
private def cross (p k : Fin 42) : Choice 42 42 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (7 * negativeIndex.getD k.val 0)) &&& 127
  if x < 42 then .skip (Fin.ofNat' 42 x)
  else .edge (Fin.ofNat' 42 (x-42)) (((x-42) / 42+1 : ℕ) : ℤ)

private theorem valid : Valid stage17 stage18 8 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage17)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage18 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut18

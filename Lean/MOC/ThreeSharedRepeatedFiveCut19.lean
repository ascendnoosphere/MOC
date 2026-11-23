import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 9 in cut 19. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut19

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 2, 3, 0, 0, 0, 0, 4, 5, 0, 6, 7, 8, 0, 9, 0, 0, 10, 11, 0, 0, 12, 13, 14, 0, 15, 16, 17, 18, 0, 0, 0, 19, 20, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0]

private def crossRows : Array ℕ :=
  #[2130433, 532621, 532625, 8688461, 266305, 532621, 532615, 532625, 532625, 532627, 65, 532631, 4161, 532611, 532609, 65, 532615, 532610, 532610, 532611, 65]

private def masks : Array ℕ :=
  #[272450, 4718610, 135556, 4582251977, 2155913216, 293995001, 271846505, 5452660736, 1080047814, 361209856, 338690084, 6511132982, 6444522753, 276798465, 4649360641, 5385952713, 294108617, 298816921, 7541359097, 1373634809, 5391850697, 6444289403, 6452446521, 7546312089, 1374393497, 4649320758, 7520230761, 7586462182, 7524162561, 4649323899, 4657743161, 7587077413, 7519346157, 1349524717, 2432205881, 369067065, 7536451049, 4582219259, 1350278277, 1440985220, 1373879501, 1374141641]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 0, 0, 0, 37]

private def mask (p : Fin 42) : ℕ := masks.getD p.val 0
private def keep (p : Fin 42) : Fin 38 := Fin.ofNat' 38 (kept.getD p.val 0)
private def cross (p k : Fin 42) : Choice 42 38 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (6 * negativeIndex.getD k.val 0)) &&& 63
  if x < 42 then .skip (Fin.ofNat' 42 x)
  else .edge (Fin.ofNat' 38 (x-42)) (((x-42) / 38+1 : ℕ) : ℤ)

private theorem valid : Valid stage18 stage19 9 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage18)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage19 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut19

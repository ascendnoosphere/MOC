import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 19 in cut 16. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut16

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 3, 4, 5, 6, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 8, 9, 10, 11, 12, 13, 14, 0, 15, 16, 17, 18, 19, 0, 0, 0, 20, 0, 0, 21, 22]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[34628178011, 8674215426, 4462741340, 176194717210, 8640467202, 8640660226, 8640463618, 8674149634, 83886850, 100667408, 17280799764, 8674087170, 8674149634, 83886594, 17280830230, 17280801306, 83886594, 83886850, 8674149122, 17280796423, 43050731015, 17280796180, 8674149122]

private def masks : Array ℕ :=
  #[272450, 4194322, 135300, 4581694665, 2155880448, 293994745, 271846505, 5452660736, 1080047814, 361177088, 338690084, 6510608438, 1349590017, 6443965441, 276241409, 4648803329, 5385750779, 5385952457, 294075593, 298259609, 7541358841, 5387589869, 5387918569, 1369712873, 1373634809, 5664671993, 5391850697, 4581625083, 6443764859, 6451889209, 7545754777, 1373836441, 4648796214, 7519673449, 7586461926, 7523605505, 4648732927, 4648799355, 4657185849, 7586520101, 7519345901, 1349524717, 1440817152, 1441858617, 1373649133, 1373715657, 2431648825, 368510009]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 0, 0, 0, 21, 0, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 0, 40, 41, 42]

private def mask (p : Fin 48) : ℕ := masks.getD p.val 0
private def keep (p : Fin 48) : Fin 46 := Fin.ofNat' 46 (kept.getD p.val 0)
private def cross (p k : Fin 48) : Choice 48 46 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 48 then .skip (Fin.ofNat' 48 x)
  else .edge (Fin.ofNat' 46 (x-48)) (((x-48) / 46+1 : ℕ) : ℤ)

private theorem valid : Valid stage15 stage16 19 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage15)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage16 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut16

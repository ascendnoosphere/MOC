import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 15 in cut 17. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut17

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 3, 4, 5, 6, 0, 0, 7, 8, 0, 0, 0, 0, 0, 9, 10, 11, 0, 12, 0, 13, 0, 0, 14, 15, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0]

private def crossRows : Array ℕ :=
  #[8606875921, 86033563648, 0, 4311810305, 8606843665, 4311810305, 8606843651, 0, 4311810305, 47261746452, 4311810305, 4311810305, 30081680152, 4311810305, 8607040773, 30081679879, 17297309696, 4311810305, 17314086912, 4311810305, 4311810305]

private def masks : Array ℕ :=
  #[272450, 4718610, 135300, 4582218953, 2155880448, 293994745, 271846505, 5452660736, 1080047814, 361177088, 338690084, 6511132726, 1350114305, 6444489729, 276765697, 4649327617, 5385750779, 5385952457, 294075593, 298783897, 7541358841, 1373634809, 5391850697, 4582149371, 6444289147, 6452413497, 7546279065, 1374360729, 4649320502, 7520197737, 7586461926, 7524129793, 4649257215, 4649323643, 4657710137, 7587044389, 7519345901, 1349524717, 1440817152, 1442382905, 1373715657, 2432173113, 369034297, 5391784191, 7603230975, 7536450793]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 16, 17, 18, 19, 20, 21, 0, 22, 23, 24, 25, 26, 27, 28, 29, 0, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 0, 0, 40]

private def mask (p : Fin 46) : ℕ := masks.getD p.val 0
private def keep (p : Fin 46) : Fin 42 := Fin.ofNat' 42 (kept.getD p.val 0)
private def cross (p k : Fin 46) : Choice 46 42 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 46 then .skip (Fin.ofNat' 46 x)
  else .edge (Fin.ofNat' 42 (x-46)) (((x-46) / 42+1 : ℕ) : ℤ)

private theorem valid : Valid stage16 stage17 15 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage16)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage17 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut17

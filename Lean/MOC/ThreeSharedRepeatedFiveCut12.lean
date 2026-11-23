import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 12 in cut 12. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut12

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 4, 5, 6, 7, 8, 0, 9, 10, 11, 0, 0, 12, 13, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 16, 0, 17, 18, 19]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[105579071364958, 6622940694032, 16777472, 8826292340737, 17622502739984, 17622519582209, 161658526174866, 12124877490951, 12124877556481, 3311470314243, 3311470314240, 17605322804737, 2246453168907, 3328717555463, 3328734201857, 8809112340481, 8809112340481, 7726763869959, 16778240, 8826292275201]

private def masks : Array ℕ :=
  #[270402, 4194322, 131204, 269944009, 2155880448, 283123712, 277217529, 271844457, 1140916224, 1080041670, 344399872, 338690084, 2215641142, 1349583873, 2148992001, 276235265, 337052673, 2150630437, 275776549, 1074004219, 1074201801, 277292233, 281478297, 3229614329, 2428633273, 1075839213, 1076167913, 1352933609, 279322857, 1356857593, 283246777, 1352925433, 1080100041, 269878523, 336855163, 2492465209, 347349097, 351273017, 347340921, 2148795515, 2156921913, 284165177, 348586169, 345440313, 3234006169, 1357055129, 337051702, 3224700009, 3291488486, 3228632065]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 0, 0, 0, 0, 0, 34, 35, 36, 37, 0, 38, 39, 40, 41, 42, 43]

private def mask (p : Fin 50) : ℕ := masks.getD p.val 0
private def keep (p : Fin 50) : Fin 49 := Fin.ofNat' 49 (kept.getD p.val 0)
private def cross (p k : Fin 50) : Choice 50 49 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 50 then .skip (Fin.ofNat' 50 x)
  else .edge (Fin.ofNat' 49 (x-50)) (((x-50) / 49+1 : ℕ) : ℤ)

private theorem valid : Valid stage11 stage12 12 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage11)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage12 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut12

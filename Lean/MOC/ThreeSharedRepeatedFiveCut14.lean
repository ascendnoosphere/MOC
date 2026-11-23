import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 24 in cut 14. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut14

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 4, 0, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 0, 0, 18, 19, 20, 0, 0, 0, 21, 22, 23]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[514, 514, 2902, 1284, 2827, 280, 514, 514, 514, 4376, 34180, 1816, 1284, 514, 6162, 1799, 3352, 258, 514, 514, 267, 258, 263, 2827]

private def masks : Array ℕ :=
  #[272450, 4194322, 135300, 269950153, 2155880448, 283123712, 277217529, 271846505, 1140916224, 1080047814, 344399872, 338690084, 2215641142, 1349590017, 2148998145, 276241409, 337058817, 2150636581, 275782693, 1074006267, 1074207945, 277298377, 281482393, 3229614329, 1075845357, 1076174057, 1352935657, 279324905, 1356857593, 1352927481, 1080106185, 269880571, 2148797563, 2156921913, 284165177, 3234010265, 1357059225, 337051702, 3224706153, 3291494630, 3228638209, 336988415, 337054843, 345441337]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0, 0, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]

private def mask (p : Fin 44) : ℕ := masks.getD p.val 0
private def keep (p : Fin 44) : Fin 45 := Fin.ofNat' 45 (kept.getD p.val 0)
private def cross (p k : Fin 44) : Choice 44 45 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 44 then .skip (Fin.ofNat' 44 x)
  else .edge (Fin.ofNat' 45 (x-44)) (((x-44) / 45+1 : ℕ) : ℤ)

private theorem valid : Valid stage13 stage14 24 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage13)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage14 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut14

import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 32 in cut 15. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut15

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 3, 0, 4, 5, 6, 0, 0, 7, 8, 9, 0, 0, 0, 10, 11, 12, 13, 14, 0, 15, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[395023, 5769815, 65537, 983812, 983818, 65536, 201491, 1704964, 1704537, 463384, 460312, 853338, 65536, 65536, 9110532, 2032644, 65537, 459524, 65540, 852740, 65536, 65536, 9176586, 721412, 2032132]

private def masks : Array ℕ :=
  #[272450, 4194322, 135300, 286727369, 2155880448, 283123712, 293994745, 271846505, 1157693440, 1080047814, 361177088, 338690084, 2215641142, 1349590017, 2148998145, 276241409, 353836033, 1090783483, 1090985161, 294075593, 298259609, 3246391545, 1092622573, 1092951273, 1369712873, 296102121, 1373634809, 1369704697, 1096883401, 286657787, 2148797563, 2156921913, 284165177, 3250787481, 1373836441, 353828918, 3224706153, 3291494630, 3228638209, 353765631, 353832059, 362218553, 3291552805, 3224378605, 1349524717]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 24, 25, 26, 27, 28, 29, 0, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]

private def mask (p : Fin 45) : ℕ := masks.getD p.val 0
private def keep (p : Fin 45) : Fin 48 := Fin.ofNat' 48 (kept.getD p.val 0)
private def cross (p k : Fin 45) : Choice 45 48 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 45 then .skip (Fin.ofNat' 45 x)
  else .edge (Fin.ofNat' 48 (x-45)) (((x-45) / 48+1 : ℕ) : ℤ)

private theorem valid : Valid stage14 stage15 32 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage14)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage15 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut15

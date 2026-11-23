import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 7 in cut 10. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut10

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 2, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 0, 0, 0, 0, 0, 0, 0, 0, 22, 0, 23, 24, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6]

private def crossRows : Array ℕ :=
  #[57626690111085, 26630691275669, 215608169907757, 0, 0, 35425173635080, 13298030395779, 13298030346624, 88653533561473, 35426784248328, 176579835609601, 35426784101384, 35425173635080, 31028737590151, 35426240824320, 26492169881088, 35426784002689, 211798835872385, 35426784101384, 31028737737224, 31028737491585, 13297493524483, 176614463783553, 35463578534401, 35463846969985]

private def masks : Array ℕ :=
  #[270402, 4194322, 131076, 1508425, 2155880448, 14688256, 8781945, 3409001, 1140916224, 3221233734, 1080041542, 68485170, 75964416, 70254628, 2215641142, 78979104, 3222340609, 1081148417, 2148860979, 2148992001, 7799809, 68617217, 2150630437, 7341093, 2148533303, 2150958113, 7668769, 70583329, 1074004091, 1074201673, 8856649, 13042713, 3229614201, 2160197689, 1075839085, 3221225599, 1076167785, 1084498025, 10887273, 1088422009, 14811193, 1084489849, 3221292105, 1080099913, 1442939, 68419707, 2224029753, 78913641, 82837561, 78905465, 2148795515, 2156921913, 15729721, 80150585, 77004857, 3234006041, 1088619545, 78970937]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 11, 12, 13, 0, 14, 15, 0, 16, 17, 18, 19, 20, 21, 0, 0, 0, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 0]

private def mask (p : Fin 58) : ℕ := masks.getD p.val 0
private def keep (p : Fin 58) : Fin 52 := Fin.ofNat' 52 (kept.getD p.val 0)
private def cross (p k : Fin 58) : Choice 58 52 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (7 * negativeIndex.getD k.val 0)) &&& 127
  if x < 58 then .skip (Fin.ofNat' 58 x)
  else .edge (Fin.ofNat' 52 (x-58)) (((x-58) / 52+1 : ℕ) : ℤ)

private theorem valid : Valid stage09 stage10 7 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage09)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage10 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut10

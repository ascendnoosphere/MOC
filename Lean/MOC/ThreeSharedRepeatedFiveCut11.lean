import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 28 in cut 11. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut11

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 4, 5, 0, 0, 6, 0, 7, 8, 0, 9, 0, 0, 0, 10, 11, 0, 12, 0, 0, 0, 13, 14, 15, 16, 17, 0, 0, 18, 19, 20, 21, 22, 23, 0, 0, 24, 25, 26, 0, 27, 28]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[60163231744, 17196712964, 98817934080, 60449579776, 17180132352, 34578696292, 60146423562, 12901748480, 12919310336, 60146388746, 17179869952, 98801094656, 111686003969, 17179870208, 17179869952, 111685996289, 111685996289, 112038708992, 12918588160, 34578696192, 34578696196, 17179870208, 34376583169, 30266558208, 60146388737, 25786648576, 12919310336, 158930636545, 8624343040]

private def masks : Array ℕ :=
  #[270402, 4194322, 131204, 1508553, 2155880448, 14688256, 8782073, 3409001, 1140916224, 3221233862, 1080041670, 75964416, 70254628, 2215641142, 3222340609, 1081148417, 2148992001, 7799809, 68617217, 2150630437, 7341093, 2148533303, 1074004219, 1074201801, 8856777, 13042841, 3229614329, 2160197817, 1075839213, 3221225727, 1076167913, 1084498153, 10887401, 1088422137, 14811321, 1084489977, 3221292233, 1080100041, 1443067, 68419707, 2224029753, 78913641, 82837561, 78905465, 2148795515, 2156921913, 15729721, 80150713, 77004857, 3234006169, 1088619673, 68616246]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 9, 10, 11, 12, 0, 13, 14, 15, 16, 17, 18, 0, 19, 20, 21, 22, 23, 24, 25, 0, 26, 27, 28, 29, 30, 31, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]

private def mask (p : Fin 52) : ℕ := masks.getD p.val 0
private def keep (p : Fin 52) : Fin 50 := Fin.ofNat' 50 (kept.getD p.val 0)
private def cross (p k : Fin 52) : Choice 52 50 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 52 then .skip (Fin.ofNat' 52 x)
  else .edge (Fin.ofNat' 50 (x-52)) (((x-52) / 50+1 : ℕ) : ℤ)

private theorem valid : Valid stage10 stage11 28 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage10)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage11 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut11

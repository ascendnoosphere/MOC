import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 11 in cut 13. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut13

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 2, 0, 3, 0, 0, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 0, 0, 13, 14, 15, 16, 0, 0, 17, 18, 19, 20, 0, 0, 0, 0, 0, 0, 21, 22, 23, 24, 0, 0, 25, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0]

private def crossRows : Array ℕ :=
  #[101716033, 34103686, 102261126, 262209, 34113822, 34145238, 34145678, 34169806, 34087042, 34087042, 102240321, 34103686, 34103620, 34087042, 34103686, 101732676, 101732676, 102261126, 34105175, 102240321, 102240321, 34091203, 524353, 34112333, 102240321, 102240321]

private def masks : Array ℕ :=
  #[270402, 4194322, 135300, 269948105, 2155880448, 283123712, 277217529, 271844457, 1140916224, 1080045766, 344399872, 338690084, 2215641142, 1349587969, 2148996097, 276239361, 337056769, 2150634533, 275780645, 1074004219, 1074205897, 277296329, 281482393, 3229614329, 2428633273, 1075843309, 1076172009, 1352933609, 279322857, 1356857593, 283246777, 1352925433, 1080104137, 269878523, 2148795515, 2156921913, 284165177, 348586169, 3234010265, 1357059225, 337051702, 3224704105, 3291492582, 3228636161, 336986367, 2492596413, 345440445, 337052795, 345441337]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 24, 25, 26, 27, 28, 0, 29, 30, 31, 32, 33, 34, 0, 35, 36, 37, 38, 39, 40, 41, 0, 0, 42, 43]

private def mask (p : Fin 49) : ℕ := masks.getD p.val 0
private def keep (p : Fin 49) : Fin 44 := Fin.ofNat' 44 (kept.getD p.val 0)
private def cross (p k : Fin 49) : Choice 49 44 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (6 * negativeIndex.getD k.val 0)) &&& 63
  if x < 49 then .skip (Fin.ofNat' 49 x)
  else .edge (Fin.ofNat' 44 (x-49)) (((x-49) / 44+1 : ℕ) : ℤ)

private theorem valid : Valid stage12 stage13 11 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage12)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage13 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut13

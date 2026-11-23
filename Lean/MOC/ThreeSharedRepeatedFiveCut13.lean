import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 11 in cut 13. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut13

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage12.count := ⟨by decide +kernel⟩
local instance : NeZero stage13.count := ⟨by decide +kernel⟩

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

private def positiveRows : Array (Fin 49) := #[0, 3, 7, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 25, 26, 27, 28, 31, 32, 33, 34, 41, 42, 43, 44, 47]
private def negativeRows : Array (Fin 49) := #[24, 30, 37, 45, 46]
private def positiveRay (i : Fin 26) : Fin 49 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 5) : Fin 49 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 49) : Fin 26 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 49) : Fin 5 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 49) (hp : 0 < stage12.ray p 11)
    (hk : stage12.ray k 11 < 0) :
    CrossOK stage12 stage13 11 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage12.ray p 11 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage12.ray k 11 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage12 stage13 11 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[557452395274440, 163853002871299, 128642894404100, 548656301736136, 547551988682818, 553324924246208, 164960008667849, 128522600841804, 0, 0, 434165434015880, 0, 16222199996940, 4398451263025, 0, 0, 505642279363848, 547429308023884, 513637764154569, 0, 561979291334792, 16020194896544, 9832812028450, 388097437074544, 0, 0, 550992764542208, 0, 547225967373544, 0, 16225020683008, 50903977709584, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [5, 22, 13, 26, 31, 30, 2], [0, 26, 22, 18, 2], [0, 26, 1, 31, 2], [10, 26, 21, 31, 1, 2], [7, 16, 31, 22, 26, 13], [0, 2, 13, 22], [0, 26, 23, 18, 4, 17], [0, 2, 22, 31, 30, 1], [0, 13, 4, 30, 17], [0, 13, 17, 22, 30, 21], [3, 2, 18, 31, 26, 23, 4], [3, 21, 26, 13, 22, 2], [3, 2, 13, 30, 26, 31, 4], [3, 21, 1, 31, 30, 2, 23], [3, 16, 13, 26, 22, 17], [3, 16, 13, 26, 31, 4, 17], [28, 12, 31, 26, 22, 13], [5, 22, 13, 20, 26, 2], [5, 22, 26, 31, 30, 2, 1, 20], [5, 30, 13, 20, 2, 1], [28, 12, 1, 26, 10, 13], [18, 21, 26, 30, 2, 10, 13, 1], [28, 31, 18, 22, 26, 17], [28, 31, 1, 2, 26, 22, 17], [10, 4, 2, 26, 22, 31, 1, 17], [10, 4, 30, 26, 22, 31, 2, 1], [18, 12, 31, 26, 10, 13, 1, 17], [18, 30, 20, 31, 2, 13, 1], [10, 17, 13, 26, 22, 31, 2, 1], [5, 17, 13, 20, 26, 4], [23, 12, 26, 22, 31, 30, 21, 13], [28, 30, 2, 23, 22, 13, 17], [28, 30, 1, 12, 13], [7, 18, 31, 26, 12, 13, 1], [10, 6, 2, 13, 31, 30, 21, 1], [5, 18, 21, 26, 2, 13, 1], [5, 18, 31, 2, 26, 13, 1, 20, 6], [0, 13, 22, 31, 30, 21, 7], [28, 7, 4, 13, 26, 22, 2, 17], [0, 28, 22, 18, 23, 4, 17, 16], [3, 2, 18, 23, 26, 4, 28], [10, 23, 30, 22, 31, 21, 13, 16, 12], [18, 21, 22, 30, 10, 13, 1, 12], [10, 6, 22, 31, 30, 21, 13, 1, 12], [7, 21, 31, 23, 22, 30, 2, 13, 12], [7, 21, 1, 31, 30, 13, 12]]
private def zeros (k : Fin 49) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 562949953421311 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage12 stage13 11 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage12)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage13 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut13

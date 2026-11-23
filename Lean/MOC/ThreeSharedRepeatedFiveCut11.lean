import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 28 in cut 11. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut11

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage10.count := ⟨by decide +kernel⟩
local instance : NeZero stage11.count := ⟨by decide +kernel⟩

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

private def positiveRows : Array (Fin 52) := #[3, 5, 6, 7, 11, 12, 15, 17, 18, 20, 24, 25, 27, 31, 32, 33, 34, 35, 38, 39, 40, 41, 42, 43, 46, 47, 48, 50, 51]
private def negativeRows : Array (Fin 52) := #[9, 14, 21, 29, 36]
private def positiveRay (i : Fin 29) : Fin 52 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 5) : Fin 52 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 52) : Fin 29 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 52) : Fin 5 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 52) (hp : 0 < stage10.ray p 28)
    (hk : stage10.ray k 28 < 0) :
    CrossOK stage10 stage11 28 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage10.ray p 28 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage10.ray k 28 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage10 stage11 28 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[2251799813669064, 2270217176622595, 2251800622675460, 2251799809491144, 4501186633801794, 2814543549444288, 29669462116041, 1830137100240460, 0, 0, 1812477335552136, 0, 0, 2205482487345, 0, 0, 4363069430417672, 4363158685157452, 2703466154100937, 0, 2673737405034632, 1211867168674976, 1904517517050914, 2233174939666544, 0, 0, 2691054709258496, 0, 0, 0, 1689103074641664, 616895483568656, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 2, 23, 26, 22], [0, 2, 13, 26], [0, 13, 26, 22], [5, 30, 23, 22, 26, 31, 2, 13], [0, 2, 26, 22, 18], [0, 2, 26, 1, 31], [20, 30, 22, 13, 2], [4, 16, 13, 2], [0, 2, 13, 22], [0, 26, 22, 18, 23, 17], [0, 26, 31, 18, 23, 4, 17], [0, 2, 22, 31, 30, 1], [0, 13, 4, 30, 17], [0, 13, 17, 22, 30, 21], [3, 2, 18, 22, 26, 23], [3, 2, 18, 31, 26, 23, 4], [3, 2, 22, 26, 13, 30], [3, 2, 13, 30, 26, 31, 4], [3, 2, 22, 31, 13, 30], [3, 16, 1, 22, 26, 23, 17], [3, 16, 1, 31, 26, 23, 17], [3, 16, 21, 13, 26, 22, 17], [23, 10, 2, 26, 22, 13], [5, 22, 31, 26, 13, 2, 20], [5, 30, 22, 20, 26, 31, 2, 1], [5, 30, 13, 20, 2, 1], [18, 22, 2, 10, 26, 13], [18, 30, 20, 21, 2, 13, 1], [4, 10, 13, 26, 17], [18, 22, 20, 23, 16, 21, 13, 17], [4, 20, 13, 2, 26, 22, 31, 17], [4, 10, 2, 26, 22, 31, 1, 17], [4, 10, 30, 26, 22, 31, 2, 1], [18, 31, 2, 10, 26, 13, 1, 17], [18, 31, 30, 20, 2, 13, 1], [20, 17, 13, 16, 1, 22, 31, 2], [5, 17, 22, 13, 26, 20], [5, 17, 13, 31, 26, 4, 20], [23, 30, 2, 16, 26, 22, 31, 21, 13], [7, 10, 23, 2, 22, 30, 13], [7, 18, 21, 10, 1, 30, 13], [4, 10, 7, 16, 22, 31, 2, 1], [7, 18, 31, 10, 30, 2, 13, 1], [7, 10, 13, 1, 16, 22, 31, 2], [7, 26, 21, 23, 16, 22, 2, 13], [7, 26, 21, 1, 16, 13], [7, 26, 31, 18, 30, 2, 13, 1], [6, 20, 31, 21, 30, 2, 10, 13, 1], [7, 10, 21, 1, 31, 30, 13], [5, 18, 21, 2, 26, 13, 1, 20, 6], [5, 18, 31, 2, 26, 13, 1, 20, 6], [0, 13, 22, 31, 30, 21, 7]]
private def zeros (k : Fin 52) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 4503599627370495 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage10 stage11 28 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage10)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage11 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut11

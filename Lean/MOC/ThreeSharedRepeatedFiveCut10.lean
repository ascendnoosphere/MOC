import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 7 in cut 10. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut10

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage09.count := ⟨by decide +kernel⟩
local instance : NeZero stage10.count := ⟨by decide +kernel⟩

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

private def positiveRows : Array (Fin 58) := #[2, 3, 6, 9, 10, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 53, 55, 56]
private def negativeRows : Array (Fin 58) := #[11, 15, 18, 25, 26, 27, 57]
private def positiveRay (i : Fin 25) : Fin 58 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 7) : Fin 58 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 58) : Fin 25 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 58) : Fin 7 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 58) (hp : 0 < stage09.ray p 7)
    (hk : stage09.ray k 7 < 0) :
    CrossOK stage09 stage10 7 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage09.ray p 7 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage09.ray k 7 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage09 stage10 7 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[288230376151646408, 1178711110209027, 51568993796, 288230375883276488, 288075944445626434, 180130787193317568, 1898845575317193, 0, 0, 0, 115998549476311176, 0, 0, 141150878996017, 0, 0, 279236443753126152, 135126967748399180, 173021834071808201, 0, 171119193922463880, 221674687008253088, 121889121090274338, 287038384214413424, 0, 0, 172227501511211264, 0, 0, 0, 108102596774004480, 39481310830215696, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 13, 26, 2], [0, 13, 26, 22], [5, 30, 23, 22, 26, 31, 2, 13], [0, 26, 1, 22, 2], [0, 26, 1, 31, 2], [20, 30, 22, 13, 2], [4, 16, 13, 2], [0, 13, 5, 22, 2], [0, 26, 22, 18, 23, 17], [0, 26, 31, 18, 23, 4, 17], [0, 13, 2, 22, 30], [0, 1, 21, 31, 30, 2], [0, 13, 4, 30, 17], [0, 13, 16, 22, 21, 17], [0, 1, 2, 22, 31, 30, 17], [5, 17, 22, 13, 26, 3], [5, 17, 13, 31, 26, 4, 3], [3, 21, 26, 2, 13, 22, 30, 17], [5, 30, 23, 22, 6, 26, 2], [5, 30, 23, 1, 26, 31, 2, 3], [5, 30, 23, 22, 6, 31, 2], [3, 16, 1, 22, 26, 23, 17], [3, 16, 1, 31, 26, 23, 17], [3, 16, 21, 13, 26, 22, 17], [3, 26, 22, 2, 13, 30, 4, 17], [3, 31, 26, 2, 13, 30, 4, 17], [3, 31, 22, 13, 2, 30, 4, 17], [20, 23, 2, 16, 22, 13], [5, 22, 31, 26, 13, 2, 20], [5, 30, 22, 20, 26, 31, 2, 1], [5, 30, 13, 20, 2, 1], [18, 22, 2, 10, 26, 13], [18, 30, 20, 21, 2, 13, 1], [18, 4, 10, 13, 26, 17], [18, 22, 20, 23, 16, 21, 13, 17], [20, 23, 1, 2, 26, 22, 31, 17], [20, 4, 16, 2, 22, 31, 1, 17], [20, 30, 22, 16, 31, 2, 4, 1], [18, 31, 2, 10, 26, 13, 1, 17], [18, 31, 30, 20, 2, 13, 1], [20, 17, 13, 16, 1, 22, 31, 2], [5, 17, 22, 13, 26, 20], [5, 17, 13, 31, 26, 4, 20], [21, 31, 16, 26, 22, 30, 2, 23, 13], [21, 31, 17, 30, 22, 13, 16], [18, 22, 2, 30, 10, 13], [4, 10, 30, 17, 22, 31, 2, 1, 16], [18, 31, 30, 2, 10, 13, 1, 17], [10, 30, 17, 13, 1, 22, 31, 2, 16], [21, 16, 23, 2, 26, 22, 30, 13, 17], [18, 22, 2, 30, 26, 13], [18, 31, 30, 2, 26, 13, 1, 17], [20, 6, 31, 21, 30, 2, 10, 13, 1], [21, 31, 6, 22, 30, 2, 10, 13, 1], [5, 18, 21, 2, 26, 13, 1, 20, 6], [5, 18, 31, 2, 26, 13, 1, 20, 6], [10, 6, 22, 31, 17, 30, 2, 13, 1]]
private def zeros (k : Fin 58) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 288230376151711743 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage09 stage10 7 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage09)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage10 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut10

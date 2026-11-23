import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 32 in cut 15. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut15

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage14.count := ⟨by decide +kernel⟩
local instance : NeZero stage15.count := ⟨by decide +kernel⟩

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

private def positiveRows : Array (Fin 45) := #[3, 8, 12, 14, 16, 17, 18, 21, 22, 23, 27, 28, 29, 30, 31, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43]
private def negativeRows : Array (Fin 45) := #[5, 25, 32]
private def positiveRay (i : Fin 25) : Fin 45 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 3) : Fin 45 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 45) : Fin 25 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 45) : Fin 3 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 45) (hp : 0 < stage14.ray p 32)
    (hk : stage14.ray k 32 < 0) :
    CrossOK stage14 stage15 32 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage14.ray p 32 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage14.ray k 32 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage14 stage15 32 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[35012573389000, 1822676881923, 31507884284420, 30339648848072, 3916677910594, 34883453982912, 28245851243209, 27102317249100, 0, 0, 34462559494280, 32918706578057, 31293414695436, 137489810993, 0, 0, 8100587103496, 3908992615500, 3953175545033, 0, 35158065543304, 31289369471648, 17897465356834, 2231490839664, 3909493917000, 0, 8418135973120, 0, 21497101528296, 0, 31293633340160, 13686989148176, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [5, 22, 13, 26, 31, 30, 2], [0, 26, 22, 18, 2], [0, 26, 1, 31, 2], [11, 22, 26, 31, 2], [24, 12, 4, 13, 26], [0, 2, 13, 22], [0, 26, 23, 18, 4, 17], [0, 2, 22, 31, 30, 1], [0, 13, 4, 30, 17], [0, 13, 17, 22, 30, 21], [3, 26, 13, 17, 31, 4], [3, 26, 22, 13, 2], [3, 26, 13, 31, 30, 2, 4], [3, 21, 1, 31, 30, 2, 23], [10, 28, 2, 31, 26, 22, 13], [5, 22, 13, 20, 26, 2], [5, 22, 26, 31, 30, 2, 1, 20], [11, 5, 30, 13, 2, 1], [11, 28, 26, 22, 2, 10, 13], [10, 28, 1, 31, 26, 17], [28, 31, 1, 2, 26, 22, 17], [10, 4, 2, 26, 22, 31, 1, 17], [10, 30, 26, 22, 31, 2, 4, 1], [11, 17, 31, 26, 10, 13, 1], [10, 2, 13, 22, 26, 31, 1, 17], [5, 17, 13, 20, 26, 4], [21, 16, 31, 2, 22, 30, 23, 13], [24, 21, 2, 23, 22, 13, 17], [11, 28, 30, 2, 22, 13], [11, 24, 31, 2, 13, 1], [11, 28, 5, 26, 2, 13, 1], [11, 5, 13, 26, 18, 31, 2, 1], [0, 13, 22, 31, 30, 21, 7], [24, 22, 2, 23, 1, 17, 28], [0, 28, 22, 18, 23, 4, 17, 16], [3, 26, 13, 17, 4, 28], [10, 30, 23, 22, 31, 21, 13, 16, 12], [7, 21, 31, 23, 22, 30, 2, 13, 12], [11, 22, 31, 2, 30, 13, 6], [3, 28, 1, 17, 22, 23, 24], [24, 22, 18, 26, 23, 17], [24, 31, 18, 23, 1, 26, 17, 16]]
private def zeros (k : Fin 45) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 35184372088831 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage14 stage15 32 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage14)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage15 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut15

import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 24 in cut 14. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut14

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage13.count := ⟨by decide +kernel⟩
local instance : NeZero stage14.count := ⟨by decide +kernel⟩

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

private def positiveRows : Array (Fin 44) := #[3, 6, 8, 10, 16, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 35, 36, 37, 41, 42, 43]
private def negativeRows : Array (Fin 44) := #[17, 18]
private def positiveRay (i : Fin 24) : Fin 44 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 2) : Fin 44 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 44) : Fin 24 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 44) : Fin 2 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 44) (hp : 0 < stage13.ray p 24)
    (hk : stage13.ray k 24 < 0) :
    CrossOK stage13 stage14 24 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage13.ray p 24 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage13.ray k 24 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage13 stage14 24 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[16904991269064, 7290707513859, 2886235200004, 15805479125192, 15666711629890, 16388513994944, 7430288704201, 2856152728140, 0, 0, 14704935690376, 8529524023945, 2028356493836, 549959239217, 0, 0, 14810161997064, 15635970114636, 15812701832393, 0, 17486959868040, 2012175837856, 1221117387298, 8925963355248, 0, 0, 16080357629184, 0, 15619661868264, 0, 2029231022848, 1971398529040, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [5, 22, 13, 26, 31, 30, 2], [0, 26, 22, 18, 2], [0, 26, 1, 31, 2], [11, 22, 26, 31, 2], [7, 16, 31, 22, 26, 13], [0, 2, 13, 22], [0, 26, 23, 18, 4, 17], [0, 2, 22, 31, 30, 1], [0, 13, 4, 30, 17], [0, 13, 17, 22, 30, 21], [3, 2, 18, 31, 26, 23, 4], [3, 21, 26, 13, 22, 2], [3, 2, 13, 30, 26, 31, 4], [3, 21, 1, 31, 30, 2, 23], [3, 16, 13, 26, 22, 17], [3, 16, 13, 26, 31, 4, 17], [10, 28, 2, 31, 26, 22, 13], [5, 22, 13, 20, 26, 2], [5, 22, 26, 31, 30, 2, 1, 20], [11, 5, 30, 13, 2, 1], [11, 28, 26, 22, 2, 10, 13], [18, 22, 31, 26, 17], [28, 31, 1, 2, 26, 22, 17], [10, 4, 2, 26, 22, 31, 1, 17], [10, 30, 26, 22, 31, 2, 4, 1], [11, 17, 31, 26, 10, 13, 1], [10, 2, 13, 22, 26, 31, 1, 17], [5, 17, 13, 20, 26, 4], [21, 16, 31, 2, 22, 30, 23, 13], [28, 30, 2, 23, 22, 13, 17], [11, 28, 30, 2, 22, 13], [11, 17, 31, 26, 30, 13, 1], [11, 28, 5, 26, 2, 13, 1], [11, 5, 13, 26, 18, 31, 2, 1], [0, 13, 22, 31, 30, 21, 7], [28, 7, 4, 13, 26, 22, 2, 17], [0, 28, 22, 18, 23, 4, 17, 16], [3, 2, 18, 23, 26, 4, 28], [10, 30, 23, 22, 31, 21, 13, 16, 12], [7, 21, 31, 23, 22, 30, 2, 13, 12], [11, 22, 31, 2, 30, 13, 6]]
private def zeros (k : Fin 44) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 17592186044415 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage13 stage14 24 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage13)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage14 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut14

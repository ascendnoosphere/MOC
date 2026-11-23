import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 3 in cut 6. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut06

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage05.count := ⟨by decide +kernel⟩
local instance : NeZero stage06.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 1, 2, 0, 0, 3, 4, 0, 0, 5, 6, 7, 8, 9, 10, 11, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[1154899551896056240, 1152922604219466162, 1152929201297536179, 360293467831993605, 360577146143750070, 360293467831993605, 432633662144841400, 1154899551895927481, 288512976510714299, 6485191160095922520, 1152929201289235210, 504692334219607815, 1152929201289236493]

private def masks : Array ℕ :=
  #[270338, 4194322, 1073741825, 131076, 262195, 394241, 2147484673, 6292481, 8790017, 12714001, 2155880448, 14688256, 8781873, 2155872305, 2097189, 2147483703, 2360353, 10756129, 14680113, 10747953, 1140850688, 3221233670, 1080041478, 67371058, 67503104, 2214593536, 2147492870, 73401344, 6300678, 75898880, 79822864, 75890736, 2222981168, 69206052, 2149589030, 6299686, 2214592566, 2147491894, 69469216, 77864992, 81788976, 77856816]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 0, 0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 0, 0, 0, 0, 0, 22, 23, 24, 25, 26, 27, 28, 29, 30, 0, 31, 32, 33]

private def mask (p : Fin 42) : ℕ := masks.getD p.val 0
private def keep (p : Fin 42) : Fin 50 := Fin.ofNat' 50 (kept.getD p.val 0)
private def cross (p k : Fin 42) : Choice 42 50 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 42 then .skip (Fin.ofNat' 42 x)
  else .edge (Fin.ofNat' 50 (x-42)) (((x-42) / 50+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 42) := #[2, 4, 5, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19]
private def negativeRows : Array (Fin 42) := #[6, 7, 24, 25, 26, 27, 28, 38]
private def positiveRay (i : Fin 13) : Fin 42 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 8) : Fin 42 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 42) : Fin 13 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 42) : Fin 8 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 42) (hp : 0 < stage05.ray p 3)
    (hk : stage05.ray k 3 < 0) :
    CrossOK stage05 stage06 3 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage05.ray p 3 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage05.ray k 3 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage05 stage06 3 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[1045492, 258048294931, 266629857288, 0, 3512218726930, 4395908460560, 0, 0, 0, 0, 275398066400, 0, 0, 739613216001, 0, 0, 0, 3774878504, 3026367222065, 0, 0, 4183705995392, 1135352220290, 3856344694528, 0, 0, 4208725065728, 0, 0, 0, 7340036, 227736069184, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[5, 22, 31, 17, 30], [5, 13, 10, 17, 30], [5, 13, 10, 22, 26, 2], [5, 13, 10, 22, 30], [21, 31, 17, 26, 22, 30, 13], [5, 13, 26, 22, 31, 30, 2], [5, 13, 26, 22, 17, 30], [5, 13, 26, 17, 31, 30, 4], [5, 22, 31, 26, 30, 2, 10, 1], [5, 13, 10, 26, 30, 2, 1], [5, 22, 18, 30, 10, 2], [5, 10, 17, 30, 1, 31], [21, 31, 26, 1, 22, 30, 2, 10, 13], [21, 26, 1, 17, 30, 10, 13], [23, 1, 10, 26, 30, 17], [21, 26, 13, 17, 18, 22, 30, 23, 10], [23, 1, 26, 2, 22, 31, 30, 17], [4, 10, 2, 26, 22, 31, 30, 1, 17], [26, 13, 18, 31, 2, 30, 10, 1, 17], [26, 13, 22, 31, 17, 30, 2, 10, 1], [5, 13, 10, 22, 2, 0], [5, 22, 18, 10, 26, 23, 17, 0], [5, 10, 23, 26, 18, 31, 4, 17, 0], [21, 31, 17, 30, 22, 13, 0], [5, 13, 22, 0, 31, 30, 2], [5, 13, 22, 17, 30, 0], [5, 22, 18, 30, 26, 23, 17, 0], [5, 13, 17, 0, 31, 30, 4], [5, 17, 31, 30, 26, 18, 23, 4, 0], [5, 22, 31, 0, 30, 2, 10, 1], [5, 13, 10, 30, 2, 1, 0], [21, 31, 0, 1, 22, 30, 2, 10, 13], [21, 18, 2, 0, 22, 30, 10, 13], [23, 1, 10, 30, 17, 0], [23, 10, 4, 30, 26, 18, 22, 17, 0], [23, 10, 4, 30, 26, 18, 31, 17, 0], [21, 18, 23, 30, 10, 22, 13, 17, 0], [21, 26, 0, 18, 22, 30, 23, 10, 17], [23, 1, 0, 2, 22, 31, 30, 17], [4, 10, 2, 0, 22, 31, 30, 1, 17], [18, 2, 0, 31, 30, 10, 13, 1, 17], [0, 13, 22, 31, 17, 30, 2, 10, 1]]
private def zeros (k : Fin 42) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 4398046511103 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage05 stage06 3 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage05)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage06 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut06

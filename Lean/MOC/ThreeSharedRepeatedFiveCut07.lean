import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 20 in cut 7. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut07

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage06.count := ⟨by decide +kernel⟩
local instance : NeZero stage07.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 9, 0, 0, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[65763, 15132132, 15206631, 197609, 65770, 329065, 454124, 15665134, 658160, 65540, 657930, 722955, 197388, 65548, 65548, 65549, 65549, 397071, 1050384, 657937, 131760, 131761, 65540, 328965, 328965, 328965, 11666695, 11732231, 722187, 197388, 197388, 65549, 328974, 328974, 328974, 1049872]

private def masks : Array ℕ :=
  #[270338, 4194322, 1073741833, 131076, 262203, 394249, 8790025, 12714009, 2155880448, 14688256, 8781881, 2155872313, 2097197, 2147483711, 2360361, 10756137, 14680121, 10747961, 1140850688, 3221233670, 1080041478, 67371058, 75898880, 79822864, 75890736, 2222981168, 69206052, 2149589030, 6299686, 2214592566, 2147491894, 77864992, 81788976, 77856816, 3221226497, 1080034305, 2147746867, 2147877889, 6685697, 67503105, 2160198673, 14812177, 2155873329, 2149581861, 6292517, 2147484727, 2149844001, 6554657, 69469217, 14681137]

private def kept : Array ℕ :=
  #[0, 1, 0, 2, 3, 4, 0, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]

private def mask (p : Fin 50) : ℕ := masks.getD p.val 0
private def keep (p : Fin 50) : Fin 65 := Fin.ofNat' 65 (kept.getD p.val 0)
private def cross (p k : Fin 50) : Choice 50 65 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 50 then .skip (Fin.ofNat' 50 x)
  else .edge (Fin.ofNat' 65 (x-50)) (((x-50) / 65+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 50) := #[4, 5, 11, 12, 13, 14, 15, 16, 17, 21, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]
private def negativeRows : Array (Fin 50) := #[2, 6, 7]
private def positiveRay (i : Fin 36) : Fin 50 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 3) : Fin 50 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 50) : Fin 36 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 50) : Fin 3 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 50) (hp : 0 < stage06.ray p 20)
    (hk : stage06.ray k 20 < 0) :
    CrossOK stage06 stage07 20 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage06.ray p 20 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage06.ray k 20 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage06 stage07 20 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[1125882727234804, 35255108509715, 61574733115400, 261364, 605914182921362, 1121587745258512, 0, 0, 0, 0, 1125882726989856, 0, 0, 3629679425, 0, 0, 0, 4260636919016, 493622762062961, 0, 0, 1084443206078976, 724891973255810, 570661630349248, 0, 0, 282040434163712, 0, 0, 0, 51541442564, 120071884646656, 0]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[5, 17, 30, 22, 31], [5, 17, 30, 13], [5, 17, 13, 22, 26, 31], [5, 0, 13, 26, 22], [21, 31, 17, 26, 22, 30, 13], [5, 22, 13, 30, 26, 31, 2], [5, 22, 31, 26, 30, 2, 10, 1], [5, 10, 13, 26, 30, 2, 1], [5, 17, 30, 22, 18], [5, 17, 30, 1, 31], [21, 31, 26, 1, 22, 30, 2, 10, 13], [21, 18, 2, 22, 30, 26, 10, 13], [4, 18, 30, 13, 10, 26, 17], [21, 18, 23, 30, 26, 22, 10, 13, 17], [4, 13, 2, 30, 17, 26, 22, 31], [4, 10, 2, 26, 22, 31, 30, 1, 17], [18, 31, 2, 26, 10, 30, 13, 1, 17], [10, 13, 26, 22, 2, 31, 30, 1, 17], [5, 17, 13, 0, 22], [5, 17, 22, 0, 26, 18, 23], [5, 17, 31, 0, 26, 18, 23, 4], [0, 13, 23, 2, 22, 30], [5, 0, 22, 31, 30, 2, 1], [5, 0, 13, 30, 2, 1], [0, 13, 22, 2, 31, 30, 21, 1], [0, 13, 18, 22, 2, 30], [0, 13, 4, 30, 17], [0, 26, 22, 18, 30, 23, 4, 17], [0, 26, 31, 18, 30, 23, 4, 17], [0, 13, 23, 18, 22, 30, 21, 17], [0, 26, 22, 18, 30, 23, 21, 17], [0, 4, 2, 22, 31, 30, 1, 17], [0, 13, 18, 2, 31, 30, 1, 17], [0, 13, 22, 2, 31, 30, 1, 17], [5, 17, 13, 22, 26, 3], [5, 17, 13, 26, 31, 4, 3], [21, 23, 2, 26, 3, 22, 30, 13, 17], [5, 22, 13, 30, 26, 2, 3], [5, 23, 30, 1, 26, 31, 2, 3], [5, 22, 13, 30, 31, 2, 3], [5, 18, 30, 21, 26, 2, 13, 1, 3], [5, 18, 30, 31, 26, 2, 13, 1, 3], [21, 18, 2, 22, 30, 26, 13, 3], [4, 18, 30, 13, 26, 22, 17, 3], [4, 18, 30, 13, 26, 31, 17, 3], [21, 18, 23, 30, 26, 22, 13, 17, 3], [4, 13, 2, 30, 17, 26, 22, 3], [4, 13, 2, 30, 17, 26, 31, 3], [4, 13, 2, 30, 17, 22, 31, 3], [18, 31, 2, 26, 3, 30, 13, 1, 17]]
private def zeros (k : Fin 50) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 1125899906842623 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage06 stage07 20 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage06)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage07 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut07

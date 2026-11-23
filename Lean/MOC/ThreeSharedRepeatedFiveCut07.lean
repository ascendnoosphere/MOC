import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 20 in cut 7. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut07

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

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

private theorem valid : Valid stage06 stage07 20 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage06)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage07 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut07

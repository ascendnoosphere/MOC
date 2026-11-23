import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 3 in cut 6. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut06

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

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

private theorem valid : Valid stage05 stage06 3 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage05)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage06 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut06

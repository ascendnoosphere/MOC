import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 0 in cut 5. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut05

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 0, 7, 8, 0, 0, 9, 10, 11, 12, 13, 14]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[8487039, 65922, 65923, 558468, 8849286, 65928, 131721, 65846, 134027, 9342348, 168079, 65853, 65938, 131731, 65940]

private def masks : Array ℕ :=
  #[67108864, 270338, 4194322, 1073741824, 131076, 262194, 394240, 2147484672, 6292480, 8790016, 12714000, 2155880448, 14688256, 8781872, 2155872304, 2147491846, 6299654, 2097188, 2147483702, 2360352, 10756128, 14680112, 10747952]

private def kept : Array ℕ :=
  #[0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 14, 15, 16, 17, 18, 19]

private def mask (p : Fin 23) : ℕ := masks.getD p.val 0
private def keep (p : Fin 23) : Fin 42 := Fin.ofNat' 42 (kept.getD p.val 0)
private def cross (p k : Fin 23) : Choice 23 42 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 23 then .skip (Fin.ofNat' 23 x)
  else .edge (Fin.ofNat' 42 (x-23)) (((x-23) / 42+1 : ℕ) : ℤ)

private theorem valid : Valid stage04 stage05 0 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage04)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage05 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut05

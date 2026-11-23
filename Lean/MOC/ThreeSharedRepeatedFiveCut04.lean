import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 17 in cut 4. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut04

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 3, 0, 0, 4, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[623125282, 148766977, 22348033, 39191042, 136904961]

private def masks : Array ℕ :=
  #[67108864, 270338, 4194322, 2147491842, 1073741824, 4, 6299650, 2097184, 262194, 263168, 2147483698, 2147484672, 6292480, 8658944, 12582928, 2155880448, 14688256, 8650800, 2155872304]

private def kept : Array ℕ :=
  #[0, 1, 2, 0, 3, 4, 0, 0, 5, 6, 0, 7, 8, 9, 10, 11, 12, 13, 14]

private def mask (p : Fin 19) : ℕ := masks.getD p.val 0
private def keep (p : Fin 19) : Fin 23 := Fin.ofNat' 23 (kept.getD p.val 0)
private def cross (p k : Fin 19) : Choice 19 23 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 19 then .skip (Fin.ofNat' 19 x)
  else .edge (Fin.ofNat' 23 (x-19)) (((x-19) / 23+1 : ℕ) : ℤ)

private theorem valid : Valid stage03 stage04 17 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage03)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage04 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut04

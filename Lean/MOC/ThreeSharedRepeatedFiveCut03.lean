import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 1 in cut 3. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut03

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 1, 2, 0, 0, 0, 3, 0, 4, 0, 5, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[27, 28, 181, 182, 183, 70]

private def masks : Array ℕ :=
  #[67108864, 270336, 4194320, 2147491840, 1073741824, 4, 8388608, 6299648, 2097184, 262192, 263168, 2147483696, 2147484672, 6292480]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 0, 6, 7, 8, 9, 10, 11, 12]

private def mask (p : Fin 14) : ℕ := masks.getD p.val 0
private def keep (p : Fin 14) : Fin 19 := Fin.ofNat' 19 (kept.getD p.val 0)
private def cross (p k : Fin 14) : Choice 14 19 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 14 then .skip (Fin.ofNat' 14 x)
  else .edge (Fin.ofNat' 19 (x-14)) (((x-14) / 19+1 : ℕ) : ℤ)

private theorem valid : Valid stage02 stage03 1 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage02)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage03 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut03

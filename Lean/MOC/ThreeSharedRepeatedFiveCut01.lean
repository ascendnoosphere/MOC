import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 4 in cut 1. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut01

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 1, 0, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[19, 42]

private def masks : Array ℕ :=
  #[67108864, 262144, 4194304, 2147483648, 32, 1073741824, 4, 8388608, 2097152, 1024]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 0, 8]

private def mask (p : Fin 10) : ℕ := masks.getD p.val 0
private def keep (p : Fin 10) : Fin 11 := Fin.ofNat' 11 (kept.getD p.val 0)
private def cross (p k : Fin 10) : Choice 10 11 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (6 * negativeIndex.getD k.val 0)) &&& 63
  if x < 10 then .skip (Fin.ofNat' 10 x)
  else .edge (Fin.ofNat' 11 (x-10)) (((x-10) / 11+1 : ℕ) : ℤ)

private theorem valid : Valid stage00 stage01 4 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage00)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage01 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut01

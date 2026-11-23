import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 13 in cut 1. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut01

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 2, 0, 0, 0, 0, 3]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0]

private def crossRows : Array ℕ :=
  #[2103554, 535044, 2111750, 2115848]

private def masks : Array ℕ :=
  #[8589934592, 4398046511104, 70368744177664, 2048, 274877906944, 4294967296, 137438953472, 262144, 2, 512]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 0, 0, 6, 7]

private def mask (p : Fin 10) : ℕ := masks.getD p.val 0
private def keep (p : Fin 10) : Fin 16 := Fin.ofNat' 16 (kept.getD p.val 0)
private def cross (p k : Fin 10) : Choice 10 16 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (11 * negativeIndex.getD k.val 0)) &&& 2047
  if x < 10 then .skip (Fin.ofNat' 10 x)
  else .edge (Fin.ofNat' 16 (x-10)) (((x-10) / 16+1 : ℕ) : ℤ)

private theorem valid : Valid stage00 stage01 13 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage00)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage01 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut01

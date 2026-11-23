import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 13 in cut 2. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut02

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]

private def crossRows : Array ℕ :=
  #[1364, 3314, 3330]

private def masks : Array ℕ :=
  #[67108864, 262144, 4194320, 2147483648, 48, 1073741824, 4, 8388608, 1024, 6291456, 2097184]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 0, 4, 5, 6, 0, 7, 8]

private def mask (p : Fin 11) : ℕ := masks.getD p.val 0
private def keep (p : Fin 11) : Fin 14 := Fin.ofNat' 14 (kept.getD p.val 0)
private def cross (p k : Fin 11) : Choice 11 14 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (6 * negativeIndex.getD k.val 0)) &&& 63
  if x < 11 then .skip (Fin.ofNat' 11 x)
  else .edge (Fin.ofNat' 14 (x-11)) (((x-11) / 14+1 : ℕ) : ℤ)

private theorem valid : Valid stage01 stage02 13 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage01)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage02 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut02

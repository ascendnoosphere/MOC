import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 47 in cut 2. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut02

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 5]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[603436, 605486, 4100, 4100, 7175, 7175]

private def masks : Array ℕ :=
  #[8589942784, 4398046511104, 70368744177664, 10240, 274877915136, 4294967296, 2, 8704, 146028888064, 8590196736, 137438955520, 264192, 412316860416, 274878169088, 137438953984, 262656]

private def kept : Array ℕ :=
  #[0, 0, 1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

private def mask (p : Fin 16) : ℕ := masks.getD p.val 0
private def keep (p : Fin 16) : Fin 18 := Fin.ofNat' 18 (kept.getD p.val 0)
private def cross (p k : Fin 16) : Choice 16 18 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (10 * negativeIndex.getD k.val 0)) &&& 1023
  if x < 16 then .skip (Fin.ofNat' 16 x)
  else .edge (Fin.ofNat' 18 (x-16)) (((x-16) / 18+1 : ℕ) : ℤ)

private theorem valid : Valid stage01 stage02 47 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage01)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage02 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut02

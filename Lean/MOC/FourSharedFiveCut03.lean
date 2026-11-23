import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 6 in cut 3. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut03

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 1, 0, 2, 3, 4, 0, 0, 0, 5, 0, 6, 0, 7, 0, 8, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[229599, 11489, 896442, 13540, 7397, 8422, 8423, 7400, 7401]

private def masks : Array ℕ :=
  #[4398046511104, 70368744177664, 141012366270464, 4294967296, 2, 140737488364032, 146028888064, 8590196736, 137438955520, 264192, 141149805215744, 141012366524416, 140874927309312, 140737488617984, 283467849728, 274877917184, 8589943296, 10752]

private def kept : Array ℕ :=
  #[0, 0, 1, 2, 3, 4, 5, 6, 7, 0, 8, 9, 10, 11, 12, 13, 14, 15]

private def mask (p : Fin 18) : ℕ := masks.getD p.val 0
private def keep (p : Fin 18) : Fin 27 := Fin.ofNat' 27 (kept.getD p.val 0)
private def cross (p k : Fin 18) : Choice 18 27 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (10 * negativeIndex.getD k.val 0)) &&& 1023
  if x < 18 then .skip (Fin.ofNat' 18 x)
  else .edge (Fin.ofNat' 27 (x-18)) (((x-18) / 27+1 : ℕ) : ℤ)

private theorem valid : Valid stage02 stage03 6 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage02)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage03 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut03

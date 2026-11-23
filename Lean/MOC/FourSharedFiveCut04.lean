import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 0 in cut 4. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut04

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 1, 0, 0, 2, 3, 0, 4, 5, 0, 6, 0, 7, 8, 9, 10, 11, 12, 13, 0, 0, 14, 15, 16, 17, 18, 19]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 0, 0, 1, 4, 5, 8, 10, 12, 14]

private def masks : Array ℕ :=
  #[70368744177728, 141012366270528, 4294967296, 66, 140737488364096, 146028888128, 8590196736, 137438955520, 141149805215808, 141012366524416, 140874927309376, 140737488617984, 283467849792, 274877917184, 8589943360, 10752, 74766790688768, 70368744441856, 145410412781568, 4398046511106, 264194, 145135534875136, 4544075399168, 145547851726848, 145272973820416, 4681514360832, 4406636454400]

private def kept : Array ℕ :=
  #[0, 1, 2, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

private def mask (p : Fin 27) : ℕ := masks.getD p.val 0
private def keep (p : Fin 27) : Fin 37 := Fin.ofNat' 37 (kept.getD p.val 0)
private def cross (p k : Fin 27) : Choice 27 37 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (9 * negativeIndex.getD k.val 0)) &&& 511
  if x < 27 then .skip (Fin.ofNat' 27 x)
  else .edge (Fin.ofNat' 37 (x-27)) (((x-27) / 37+1 : ℕ) : ℤ)

private theorem valid : Valid stage03 stage04 0 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage03)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage04 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut04

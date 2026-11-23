import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 50 in cut 5. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut05

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 2, 0, 3, 4, 0, 5, 0, 6, 7, 8, 9, 0, 0, 10, 0, 0, 11, 12, 13, 14, 15, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 1, 3, 4, 7, 9, 11, 13]

private def masks : Array ℕ :=
  #[70368744177729, 141012366270529, 4294967296, 140737488364097, 146028888129, 8590196736, 137438955521, 141149805215809, 141012366524416, 140874927309377, 140737488617984, 283467849793, 274877917185, 8589943361, 10753, 74766790688769, 70368744441857, 145410412781569, 4398046511106, 264194, 145135534875137, 4544075399169, 145547851726849, 145272973820417, 4681514360833, 4406636454401, 70368744177730, 141012366270530, 140737488364098, 146028888130, 137438955586, 141149805215810, 140874927309378, 283467849794, 274877917250, 8589943362, 10818]

private def kept : Array ℕ :=
  #[0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]

private def mask (p : Fin 37) : ℕ := masks.getD p.val 0
private def keep (p : Fin 37) : Fin 45 := Fin.ofNat' 45 (kept.getD p.val 0)
private def cross (p k : Fin 37) : Choice 37 45 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (9 * negativeIndex.getD k.val 0)) &&& 511
  if x < 37 then .skip (Fin.ofNat' 37 x)
  else .edge (Fin.ofNat' 45 (x-37)) (((x-37) / 45+1 : ℕ) : ℤ)

private theorem valid : Valid stage04 stage05 50 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage04)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage05 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut05

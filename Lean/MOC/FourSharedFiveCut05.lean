import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 50 in cut 5. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut05

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage04.count := ⟨by decide +kernel⟩
local instance : NeZero stage05.count := ⟨by decide +kernel⟩

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

private def positiveRows : Array (Fin 37) := #[1, 3, 4, 6, 7, 9, 11, 12, 13, 14, 17, 20, 21, 22, 23, 24, 25]
private def negativeRows : Array (Fin 37) := #[0, 26]
private def positiveRay (i : Fin 17) : Fin 37 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 2) : Fin 37 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 37) : Fin 17 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 37) : Fin 2 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 37) (hp : 0 < stage04.ray p 50)
    (hk : stage04.ray k 50 < 0) :
    CrossOK stage04 stage05 50 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage04.ray p 50 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage04.ray k 50 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage04 stage05 50 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[66321115, 137372631040, 0, 0, 0, 0, 137371855515, 0, 0, 107685635592, 0, 86973698112, 0, 129303214090, 0, 0, 0, 0, 591136, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 43538982960, 0, 0, 0, 8067744464, 28072614274, 0, 0, 0, 66486272, 0, 0, 0, 67207169, 6858868618, 0, 0, 0]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[13, 37, 18, 42, 32, 1], [1, 42, 9, 33, 11, 46, 32, 37, 18], [0, 1, 18], [1, 42, 38, 33, 11, 46, 32, 37, 18], [13, 47, 1, 46, 42, 11, 32, 18], [0, 1, 47, 32], [6, 42, 18, 13, 32], [13, 1, 42, 18, 33, 46, 11, 32, 9], [0, 1, 33, 32, 9], [13, 1, 42, 18, 33, 46, 11, 38, 32], [0, 1, 33, 38, 32], [47, 1, 42, 11, 46, 32, 37, 18, 9], [6, 42, 18, 32, 37, 9], [47, 1, 42, 11, 46, 38, 32, 37, 18], [6, 42, 18, 38, 32, 37], [6, 13, 18, 37, 32, 1], [6, 42, 38, 9, 33, 32, 37, 1], [6, 11, 33, 9, 46, 32, 37, 18, 1], [0, 6, 18, 32], [0, 6, 47, 33, 42, 32], [6, 11, 33, 38, 46, 32, 37, 18, 1], [6, 13, 18, 47, 46, 11, 32, 1], [6, 13, 18, 33, 46, 11, 32, 1, 9], [6, 13, 18, 33, 46, 11, 38, 32, 1], [6, 47, 11, 46, 32, 37, 18, 1, 9], [6, 47, 11, 46, 38, 32, 37, 18, 1], [0, 13, 37, 18, 42, 32], [0, 9, 33, 11, 42, 46, 32, 37, 18], [0, 38, 33, 11, 42, 46, 32, 37, 18], [0, 13, 18, 47, 42, 46, 11, 32], [0, 13, 18, 47, 33, 42, 46, 32], [0, 13, 18, 33, 42, 46, 11, 32, 9], [0, 13, 18, 33, 42, 46, 11, 38, 32], [0, 47, 11, 42, 46, 32, 37, 18, 9], [0, 47, 33, 42, 46, 32, 37, 18, 9], [0, 47, 11, 42, 46, 38, 32, 37, 18], [0, 47, 33, 42, 46, 38, 32, 37, 18]]
private def zeros (k : Fin 37) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 137438953471 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage04 stage05 50 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage04)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage05 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut05

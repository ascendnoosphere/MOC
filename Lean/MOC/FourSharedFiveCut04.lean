import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 0 in cut 4. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut04

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage03.count := ⟨by decide +kernel⟩
local instance : NeZero stage04.count := ⟨by decide +kernel⟩

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

private def positiveRows : Array (Fin 27) := #[0, 1, 4, 5, 7, 8, 10, 12, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 25, 26]
private def negativeRows : Array (Fin 27) := #[3]
private def positiveRay (i : Fin 20) : Fin 27 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 1) : Fin 27 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 27) : Fin 20 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 27) : Fin 1 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 27) (hp : 0 < stage03.ray p 0)
    (hk : stage03.ray k 0 < 0) :
    CrossOK stage03 stage04 0 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage03.ray p 0 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage03.ray k 0 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage03 stage04 0 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[0, 1572872, 0, 0, 0, 0, 21819, 0, 0, 86035472, 0, 1220736, 0, 103084050, 0, 0, 0, 0, 1182272, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 104878176, 0, 0, 0, 29361568, 42218242, 0, 0, 0, 132972544, 0, 0, 0, 196609, 27528978, 0, 0, 0]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[13, 37, 18, 42, 32, 1], [42, 11, 33, 9, 46, 32, 37, 18, 1], [13, 37, 18, 42, 6], [13, 37, 18, 42, 46, 32], [42, 11, 33, 38, 46, 32, 37, 18, 1], [13, 47, 42, 11, 46, 32, 18, 1], [13, 37, 46, 1, 47, 32], [13, 47, 33, 46, 1, 32], [13, 42, 18, 33, 46, 11, 32, 1, 9], [13, 37, 46, 1, 33, 32, 9], [13, 42, 18, 33, 46, 11, 38, 32, 1], [13, 37, 46, 1, 33, 38, 32], [47, 42, 11, 46, 32, 37, 18, 1, 9], [47, 33, 46, 1, 32, 37, 9], [47, 42, 11, 46, 38, 32, 37, 18, 1], [47, 33, 46, 1, 38, 32, 37], [13, 37, 18, 1, 32, 6], [13, 37, 1, 47, 33, 42, 32, 6], [6, 11, 33, 9, 46, 32, 37, 18, 1], [13, 37, 18, 46, 32, 6], [13, 37, 46, 47, 33, 42, 32, 6], [6, 11, 33, 38, 46, 32, 37, 18, 1], [13, 47, 46, 1, 11, 32, 18, 6], [13, 18, 6, 33, 46, 11, 32, 1, 9], [13, 18, 6, 33, 46, 11, 38, 32, 1], [47, 11, 6, 46, 32, 37, 18, 1, 9], [47, 11, 6, 46, 38, 32, 37, 18, 1]]
private def zeros (k : Fin 27) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 134217727 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage03 stage04 0 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage03)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage04 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut04

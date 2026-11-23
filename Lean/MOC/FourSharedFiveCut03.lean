import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 6 in cut 3. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut03

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage02.count := ⟨by decide +kernel⟩
local instance : NeZero stage03.count := ⟨by decide +kernel⟩

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

private def positiveRows : Array (Fin 18) := #[1, 2, 4, 5, 6, 10, 12, 14, 16]
private def negativeRows : Array (Fin 18) := #[0, 9]
private def positiveRay (i : Fin 9) : Fin 18 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 2) : Fin 18 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 18) : Fin 9 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 18) : Fin 2 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 18) (hp : 0 < stage02.ray p 6)
    (hk : stage02.ray k 6 < 0) :
    CrossOK stage02 stage03 6 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage02.ray p 6 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage02.ray k 6 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage02 stage03 6 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[0, 16, 0, 0, 0, 0, 0, 0, 0, 208928, 0, 164608, 0, 245796, 0, 0, 0, 0, 10880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 82112, 0, 0, 0, 5440, 52228, 0, 0, 0, 1, 0, 0, 0, 2, 15396, 0, 0, 0]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[13, 37, 18, 46, 32, 1], [13, 37, 18, 42, 32, 1], [9, 33, 11, 42, 46, 32, 37, 18, 1], [13, 37, 18, 42, 46, 1], [13, 37, 18, 42, 46, 32], [38, 33, 11, 42, 46, 32, 37, 18, 1], [13, 18, 47, 42, 46, 11, 32, 1], [13, 37, 47, 42, 46, 11, 32, 1], [13, 18, 47, 33, 42, 46, 32, 1], [13, 37, 47, 33, 42, 46, 32, 1], [13, 18, 33, 42, 46, 11, 32, 1, 9], [13, 37, 33, 42, 46, 11, 32, 1, 9], [13, 18, 33, 42, 46, 11, 38, 32, 1], [13, 37, 33, 42, 46, 11, 38, 32, 1], [47, 11, 42, 46, 32, 37, 18, 1, 9], [47, 33, 42, 46, 32, 37, 18, 1, 9], [47, 11, 42, 46, 38, 32, 37, 18, 1], [47, 33, 42, 46, 38, 32, 37, 18, 1]]
private def zeros (k : Fin 18) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 262143 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage02 stage03 6 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage02)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage03 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut03

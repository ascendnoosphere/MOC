import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 35 in cut 9. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut09

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage08.count := ⟨by decide +kernel⟩
local instance : NeZero stage09.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4, 5, 0, 0, 6, 7, 8, 9, 0, 10, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 4]

private def crossRows : Array ℕ :=
  #[275415569411, 825844830729, 137842136067, 894564303881, 1513847266831, 139318538256, 1170114616847, 139318557200, 1238968311311, 139318538256, 19243539891215]

private def masks : Array ℕ :=
  #[4294967296, 8590196736, 1126037345802241, 141012400078848, 140737488617984, 1126174885423105, 1125899973962241, 74766891352065, 70368845109249, 4398046511106, 268290, 1130443982241793, 1271447792123905, 1271172880663041, 141012399824962, 283467849794, 274877921346, 211381211111489, 211106299650625, 70514773069889, 70506283800641, 211518582952001, 211243671491137, 70652312690753, 70643722762305, 70377401229889, 70368844855873, 1267049745621057, 1126320813645889, 70506183137347, 141012366271042, 70368811301443, 1267049712067137]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 14, 0, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 25, 26, 0, 27, 0]

private def mask (p : Fin 33) : ℕ := masks.getD p.val 0
private def keep (p : Fin 33) : Fin 31 := Fin.ofNat' 31 (kept.getD p.val 0)
private def cross (p k : Fin 33) : Choice 33 31 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (9 * negativeIndex.getD k.val 0)) &&& 511
  if x < 33 then .skip (Fin.ofNat' 33 x)
  else .edge (Fin.ofNat' 31 (x-33)) (((x-33) / 31+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 33) := #[1, 7, 8, 11, 19, 20, 23, 24, 25, 26, 28]
private def negativeRows : Array (Fin 33) := #[14, 16, 27, 30, 32]
private def positiveRay (i : Fin 11) : Fin 33 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 5) : Fin 33 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 33) : Fin 11 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 33) : Fin 5 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 33) (hp : 0 < stage08.ray p 35)
    (hk : stage08.ray k 35 < 0) :
    CrossOK stage08 stage09 35 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage08.ray p 35 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage08.ray k 35 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage08 stage09 35 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[7516076516, 3758212608, 0, 0, 0, 0, 8589918208, 0, 0, 7621320784, 0, 2769356132, 2776171780, 8045183072, 0, 0, 0, 0, 1306, 0, 0, 0, 0, 0, 0, 229790120, 2274755040, 0, 0, 0, 0, 0, 1, 310937602, 0, 0, 0, 5242370052, 5798875176, 0, 0, 0, 14976, 0, 0, 0, 2818441600, 5509640216, 0, 0, 4697634916]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[0, 1, 18], [0, 1, 47, 32], [6, 42, 18, 13, 32], [0, 1, 33, 32, 9], [0, 1, 33, 38, 32], [6, 42, 18, 32, 37, 9], [6, 42, 18, 38, 32, 37], [6, 50, 18, 32, 1], [6, 50, 42, 47, 33, 32, 1], [0, 38, 18, 32], [0, 38, 33, 42, 32, 9], [6, 11, 47, 46, 32, 18, 1], [6, 11, 18, 33, 46, 32, 1, 9], [6, 11, 18, 25, 33, 32, 1], [0, 18, 33, 42, 11, 32, 9], [0, 18, 47, 42, 11, 32], [0, 18, 47, 33, 42, 32], [37, 11, 33, 1, 18, 42, 32, 9], [38, 12, 42, 33, 11, 32, 18], [13, 47, 11, 42, 32, 18], [13, 47, 33, 1, 42, 32, 18, 50], [13, 42, 11, 18, 33, 32, 9], [13, 25, 33, 11, 42, 32, 18], [37, 11, 47, 42, 32, 18, 1, 9], [37, 1, 9, 18, 33, 42, 32, 47, 50], [38, 12, 42, 18, 11, 32, 47], [38, 37, 18, 42, 33, 32, 1, 47, 50], [46, 1, 9, 33, 11, 42, 32, 18], [46, 47, 11, 42, 32, 18, 1], [13, 47, 33, 26, 42, 32, 18, 50], [0, 18, 33, 42, 11, 32, 25], [38, 37, 18, 42, 33, 32, 47, 50, 25], [46, 1, 25, 33, 11, 42, 32, 18]]
private def zeros (k : Fin 33) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 8589934591 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage08 stage09 35 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage08)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage09 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut09

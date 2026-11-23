import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 25 in cut 8. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut08

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage07.count := ⟨by decide +kernel⟩
local instance : NeZero stage08.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 1, 0, 2, 3, 0, 0, 0, 4, 0, 5, 0, 0, 0, 0, 0, 6, 0, 0, 7, 8, 0, 9, 10, 0, 11, 12, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0]

private def crossRows : Array ℕ :=
  #[69257396740, 413123742726, 757661438473, 68990534148, 757659603465, 1032809356964, 1445931260942, 137715000851, 1515187608590, 1926833905678, 137711853582, 137724700179, 2188017933326]

private def masks : Array ℕ :=
  #[4294967296, 8590196736, 1126037345802241, 141012366524416, 140737488617984, 1126174851868673, 1125899973962241, 74766857797633, 70368811554817, 4398046511106, 268290, 1130443982241793, 1271447758569473, 1271172880663041, 141012366270530, 140737488364098, 283467849794, 274877921346, 8589943362, 14914, 211381177557057, 211106299650625, 70514773069889, 70506250246209, 211518549397569, 211243671491137, 70652279136321, 70643689207873, 70377401229889, 70368811301441, 1267049712066625, 1266774834160193, 1126320813645889, 1126045935739457, 70506183137347]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 0, 15, 16, 0, 0, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 0, 28, 0, 29]

private def mask (p : Fin 35) : ℕ := masks.getD p.val 0
private def keep (p : Fin 35) : Fin 33 := Fin.ofNat' 33 (kept.getD p.val 0)
private def cross (p k : Fin 35) : Choice 35 33 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (9 * negativeIndex.getD k.val 0)) &&& 511
  if x < 35 then .skip (Fin.ofNat' 35 x)
  else .edge (Fin.ofNat' 33 (x-35)) (((x-35) / 33+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 35) := #[3, 5, 7, 8, 12, 14, 20, 23, 24, 26, 27, 29, 30]
private def negativeRows : Array (Fin 35) := #[15, 18, 19, 31, 33]
private def positiveRay (i : Fin 13) : Fin 35 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 5) : Fin 35 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 35) : Fin 13 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 35) : Fin 5 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 35) (hp : 0 < stage07.ray p 25)
    (hk : stage07.ray k 25 < 0) :
    CrossOK stage07 stage08 25 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage07.ray p 25 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage07.ray k 25 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage07 stage08 25 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[34358704612, 17180902912, 0, 0, 0, 0, 34359721984, 0, 0, 11579203664, 0, 17860003172, 17914529028, 17116938336, 0, 0, 0, 0, 1306, 0, 0, 0, 0, 0, 0, 0, 1018167776, 0, 0, 0, 0, 0, 1, 13224970242, 0, 0, 0, 33348925444, 5588078632, 0, 0, 0, 14976, 0, 0, 0, 18252562816, 3274764312, 0, 0, 16106141796]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[0, 1, 18], [0, 1, 47, 32], [6, 42, 18, 13, 32], [0, 1, 33, 32, 9], [0, 1, 33, 38, 32], [6, 42, 18, 32, 37, 9], [6, 42, 18, 38, 32, 37], [6, 50, 18, 32, 1], [6, 50, 42, 47, 33, 32, 1], [0, 13, 18, 32], [0, 13, 47, 33, 42, 32], [6, 11, 47, 46, 32, 18, 1], [6, 11, 18, 33, 46, 32, 1, 9], [6, 11, 18, 33, 46, 38, 32, 1], [0, 18, 9, 33, 42, 11, 32], [0, 38, 18, 33, 42, 11, 32], [0, 18, 9, 42, 11, 32, 47], [0, 18, 9, 33, 42, 32, 47], [0, 38, 18, 42, 11, 32, 47], [0, 38, 18, 33, 42, 32, 47], [37, 11, 33, 1, 18, 42, 32, 9], [37, 11, 33, 38, 42, 32, 18, 1], [13, 47, 11, 42, 32, 18], [13, 47, 33, 1, 42, 32, 18, 50], [13, 42, 11, 18, 33, 32, 9], [13, 42, 11, 18, 33, 38, 32], [37, 11, 47, 1, 42, 32, 18, 9], [37, 1, 9, 18, 33, 42, 32, 47, 50], [37, 11, 47, 1, 42, 38, 32, 18], [37, 38, 1, 18, 33, 42, 32, 47, 50], [46, 1, 9, 33, 11, 42, 32, 18], [46, 38, 1, 33, 11, 42, 32, 18], [46, 1, 47, 11, 42, 32, 18, 9], [46, 38, 1, 47, 11, 42, 32, 18], [13, 47, 33, 26, 42, 32, 18, 50]]
private def zeros (k : Fin 35) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 34359738367 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage07 stage08 25 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage07)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage08 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut08

import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 19 in cut 10. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut10

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage09.count := ⟨by decide +kernel⟩
local instance : NeZero stage10.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 4, 0, 0, 5, 0, 0, 0, 0, 0, 0, 6, 0, 7, 0, 0, 0, 0, 8]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 4, 0, 5, 0, 0]

private def crossRows : Array ℕ :=
  #[8839177111555, 3341535086595, 5506232091141, 2207647531527, 2207647531532, 16578826409198, 15466530541840, 2207647859221, 2207648055824]

private def masks : Array ℕ :=
  #[4294967296, 42949935104, 1126037345802241, 141012400078848, 140737488617984, 1126174885423105, 1125899973962241, 74801251090433, 70403204847617, 4398046511106, 268290, 1130478341980161, 1271447792123905, 1271172880663041, 283467849794, 211381211111489, 211106299650625, 70549132808257, 70540643539009, 211518582952001, 211243671491137, 70686672429121, 70678082500673, 70411760968257, 70403204594241, 1126355173384257, 70506183137347, 70368811301443, 70643722762307, 1267058335555649, 1267058302001729]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 0, 15, 16, 0, 0, 17, 18, 0, 19, 20, 21, 0, 22, 0, 23, 24]

private def mask (p : Fin 31) : ℕ := masks.getD p.val 0
private def keep (p : Fin 31) : Fin 26 := Fin.ofNat' 26 (kept.getD p.val 0)
private def cross (p k : Fin 31) : Choice 31 26 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 31 then .skip (Fin.ofNat' 31 x)
  else .edge (Fin.ofNat' 26 (x-31)) (((x-31) / 26+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 31) := #[1, 4, 6, 11, 13, 16, 23, 25, 30]
private def negativeRows : Array (Fin 31) := #[15, 18, 19, 22, 26, 28]
private def positiveRay (i : Fin 9) : Fin 31 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 6) : Fin 31 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 31) : Fin 9 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 31) : Fin 6 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 31) (hp : 0 < stage09.ray p 19)
    (hk : stage09.ray k 19 < 0) :
    CrossOK stage09 stage10 19 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage09.ray p 19 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage09.ray k 19 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage09 stage10 19 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[2147465700, 469779968, 0, 0, 0, 0, 2147467264, 0, 0, 1234247760, 0, 490997092, 492700932, 2078392416, 0, 0, 0, 0, 1306, 0, 0, 0, 0, 0, 0, 829198760, 434471392, 0, 0, 0, 0, 0, 1, 1654802434, 0, 65407362, 0, 1713256452, 1919471656, 0, 0, 0, 14976, 0, 0, 0, 503284096, 1612296216, 0, 0, 1644181604]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[0, 18, 1], [0, 1, 47, 32], [6, 42, 18, 13, 32], [0, 1, 33, 32, 9], [0, 1, 33, 38, 32], [6, 42, 18, 32, 37, 9], [6, 42, 18, 38, 32, 37], [6, 50, 18, 32, 1], [6, 50, 42, 47, 33, 32, 1], [0, 18, 33, 32], [0, 33, 47, 42, 32], [6, 11, 47, 46, 32, 18, 1], [6, 11, 18, 35, 32, 1, 9], [6, 11, 18, 25, 33, 32, 1], [0, 18, 42, 32], [37, 11, 33, 42, 18, 32, 9], [25, 37, 1, 33, 11, 32, 18], [13, 47, 11, 42, 32, 18], [13, 47, 33, 1, 42, 32, 18, 50], [13, 35, 42, 11, 18, 32, 9], [13, 25, 33, 11, 42, 32, 18], [37, 11, 47, 42, 32, 18, 1, 9], [37, 9, 18, 1, 33, 42, 32, 47, 50], [25, 37, 1, 18, 11, 32, 47], [38, 37, 18, 42, 33, 32, 1, 47, 50], [46, 47, 11, 42, 32, 18, 1], [13, 47, 35, 42, 32, 18, 50], [25, 37, 33, 18, 42, 32, 47, 50], [37, 35, 9, 18, 33, 42, 32, 47, 50], [46, 42, 11, 18, 32, 1, 9, 35], [46, 42, 11, 18, 32, 1, 25, 35]]
private def zeros (k : Fin 31) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 2147483647 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage09 stage10 19 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage09)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage10 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut10

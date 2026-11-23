import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 12 in cut 7. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut07

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage06.count := ⟨by decide +kernel⟩
local instance : NeZero stage07.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 5, 6, 7, 8, 0, 9, 0, 10, 0, 0, 0, 0, 11]

private def negativeIndex : Array ℕ :=
  #[0, 0, 1, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 4, 0, 0, 5, 0, 0, 0, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[44541095215752, 13406825099653, 13406825099653, 31267363782664, 40065605075586, 40065611997767, 17869212500228, 28, 8798241032002, 31267363782664, 40065605075586, 17869212500228]

private def masks : Array ℕ :=
  #[1266912340222017, 4294967296, 1266637462315585, 8590196736, 1126037345798145, 141012366524416, 140737488617984, 1126183441801281, 1126174851868673, 1125908563894849, 1125899973962241, 74766857797633, 70368811550721, 1271310386733057, 4398046511106, 264194, 1271035508826625, 1130443982241793, 1271447758569473, 1271172880663041, 1130581488312321, 1130306610405889, 141012366270530, 140737488364098, 283467849794, 274877917250, 8589943362, 10818, 211381177557057, 211106299650625, 70514773065793, 70506250242113, 211518549393473, 211243671487041, 70652279136321, 70643689203777, 70377401229889, 70368811297345, 1267049712066625, 1266774834160193, 1126320813645889, 1126045935739457, 70506183133251]

private def kept : Array ℕ :=
  #[0, 0, 0, 1, 2, 3, 4, 0, 5, 0, 6, 7, 8, 0, 9, 10, 0, 11, 12, 13, 0, 0, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]

private def mask (p : Fin 43) : ℕ := masks.getD p.val 0
private def keep (p : Fin 43) : Fin 35 := Fin.ofNat' 35 (kept.getD p.val 0)
private def cross (p k : Fin 43) : Choice 43 35 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (6 * negativeIndex.getD k.val 0)) &&& 63
  if x < 43 then .skip (Fin.ofNat' 43 x)
  else .edge (Fin.ofNat' 35 (x-43)) (((x-43) / 35+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 43) := #[4, 12, 15, 25, 27, 30, 31, 32, 33, 35, 37, 42]
private def negativeRows : Array (Fin 43) := #[0, 2, 7, 9, 13, 16, 20, 21]
private def positiveRay (i : Fin 12) : Fin 43 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 8) : Fin 43 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 43) : Fin 12 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 43) : Fin 8 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 43) (hp : 0 < stage06.ray p 12)
    (hk : stage06.ray k 12 < 0) :
    CrossOK stage06 stage07 12 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage06.ray p 12 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage06.ray k 12 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage06 stage07 12 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[8795828731797, 4398310801408, 0, 0, 0, 0, 8796088828549, 0, 0, 2964276708932, 0, 4572160496912, 0, 4381939410821, 0, 0, 0, 0, 36968, 0, 0, 0, 0, 0, 0, 0, 260654055301, 0, 0, 0, 0, 0, 2, 3385595134600, 0, 0, 0, 8537322160144, 1430548390305, 0, 0, 0, 4155392, 0, 0, 0, 4672655988736, 838337372261, 0, 0, 4123172743061]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[9, 46, 33, 11, 42, 32, 37, 18, 1], [0, 1, 18], [38, 46, 33, 11, 42, 32, 37, 18, 1], [0, 1, 47, 32], [13, 46, 42, 18, 32], [0, 1, 33, 32, 9], [0, 1, 33, 38, 32], [9, 46, 47, 11, 42, 32, 37, 18, 1], [6, 42, 18, 32, 37, 9], [38, 46, 47, 11, 42, 32, 37, 18, 1], [6, 42, 18, 38, 32, 37], [13, 37, 18, 32, 1], [13, 37, 42, 47, 33, 32, 1], [6, 11, 33, 9, 46, 32, 37, 18, 1], [0, 13, 18, 32], [0, 13, 47, 33, 42, 32], [6, 11, 33, 38, 46, 32, 37, 18, 1], [13, 46, 18, 47, 11, 32, 1], [13, 46, 18, 33, 11, 32, 1, 9], [13, 46, 18, 33, 11, 38, 32, 1], [6, 47, 11, 46, 32, 37, 18, 1, 9], [6, 47, 11, 46, 38, 32, 37, 18, 1], [0, 18, 9, 33, 42, 11, 32], [0, 38, 18, 33, 42, 11, 32], [0, 18, 9, 42, 11, 32, 47], [0, 18, 9, 33, 42, 32, 47], [0, 38, 18, 42, 11, 32, 47], [0, 38, 18, 33, 42, 32, 47], [50, 1, 9, 33, 11, 42, 32, 37, 18], [50, 1, 38, 33, 11, 42, 32, 37, 18], [13, 47, 11, 42, 32, 18], [13, 47, 33, 1, 42, 32, 18, 50], [13, 42, 11, 18, 33, 32, 9], [13, 42, 11, 18, 33, 38, 32], [50, 1, 47, 11, 42, 32, 37, 18, 9], [50, 1, 47, 33, 42, 32, 37, 18, 9], [50, 1, 47, 11, 42, 38, 32, 37, 18], [50, 1, 47, 33, 42, 38, 32, 37, 18], [26, 1, 33, 9, 42, 46, 11, 32, 18], [26, 1, 33, 38, 42, 46, 11, 32, 18], [26, 47, 1, 42, 46, 11, 32, 18, 9], [26, 47, 1, 42, 46, 11, 38, 32, 18], [13, 47, 33, 26, 42, 32, 18, 50]]
private def zeros (k : Fin 43) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 8796093022207 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage06 stage07 12 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage06)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage07 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut07

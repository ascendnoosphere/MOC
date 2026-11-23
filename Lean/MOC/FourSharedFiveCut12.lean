import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 39 in cut 12. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut12

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage11.count := ⟨by decide +kernel⟩
local instance : NeZero stage12.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 4, 5, 6, 7, 8, 9, 0, 10, 11, 12, 0, 0, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[554260, 556310, 558360, 5402, 5403, 1308, 2333, 564510, 566560, 568610, 8199, 2057, 570660, 8199, 302638, 3081, 3082, 303110, 304134, 3075, 3075, 3075, 306738, 3075, 3075, 2055, 308788, 8199, 3082, 310838, 8199]

private def masks : Array ℕ :=
  #[4294967424, 1126037345802369, 140737489142272, 1126174885423105, 1125899974486657, 74801251090433, 70403204847617, 4398046511106, 268290, 1130478342504449, 1271447792123905, 1271172881187457, 211106300175041, 70549132808257, 211243671491265, 70411761492545, 70403204594369, 70368811301571, 1267058302526017, 211381211112001, 47245426688, 141016695046144, 287762817090, 70690967396417, 1126359468875841, 1267062630522945, 1126080296261633, 1267049745881089, 1126320813652035, 1126355173914689, 1267058335561793, 1125942924421633, 1126183442328131, 1126355241019969, 211389768016451, 211518583214657, 211527139340867, 1337427079737921, 70686672435777, 70652279142979]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 0, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]

private def mask (p : Fin 40) : ℕ := masks.getD p.val 0
private def keep (p : Fin 40) : Fin 66 := Fin.ofNat' 66 (kept.getD p.val 0)
private def cross (p k : Fin 40) : Choice 40 66 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (10 * negativeIndex.getD k.val 0)) &&& 1023
  if x < 40 then .skip (Fin.ofNat' 40 x)
  else .edge (Fin.ofNat' 66 (x-40)) (((x-40) / 66+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 40) := #[1, 3, 4, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]
private def negativeRows : Array (Fin 40) := #[5, 6]
private def positiveRay (i : Fin 31) : Fin 40 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 2) : Fin 40 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 40) : Fin 31 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 40) : Fin 2 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 40) (hp : 0 < stage11.ray p 39)
    (hk : stage11.ray k 39 < 0) :
    CrossOK stage11 stage12 39 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage11.ray p 39 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage11.ray k 39 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage11 stage12 39 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[1099504287354, 640222888320, 0, 0, 0, 0, 1097159667712, 219155, 0, 1097365182484, 0, 841746678106, 1067232485698, 1064947388440, 0, 0, 0, 0, 36711694660, 32834361876, 0, 0, 0, 0, 0, 447929189480, 856855122040, 0, 0, 0, 0, 0, 66060289, 1065014829568, 0, 286245626464, 0, 251239099906, 1097295725576, 0, 0, 0, 3744, 0, 0, 0, 1082340929632, 258942458884, 0, 0, 154602311194]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[0, 18, 1], [13, 18, 42, 46, 32], [0, 32, 1], [6, 18, 42, 7], [6, 18, 42, 38, 32, 37], [13, 37, 18, 32, 1], [13, 37, 32, 42, 1, 9], [0, 32, 18], [0, 32, 42, 9], [13, 18, 7, 46, 38, 1], [13, 18, 7, 35, 1], [13, 18, 46, 33, 11, 38, 32, 1], [33, 25, 11, 42, 32, 37, 18], [13, 18, 42, 7], [13, 18, 42, 33, 11, 32], [38, 11, 42, 47, 32, 37], [33, 47, 1, 50, 42, 32, 18], [33, 47, 25, 50, 42, 32, 18], [11, 46, 32, 42, 18], [33, 11, 42, 18, 7], [0, 1, 47, 7], [0, 1, 19, 7], [0, 18, 42, 7], [9, 37, 18, 42, 11, 1, 7], [9, 11, 25, 42, 46, 18, 1, 7], [9, 11, 35, 42, 18, 1, 7], [13, 47, 42, 46, 32, 1, 7], [13, 35, 9, 42, 32, 1, 7], [9, 25, 35, 32, 42, 18, 7], [9, 25, 32, 1, 42, 46, 18, 7], [9, 35, 32, 1, 42, 18, 26, 7], [6, 37, 25, 32, 1, 47, 7], [37, 46, 18, 32, 42, 25, 7], [12, 47, 32, 42, 46, 18, 1, 25, 7], [37, 11, 32, 42, 18, 25, 35, 7], [13, 50, 35, 32, 1, 19, 7], [50, 26, 18, 32, 42, 35, 7], [11, 19, 32, 42, 18, 1, 26, 35, 7], [37, 19, 1, 32, 42, 18, 47, 50, 7], [37, 25, 19, 32, 42, 18, 7]]
private def zeros (k : Fin 40) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 1099511627775 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage11 stage12 39 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage11)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage12 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut12

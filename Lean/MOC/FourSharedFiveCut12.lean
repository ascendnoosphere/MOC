import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 39 in cut 12. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut12

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

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

private theorem valid : Valid stage11 stage12 39 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage11)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage12 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut12

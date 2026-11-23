import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 7 in cut 11. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut11

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 5, 0, 0, 6, 0, 7, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 4, 0, 5, 0, 0]

private def crossRows : Array ℕ :=
  #[3207974602493606, 11844970742331996, 199218459838561, 422969321195524, 845733176543236, 12069341312371204, 70520146497544, 70508089709578]

private def masks : Array ℕ :=
  #[4294967296, 42950459392, 1126037345802241, 141012400078848, 140737489142272, 1126174885423105, 1125899974486529, 74801251090433, 70403204847617, 4398046511106, 268290, 1130478342504449, 1271447792123905, 1271172881187329, 283467849794, 211106300174913, 70549132808257, 211243671491137, 70686672429121, 70411761492545, 70403204594241, 1126355173908545, 70368811301443, 1267058335555649, 1267058302526017, 211381211112001]

private def kept : Array ℕ :=
  #[0, 0, 1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 12, 13, 14, 0, 15, 16, 0, 17, 0, 18, 19]

private def mask (p : Fin 26) : ℕ := masks.getD p.val 0
private def keep (p : Fin 26) : Fin 40 := Fin.ofNat' 40 (kept.getD p.val 0)
private def cross (p k : Fin 26) : Choice 26 40 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (9 * negativeIndex.getD k.val 0)) &&& 511
  if x < 26 then .skip (Fin.ofNat' 26 x)
  else .edge (Fin.ofNat' 40 (x-26)) (((x-26) / 40+1 : ℕ) : ℤ)

private theorem valid : Valid stage10 stage11 7 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage10)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage11 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut11
